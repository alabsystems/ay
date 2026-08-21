# In-tree git hooks

AY deliberately has no hosted GitHub Actions workflow. These opt-in hooks
provide early local soundness feedback; they supplement, rather than replace,
the checked-in `ay gate solver` and `publish/publish.sh check ay --check`
commands that maintainers run before staging a release.

## `pre-push` — zero-skip and SMT soundness gates

When installed, the hook first rejects active `pytest`/`unittest` skips and
expected failures in tracked first-party Python, then runs
`scripts/ci/smt_soundness_gate.sh`. The soundness gate adds two complementary
checks over the committed Tier-0 corpus:

1. **Hermetic declared-status regression check** — each `.smt2` is run through
   `libay_ffi` only and AY's verdict is compared to the file's declared
   `(set-info :status …)` expected label. A contradiction fails the regression
   check, but the label is evidence to adjudicate, not independent truth.
   **No z3 dependency**, so it works fully offline.
2. **2-solver differential vs libz3** — the classic `ay-z3-parity diff`; any
   `sat`-vs-`unsat` disagreement fails. Skipped automatically when libz3 is
   absent.

`unknown`/timeout is always tolerated (incompleteness is never a wrong answer).
The existing Git-LFS `pre-push` behavior is preserved (chained first).

## `pre-push` — MILP node ratchet (step 4)

Then it rebuilds `ay-milp`'s `mps_solve` example and runs
`scripts/milp_node_gate.py --check --tier all`: nineteen MIPLIB instances, EXACT
node counts, objectives and statuses, pinned in `.milp_node_baseline.toml`.
Models come from `~/ay-bench/milp-gate/instances`, which
`scripts/milp_gate_corpus.py --build` reconstructs from the sha256s and upstream
URLs in `.milp_gate_corpus.tsv`.

**Cost:** 46.9 s wall for the whole `--check --tier all` (44.8 s of it solving;
the rest is 19 process starts and 19 MPS parses). Measured on a quiet box,
aarch64-apple-darwin, release + `target-cpu=native`, `AY_MILP_THREADS=1`. Add a
release build that is free when warm and ~2m15s cold. `--tier fast`
(14 instances, 7.2 s) exists and is the fallback if that budget ever stops being
affordable — the difference buys `pk1` and `mas76`, the two largest trees in the
corpus.

**It blocks on exit 2 as well as exit 1.** Exit 2 means the gate measured
nothing: either the box is busy (it refuses above `0.35 x cpu_count`, because two
pinned instances have wall-deadline-bounded root cut loops) or the corpus is
missing. Reporting "measured nothing" as clean is the exact failure this step
exists to end. Quiet the box, or `git push --no-verify`.

An intended node-count change is ratcheted deliberately, in the same commit:

```sh
python3 scripts/milp_node_gate.py --ratchet --tier all
```

### Install (owner opt-in — not forced)

```sh
git config core.hooksPath scripts/git-hooks
```

### Uninstall

```sh
git config --unset core.hooksPath
```

### Bypass a single push (e.g. docs-only)

```sh
git push --no-verify
```

### Run the gate manually at any time

```sh
python3 scripts/check_no_python_test_skips.py
bash scripts/ci/smt_soundness_gate.sh
python3 scripts/milp_gate_corpus.py --verify
python3 scripts/milp_node_gate.py --check --tier all
```
