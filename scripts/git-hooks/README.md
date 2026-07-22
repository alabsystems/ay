# In-tree git hooks

GitHub Actions checks the complete public workspace and runs focused SAT-core
and LRAT-checker tests on pushes and pull requests. These opt-in hooks provide
earlier feedback and additional local soundness coverage; they supplement,
rather than replace, the hosted CI checks.

## `pre-push` — SMT soundness-differential gate

When installed, the hook runs `scripts/ci/smt_soundness_gate.sh` before each
push. It adds two complementary checks over the committed Tier-0 corpus:

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
bash scripts/ci/smt_soundness_gate.sh
```
