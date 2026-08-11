# Wrong-`unsat` regression fixtures — QF_NRA meti-tarski `exp__problem__10__3`

**P0, found 2026-07-30.** Every file here is one AY currently answers **`unsat`** on, while
both oracles say **`sat`**:

- the file's own `(set-info :status sat)`, and
- z3 5.0.0 (`-T:60`), independently.

AY's wrong verdict is fast (sub-second), stable, and reproduces at every deadline where AY
is definite — this is **not** a timeout or truncation artifact.

```
$ ay --competition -T:5 chunk-0087.smt2      # -> unsat   WRONG
$ z3 -T:60          chunk-0087.smt2          # -> sat
```

## Why these matter more than a wrong `sat`

**No gate in AY's funnel can catch a wrong `unsat`.** The independent model-check gate, the
strict model-validation gate and `--self-check` all validate a *model*, and a model only
exists on the `sat` side. A wrong `unsat` has no witness to check. Only a proof/certificate
check or a differential oracle can gate this class — neither does today.

These sit in the campaign's **headline win target**: MV QF_NRA, where meti-tarski is 79% of
the division.

## Blast radius (measured over 6,294 corpus files)

Confined to `exp__problem__10__3` (incl. `__weak__`): **7 of 129 definite verdicts (5.4%)**.
Zero contradictions in 3,000 randomly sampled QF_NRA files, zero in sibling `exp__problem`
families, and zero on this family's declared-`unsat` side. The concentration points at a
specific `exp`-related rewriting/relaxation step that *strengthens* the problem (adds a
constraint that does not follow), not at broad unsoundness.

## What "fixed" means

Each file must return `sat` (with a model that validates) or `unknown`. **`unsat` is a
soundness failure.** Do not weaken these to "any non-unsat"; `unknown` is acceptable only as
an interim fail-closed state, and the family should ultimately be solved.

Full analysis: the development design notes.
Provenance: SMT-LIB QF_NRA, Zenodo record 11061097 (fetched via `ay-z3-parity fetch`).
