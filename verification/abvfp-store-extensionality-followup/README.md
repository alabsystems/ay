# Follow-up: store-extensionality on a common base (NOT YET IMPLEMENTED)

This directory records a *measured, discharged* obligation for work that was
**deliberately not landed**. Nothing here is wired into the solver.

## Why it is here

`flatten_reads` (see `../abvfp-symbolic-read-flatten/`) now handles symbolic
read indices and non-BV element sorts. It still abstains on `store`, on nested
arrays, and on extensional array equality — and those three, not the symbolic
index, are what block the Inc Equality_MachineArith 188-query bucket. See
the development design notes §4.

`gen_probes.py` reconstructs the real image_filter idx-47 query shape and the
isolation probes that establish the two walls are independent. It also emits
`obl_rewrite_exact.smt2`, the exactness obligation for the rewrite that step 2
of the remaining chain would need:

```smt2
(= (store A i v) (store A j w))
  <=>
(ite (= i j) (= v w) (and (= v (select A i)) (= w (select A j))))
```

applied pairwise, after transitivity through the shared symbol, to the real
8-conjunct byte-write shape.

## Result (2026-08-25)

| obligation | z3 4.16.0 | cvc5 1.3.0 | bitwuzla 0.9.1 |
|---|---|---|---|
| `obl_rewrite_exact` | unsat | unsat | unsat |

The rewrite is exact. That is a necessary condition for the follow-up, not a
sufficient one: it still needs the array-symbol elimination that licenses the
transitivity step, a nested-select congruence closure, its own mutation
barriers, and a per-index measurement. Do not implement it from this file alone.

## Regenerate

```sh
python3 gen_probes.py cases
```
