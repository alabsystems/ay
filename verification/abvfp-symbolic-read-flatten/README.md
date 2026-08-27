# Exactness obligations: symbolic-index array-read elimination

`crates/ay-dpll/src/executor/theories/fp/flatten_reads.rs` used to eliminate
only reads at a **bitvector-literal** index. It now eliminates reads at an
arbitrary bitvector index, which is exact only because every pair of distinct
cells on one array carries the Ackermann congruence axiom

```smt2
(=> (= i j) (= r_i r_j))
```

Regenerate and re-discharge with:

```sh
python3 gen_obligations.py cases && ./run.sh
```

## Why these obligations and not a single one

Equisatisfiability quantifies over the existence of an array, so it is not a
quantifier-free query. It splits into two directions that *are*:

| obligation | statement | expected |
|---|---|---|
| `FWD` | a model of the original yields a model of the flattened form (`r := A[i]`) | `unsat` |
| `BWD` | a model of the flattened form yields a witness array `store(store(K,j,r2),i,r1)` for the original | `unsat` |
| `AX` | the axiom is *entailed* by array functionality, so it can never delete a real model | `unsat` |

`BWD` is the direction the axiom pays for: the witness array can satisfy both
reads only when `r1` and `r2` agree wherever `i` and `j` do.

## The mutants are the point

A barrier you cannot make fail is not a barrier. Each mutant below removes
exactly one thing and must flip:

| mutant | what it removes | expected |
|---|---|---|
| `BWD_NOAX` | the congruence axiom from the flattened form | **`sat`** |
| `AX_NOFUNC` | the array (cells as independent constants) | **`sat`** |
| `XARRAY` | the same-array restriction (reads on `A` vs `B`) | **`sat`** |

`BWD_NOAX` coming back `sat` is the whole argument: without the axiom there is a
concrete assignment satisfying the flattened formula that **no array can
witness**. That is a false `sat`, and it is what the axiom removes.

`XARRAY` is the converse guard — it shows why an axiom may never span two
arrays. Emitting one would force unrelated arrays to agree and delete real
models.

## Results (2026-08-25)

z3 4.16.0, cvc5 1.3.0, bitwuzla 0.9.1 — index width 32, element width 8.

| obligation | z3 | cvc5 | bitwuzla |
|---|---|---|---|
| `FWD` | unsat | unsat | unsat |
| `BWD` | unsat | unsat | unsat |
| `AX` | unsat | unsat | unsat |
| `BWD_NOAX` | sat | sat | sat |
| `AX_NOFUNC` | sat | sat | sat |
| `XARRAY` | sat | sat | sat |

All three solvers agree on all six. `run.sh` exits non-zero on any mismatch.

## What is NOT covered here

The pass still abstains on `store`, on array-sorted equality/`ite`, on nested
arrays, and on quantifiers — see `FlattenAbstain`. Those side conditions are
unchanged and are what the module docs' backward-direction argument relies on;
nothing in this directory licenses relaxing them.
