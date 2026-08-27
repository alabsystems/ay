#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Exactness obligations for the symbolic-index array-read elimination.

The pass replaces every `(select A i)` on a declared array symbol by a fresh
constant `r_i` and, for every pair of distinct cells on the same array, asserts
the Ackermann congruence axiom

    (=> (= i j) (= r_i r_j))

Equisatisfiability is a statement about the EXISTENCE of an array, so it is not
itself a quantifier-free SMT query. It splits into two quantifier-free
obligations that together give both directions, plus the mutants that show each
one is load-bearing.

Let  phi(A)      := P(select(A,i), select(A,j), i, j)         -- original
     phi'(r1,r2) := P(r1, r2, i, j)  /\  (=> (= i j) (= r1 r2))  -- flattened

FWD  phi(A) /\ r1 = A[i] /\ r2 = A[j]  ==>  phi'(r1,r2)
       "every model of the original yields a model of the flattened form",
       and in particular the axiom is ENTAILED by array functionality.

BWD  phi'(r1,r2) /\ A = store(store(K,j,r2),i,r1)  ==>  phi(A)
       "every model of the flattened form yields an array witnessing the
       original". This is the direction the congruence axiom pays for: the
       witness array can only satisfy both reads when r1 and r2 agree wherever
       i and j do.

Each obligation is emitted as its NEGATION, so the expected answer is `unsat`.

MUTANTS drop the congruence axiom from phi'. BWD_NOAX must come back `sat` — a
concrete counter-model in which the flattened form is satisfiable but no array
witnesses it. That is precisely the false-`sat` the axiom prevents, and it is
what makes this a barrier rather than a decoration.
"""
import pathlib, sys

OUT = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "cases")
OUT.mkdir(parents=True, exist_ok=True)

IW, EW = 32, 8  # index width, element width

DECLS = f"""(set-logic QF_ABV)
(declare-fun A () (Array (_ BitVec {IW}) (_ BitVec {EW})))
(declare-fun K () (Array (_ BitVec {IW}) (_ BitVec {EW})))
(declare-fun i () (_ BitVec {IW}))
(declare-fun j () (_ BitVec {IW}))
(declare-fun r1 () (_ BitVec {EW}))
(declare-fun r2 () (_ BitVec {EW}))
"""

# A deliberately non-trivial body mentioning both reads and both indices, so the
# obligation is not discharged by P being insensitive to its arguments.
def P(a, b):
    return (f"(and (bvult {a} {b}) "
            f"(= (bvadd {a} {b}) ((_ extract {EW-1} 0) i)) "
            f"(bvuge {b} ((_ extract {EW-1} 0) j)))")

PHI_A = P("(select A i)", "(select A j)")
AXIOM = "(=> (= i j) (= r1 r2))"
PHI_F = f"(and {P('r1', 'r2')} {AXIOM})"
PHI_F_NOAX = P("r1", "r2")
WITNESS = "(= A (store (store K j r2) i r1))"


def emit(name, body, expect):
    (OUT / f"{name}.smt2").write_text(DECLS + body + "(check-sat)\n")
    (OUT / f"{name}.expect").write_text(expect + "\n")


# ---- FWD: original |= flattened ------------------------------------------
emit("FWD",
     f"(assert (not (=> (and {PHI_A} (= r1 (select A i)) (= r2 (select A j)))\n"
     f"                 {PHI_F})))\n", "unsat")

# ---- BWD: flattened + witness array |= original ---------------------------
emit("BWD",
     f"(assert (not (=> (and {PHI_F} {WITNESS}) {PHI_A})))\n", "unsat")

# ---- AX: the congruence axiom is ENTAILED by array functionality ----------
# (this is the forward direction in its sharpest form: it can never remove a
#  model of the original)
emit("AX",
     f"(assert (and (= i j) (not (= (select A i) (select A j)))))\n", "unsat")

# ---- MUTANT BWD_NOAX: drop the axiom; the backward direction must BREAK ---
emit("BWD_NOAX",
     f"(assert (not (=> (and {PHI_F_NOAX} {WITNESS}) {PHI_A})))\n", "sat")

# ---- MUTANT AX_NOFUNC: cells as independent constants are NOT tied --------
# shows the axiom is not vacuous: with r1/r2 free, i = j does not force r1 = r2
emit("AX_NOFUNC",
     f"(assert (and (= i j) (not (= r1 r2))))\n", "sat")

# ---- MUTANT XARRAY: relating cells across DIFFERENT arrays is unsound -----
# the pass must never emit an axiom spanning two arrays; this shows why.
(OUT / "XARRAY.smt2").write_text(
    DECLS + f"(declare-fun B () (Array (_ BitVec {IW}) (_ BitVec {EW})))\n"
    "(assert (and (= i j) (not (= (select A i) (select B j)))))\n(check-sat)\n")
(OUT / "XARRAY.expect").write_text("sat\n")

print("\n".join(sorted(p.name for p in OUT.glob("*.smt2"))))
