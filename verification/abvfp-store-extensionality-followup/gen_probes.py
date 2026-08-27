#!/usr/bin/env python3
"""Generate isolation probes for the image_filter idx-47 query shape.

The real query is
  (exists ((q BV64))
    (and  <8 nested-array store equalities pinning q's bytes into memory>
          <one FP-constructor equality pinning q's bit pattern to -1.0> ))
Each probe removes exactly one wall so the blocking mechanism is attributable.
"""
import pathlib, sys

OUT = pathlib.Path(sys.argv[1])
OUT.mkdir(parents=True, exist_ok=True)

DECLS = """(set-logic ABVFP)
(declare-fun base () (_ BitVec 32))
(declare-fun off () (_ BitVec 32))
(declare-fun mem5 () (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 8))))
(declare-fun mem6 () (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 8))))
"""

def idx(k):
    return "off" if k == 0 else f"(bvadd off (_ bv{k} 32))"

def byte(k):
    return f"((_ extract {8*k+7} {8*k}) q)"

def store_eq(k):
    return (f"(= mem5 (store mem6 base (store (select mem6 base) "
            f"{idx(k)} {byte(k)})))")

ARRAY_CONJ = "\n    ".join(store_eq(k) for k in range(8))

FP_CONJ = ("(= (fp ((_ extract 63 63) q) ((_ extract 62 52) q) "
           "((_ extract 51 0) q)) ((_ to_fp 11 53) RNE (_ bv4294967295 32)))")

# ---- P_full: the real shape, verbatim ------------------------------------
(OUT / "p_full.smt2").write_text(
    DECLS + f"(assert (exists ((q (_ BitVec 64))) (and\n    {ARRAY_CONJ}\n    {FP_CONJ})))\n(check-sat)\n")

# ---- P_arrayonly: drop the FP conjunct -----------------------------------
(OUT / "p_arrayonly.smt2").write_text(
    DECLS + f"(assert (exists ((q (_ BitVec 64))) (and\n    {ARRAY_CONJ})))\n(check-sat)\n")

# ---- P_fponly: drop the array conjuncts ----------------------------------
(OUT / "p_fponly.smt2").write_text(
    DECLS + f"(assert (exists ((q (_ BitVec 64))) (and\n    {FP_CONJ})))\n(check-sat)\n")

# ---- P_fpground: FP conjunct with q a free constant (no quantifier) ------
(OUT / "p_fpground.smt2").write_text(
    "(set-logic QF_BVFP)\n(declare-fun q () (_ BitVec 64))\n"
    f"(assert {FP_CONJ})\n(check-sat)\n")

# ---- P_rw: array conjuncts replaced by the store-extensionality rewrite --
# (= (store A i v) (store A j w))  <=>  ite(i=j, v=w, v=(select A i) /\ w=(select A j))
# applied pairwise against k=0 after transitivity through mem5.
inner = "(select mem6 base)"
rw = [store_eq(0)]
for k in range(1, 8):
    rw.append(f"(ite (= {idx(0)} {idx(k)}) (= {byte(0)} {byte(k)}) "
              f"(and (= {byte(0)} (select {inner} {idx(0)})) "
              f"(= {byte(k)} (select {inner} {idx(k)}))))")
RW_CONJ = "\n    ".join(rw)
(OUT / "p_rw.smt2").write_text(
    DECLS + f"(assert (exists ((q (_ BitVec 64))) (and\n    {RW_CONJ}\n    {FP_CONJ})))\n(check-sat)\n")

# ---- OBLIGATION: the rewrite is EXACT (must be unsat in every solver) ----
(OUT / "obl_rewrite_exact.smt2").write_text(
    DECLS + "(declare-fun q () (_ BitVec 64))\n"
    f"(assert (not (= (and\n    {ARRAY_CONJ})\n  (and\n    {RW_CONJ}))))\n(check-sat)\n"
    .replace("(set-logic ABVFP)", ""))

print("\n".join(str(p) for p in sorted(OUT.glob("*.smt2"))))
