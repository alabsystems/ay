#!/usr/bin/env python3
"""Width-32 exactness for the restoring-division circuit, via a chain of
obligations that are individually tractable.

The direct miter (`circuit == bvudiv`) is out of reach: measured bitwuzla time
is 4 s at W=12, 45 s at W=16, 556 s at W=20 and >600 s at W=24. So the same
statement is discharged in pieces, all at the real width 32:

  F  the circuit's own telescoping identity, in exact 64-bit arithmetic and
     with NO division and NO multiplication anywhere:
         zext64(a) = ACC + zext64(rem_0)
     where ACC accumulates `ge_i ? b : 0` through the same shift the remainder
     uses, so ACC is literally the schoolbook expansion of quot * b.
  FR the surviving remainder is a proper remainder:  b != 0  ->  rem_0 <u b.
  G  ACC really is that product:  ACC = zext64(quot) * zext64(b).
  H  Euclidean division is unique, so F+FR+G pin quot and rem_0 to the SMT-LIB
     operators:  b != 0 and zext64(a) = zext64(q)*zext64(b) + zext64(r) and
     r <u b  ->  q = bvudiv a b  and  r = bvurem a b.
  Z  the zero divisor, which the loop handles with no special case:
         b = 0  ->  quot = all-ones  and  rem_0 = a.

F, FR, G, H, Z together are exactly `circuit == bvudiv/bvurem` at width 32.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
OUT = HERE + "/ctl"
N = 32


def write(name, body):
    open(os.path.join(OUT, name), "w").write(body)
    print(name)


def circuit_defs(n):
    """Same circuit as gen_obligations.circuit, plus the ACC accumulator."""
    lines = []
    rem = "(_ bv0 %d)" % n
    acc = "(_ bv0 %d)" % (2 * n)
    qbits = {}
    for i in reversed(range(n)):
        lines.append(
            "(define-fun sh%d () (_ BitVec %d) (concat ((_ extract %d 0) %s) ((_ extract %d %d) a)))"
            % (i, n, n - 2, rem, i, i)
        )
        lines.append("(define-fun tr%d () (_ BitVec %d) (bvsub sh%d b))" % (i, n, i))
        lines.append("(define-fun ge%d () Bool (bvuge sh%d b))" % (i, i))
        lines.append("(define-fun rem%d () (_ BitVec %d) (ite ge%d tr%d sh%d))" % (i, n, i, i, i))
        lines.append(
            "(define-fun acc%d () (_ BitVec %d) (bvadd (bvshl %s (_ bv1 %d)) "
            "(ite ge%d ((_ zero_extend %d) b) (_ bv0 %d))))"
            % (i, 2 * n, acc, 2 * n, i, n, 2 * n)
        )
        rem = "rem%d" % i
        acc = "acc%d" % i
        qbits[i] = "(ite ge%d #b1 #b0)" % i
    lines.append(
        "(define-fun quot () (_ BitVec %d) (concat %s))"
        % (n, " ".join(qbits[i] for i in reversed(range(n))))
    )
    return "\n".join(lines), rem, acc


HDR = """; AY FP-side BV division bit-blaster -- width-32 exactness chain
; unsat == the property holds on every input
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
"""

defs, rem, acc = circuit_defs(N)
head = HDR + defs + "\n"

write(
    "F_telescope_W32.smt2",
    head
    + "(assert (not (= ((_ zero_extend 32) a) (bvadd %s ((_ zero_extend 32) %s)))))\n(check-sat)\n"
    % (acc, rem),
)

write(
    "FR_remainder_lt_divisor_W32.smt2",
    head
    + "(assert (not (= b (_ bv0 32))))\n"
    + "(assert (not (bvult %s b)))\n(check-sat)\n" % rem,
)

write(
    "G_acc_is_the_product_W32.smt2",
    head
    + "(assert (not (= %s (bvmul ((_ zero_extend 32) quot) ((_ zero_extend 32) b)))))\n(check-sat)\n"
    % acc,
)

write(
    "Z_zero_divisor_W32.smt2",
    head
    + "(assert (= b (_ bv0 32)))\n"
    + "(assert (not (and (= quot (bvnot (_ bv0 32))) (= %s a))))\n(check-sat)\n" % rem,
)

write(
    "H_euclid_unique_W32.smt2",
    """; Euclidean division is unique -- a fact about SMT-LIB's own operators,
; independent of anything AY emits.
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun q () (_ BitVec 32))
(declare-fun r () (_ BitVec 32))
(assert (not (= b (_ bv0 32))))
(assert (= ((_ zero_extend 32) a)
           (bvadd (bvmul ((_ zero_extend 32) q) ((_ zero_extend 32) b))
                  ((_ zero_extend 32) r))))
(assert (bvult r b))
(assert (not (and (= q (bvudiv a b)) (= r (bvurem a b)))))
(check-sat)
""",
)
