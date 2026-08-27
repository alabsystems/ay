#!/usr/bin/env python3
"""Negative controls for the FIX-C exactness obligations.

Each file is the SAME obligation with ONE mutation of the encoding. Every one
must come back `sat` on all three oracles. An obligation that stays `unsat`
under mutation is not checking anything.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_obligations import circuit, HDR  # noqa: E402

OUT = HERE + "/ctl"


def write(name, body):
    open(os.path.join(OUT, name), "w").write(body)
    print(name)


def mut_circuit(n, ge_op="bvuge", drop_top=1, a="a", b="b", pfx=""):
    lines = []
    rem = "(_ bv0 %d)" % n
    qbits = {}
    for i in reversed(range(n)):
        shifted = "(concat ((_ extract %d 0) %s) ((_ extract %d %d) %s))" % (
            n - 1 - drop_top,
            rem,
            i,
            i,
            a,
        )
        if drop_top != 1:
            shifted = "((_ extract %d 0) %s)" % (n - 1, shifted)
        lines.append("(define-fun %ssh%d () (_ BitVec %d) %s)" % (pfx, i, n, shifted))
        sh = "%ssh%d" % (pfx, i)
        lines.append("(define-fun %str%d () (_ BitVec %d) (bvsub %s %s))" % (pfx, i, n, sh, b))
        lines.append("(define-fun %sge%d () Bool (%s %s %s))" % (pfx, i, ge_op, sh, b))
        lines.append(
            "(define-fun %srem%d () (_ BitVec %d) (ite %sge%d %str%d %s))"
            % (pfx, i, n, pfx, i, pfx, i, sh)
        )
        rem = "%srem%d" % (pfx, i)
        qbits[i] = "(ite %sge%d #b1 #b0)" % (pfx, i)
    q = "(concat %s)" % " ".join(qbits[i] for i in reversed(range(n)))
    lines.append("(define-fun %squot () (_ BitVec %d) %s)" % (pfx, n, q))
    return lines, "%squot" % pfx, rem


def gen(n):
    signs = """(define-fun ms () Bool (= ((_ extract {m} {m}) a) #b1))
(define-fun mt () Bool (= ((_ extract {m} {m}) b) #b1))
(define-fun absa () (_ BitVec {n}) (ite ms (bvneg a) a))
(define-fun absb () (_ BitVec {n}) (ite mt (bvneg b) b))
""".format(m=n - 1, n=n)

    # N1: strict `bvugt` where the circuit uses `bvuge`.
    d, q, _ = mut_circuit(n, ge_op="bvugt")
    write(
        "N1_udiv_ugt_W%d.smt2" % n,
        HDR.format(n=n) + "\n".join(d) + "\n(assert (not (= %s (bvudiv a b))))\n(check-sat)\n" % q,
    )

    # N2: sdiv negates the quotient when the signs AGREE instead of differ.
    write(
        "N2_sdiv_and_W%d.smt2" % n,
        HDR.format(n=n)
        + signs
        + "(define-fun q () (_ BitVec %d) (bvudiv absa absb))\n" % n
        + "(define-fun sdiv () (_ BitVec %d) (ite (and ms mt) (bvneg q) q))\n" % n
        + "(assert (not (= sdiv (bvsdiv a b))))\n(check-sat)\n",
    )

    # N3: srem takes the sign of the DIVISOR instead of the dividend.
    write(
        "N3_srem_divisor_sign_W%d.smt2" % n,
        HDR.format(n=n)
        + signs
        + "(define-fun u () (_ BitVec %d) (bvurem absa absb))\n" % n
        + "(define-fun srem () (_ BitVec %d) (ite mt (bvneg u) u))\n" % n
        + "(assert (not (= srem (bvsrem a b))))\n(check-sat)\n",
    )

    # N4: smod without the `u = 0` guard.
    write(
        "N4_smod_no_zero_guard_W%d.smt2" % n,
        HDR.format(n=n)
        + signs
        + "(define-fun u () (_ BitVec %d) (bvurem absa absb))\n" % n
        + "(define-fun smod () (_ BitVec {n}) "
        "(ite (and (not ms) (not mt)) u "
        "(ite (and ms (not mt)) (bvadd (bvneg u) b) "
        "(ite (and (not ms) mt) (bvadd u b) (bvneg u)))))\n".format(n=n)
        + "(assert (not (= smod (bvsmod a b))))\n(check-sat)\n",
    )

    # N5: magnitude taken with bvnot instead of bvneg (the classic off-by-one).
    write(
        "N5_sdiv_bvnot_abs_W%d.smt2" % n,
        HDR.format(n=n)
        + "(define-fun ms () Bool (= ((_ extract {m} {m}) a) #b1))\n"
        "(define-fun mt () Bool (= ((_ extract {m} {m}) b) #b1))\n".format(m=n - 1)
        + "(define-fun absa () (_ BitVec %d) (ite ms (bvnot a) a))\n" % n
        + "(define-fun absb () (_ BitVec %d) (ite mt (bvnot b) b))\n" % n
        + "(define-fun q () (_ BitVec %d) (bvudiv absa absb))\n" % n
        + "(define-fun sdiv () (_ BitVec %d) (ite (xor ms mt) (bvneg q) q))\n" % n
        + "(assert (not (= sdiv (bvsdiv a b))))\n(check-sat)\n",
    )

    # N6: the dividend bit is shifted in at the MSB end instead of the LSB end.
    lines = []
    rem = "(_ bv0 %d)" % n
    qbits = {}
    for i in reversed(range(n)):
        shifted = "(concat ((_ extract %d %d) a) ((_ extract %d 1) %s))" % (i, i, n - 1, rem)
        lines.append("(define-fun sh%d () (_ BitVec %d) %s)" % (i, n, shifted))
        lines.append("(define-fun tr%d () (_ BitVec %d) (bvsub sh%d b))" % (i, n, i))
        lines.append("(define-fun ge%d () Bool (bvuge sh%d b))" % (i, i))
        lines.append("(define-fun rem%d () (_ BitVec %d) (ite ge%d tr%d sh%d))" % (i, n, i, i, i))
        rem = "rem%d" % i
        qbits[i] = "(ite ge%d #b1 #b0)" % i
    q = "(concat %s)" % " ".join(qbits[i] for i in reversed(range(n)))
    write(
        "N6_udiv_shift_msb_W%d.smt2" % n,
        HDR.format(n=n)
        + "\n".join(lines)
        + "\n(assert (not (= %s (bvudiv a b))))\n(check-sat)\n" % q,
    )


for n in [int(x) for x in sys.argv[1:]] or [8]:
    gen(n)
