#!/usr/bin/env python3
"""Generate the exactness obligations for AY's FP-side BV division bit-blaster.

Every obligation mirrors, line for line, the circuit that
`crates/ay-theories/fp/src/bv_circuits.rs` builds:

  bv_udiv_urem(a, b):                      # restoring division, n-bit remainder
      rem = 0; quot = 0
      for i in (0..n).rev():
          shifted = (rem << 1) | a[i]      # n bits, top bit of rem DISCARDED
          trial   = shifted - b
          ge      = shifted >=u b
          quot[i] = ge
          rem     = ge ? trial : shifted
      return (quot, rem)

and the signed wrappers added in `bitblast.rs`.

Each file asserts the NEGATION of the equivalence, so `unsat` == exact.
"""
import os
import sys

OUT = os.path.dirname(os.path.abspath(__file__)) + "/ctl"
os.makedirs(OUT, exist_ok=True)


def circuit(n, a="a", b="b", pfx=""):
    """Emit define-funs for the restoring-division circuit; return (defs, q, r)."""
    lines = []
    rem = "(_ bv0 %d)" % n
    qbits = {}
    for i in reversed(range(n)):
        if n >= 2:
            shifted = "(concat ((_ extract %d 0) %s) ((_ extract %d %d) %s))" % (
                n - 2,
                rem,
                i,
                i,
                a,
            )
        else:
            shifted = "((_ extract %d %d) %s)" % (i, i, a)
        lines.append("(define-fun %ssh%d () (_ BitVec %d) %s)" % (pfx, i, n, shifted))
        sh = "%ssh%d" % (pfx, i)
        lines.append(
            "(define-fun %str%d () (_ BitVec %d) (bvsub %s %s))" % (pfx, i, n, sh, b)
        )
        lines.append("(define-fun %sge%d () Bool (bvuge %s %s))" % (pfx, i, sh, b))
        lines.append(
            "(define-fun %srem%d () (_ BitVec %d) (ite %sge%d %str%d %s))"
            % (pfx, i, n, pfx, i, pfx, i, sh)
        )
        rem = "%srem%d" % (pfx, i)
        qbits[i] = "(ite %sge%d #b1 #b0)" % (pfx, i)
    q = qbits[0] if n == 1 else "(concat %s)" % " ".join(qbits[i] for i in reversed(range(n)))
    lines.append("(define-fun %squot () (_ BitVec %d) %s)" % (pfx, n, q))
    return lines, "%squot" % pfx, rem


HDR = """; AY FP-side BV division bit-blaster -- exactness obligation
; unsat  ==  the encoding AY emits is equal to the SMT-LIB operator on every input
(set-logic QF_BV)
(declare-fun a () (_ BitVec {n}))
(declare-fun b () (_ BitVec {n}))
"""


def write(name, body):
    p = os.path.join(OUT, name)
    open(p, "w").write(body)
    print(p)


def gen(n):
    defs, q, r = circuit(n)
    head = HDR.format(n=n) + "\n".join(defs) + "\n"

    # O1: circuit quotient == bvudiv (all a, all b, including b = 0)
    write(
        "O1_udiv_circuit_W%d.smt2" % n,
        head + "(assert (not (= %s (bvudiv a b))))\n(check-sat)\n" % q,
    )
    # O2: circuit remainder == bvurem (all a, all b, including b = 0)
    write(
        "O2_urem_circuit_W%d.smt2" % n,
        head + "(assert (not (= %s (bvurem a b))))\n(check-sat)\n" % r,
    )

    ms = "(= ((_ extract {m} {m}) a) #b1)".format(m=n - 1)
    mt = "(= ((_ extract {m} {m}) b) #b1)".format(m=n - 1)
    signs = """(define-fun ms () Bool {ms})
(define-fun mt () Bool {mt})
(define-fun absa () (_ BitVec {n}) (ite ms (bvneg a) a))
(define-fun absb () (_ BitVec {n}) (ite mt (bvneg b) b))
""".format(ms=ms, mt=mt, n=n)

    # O3: AY's sign normalisation over bvudiv == bvsdiv
    write(
        "O3_sdiv_signfix_W%d.smt2" % n,
        HDR.format(n=n)
        + signs
        + "(define-fun q () (_ BitVec %d) (bvudiv absa absb))\n" % n
        + "(define-fun sdiv () (_ BitVec %d) (ite (xor ms mt) (bvneg q) q))\n" % n
        + "(assert (not (= sdiv (bvsdiv a b))))\n(check-sat)\n",
    )
    # O4: AY's sign normalisation over bvurem == bvsrem
    write(
        "O4_srem_signfix_W%d.smt2" % n,
        HDR.format(n=n)
        + signs
        + "(define-fun u () (_ BitVec %d) (bvurem absa absb))\n" % n
        + "(define-fun srem () (_ BitVec %d) (ite ms (bvneg u) u))\n" % n
        + "(assert (not (= srem (bvsrem a b))))\n(check-sat)\n",
    )
    # O5: AY's smod expansion == bvsmod
    write(
        "O5_smod_signfix_W%d.smt2" % n,
        HDR.format(n=n)
        + signs
        + "(define-fun u () (_ BitVec %d) (bvurem absa absb))\n" % n
        + "(define-fun smod () (_ BitVec {n}) "
        "(ite (= u (_ bv0 {n})) u "
        "(ite (and (not ms) (not mt)) u "
        "(ite (and ms (not mt)) (bvadd (bvneg u) b) "
        "(ite (and (not ms) mt) (bvadd u b) (bvneg u))))))\n".format(n=n)
        + "(assert (not (= smod (bvsmod a b))))\n(check-sat)\n",
    )

    # O6: fused end-to-end -- the actual circuit AY emits for bvsdiv == bvsdiv.
    fdefs, fq, fr = circuit(n, a="absa", b="absb", pfx="f")
    fused = (
        HDR.format(n=n)
        + signs
        + "\n".join(fdefs)
        + "\n(define-fun sdiv () (_ BitVec %d) (ite (xor ms mt) (bvneg %s) %s))\n" % (n, fq, fq)
        + "(assert (not (= sdiv (bvsdiv a b))))\n(check-sat)\n"
    )
    write("O6_sdiv_fused_W%d.smt2" % n, fused)

    # O7: fused end-to-end for bvsrem.
    fused_r = (
        HDR.format(n=n)
        + signs
        + "\n".join(fdefs)
        + "\n(define-fun srem () (_ BitVec %d) (ite ms (bvneg %s) %s))\n" % (n, fr, fr)
        + "(assert (not (= srem (bvsrem a b))))\n(check-sat)\n"
    )
    write("O7_srem_fused_W%d.smt2" % n, fused_r)


for n in [int(x) for x in sys.argv[1:]] or [32]:
    gen(n)
