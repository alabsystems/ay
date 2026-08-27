#!/usr/bin/env python3
"""Sign-fix obligations with the divider left UNINTERPRETED.

AY normalises a signed division to magnitudes, calls the unsigned divider ONCE,
and fixes the sign of the result. SMT-LIB instead defines `bvsdiv`/`bvsrem` by a
four-way case split with four separate `bvudiv`/`bvurem` calls. That the two
agree is a fact about the case split alone -- it holds for ANY function in the
divider's place -- so the obligation is stated over an uninterpreted `D`/`R`.

Two payoffs: the statement is exactly the layer AY implements (nothing about the
divider leaks in), and it is decidable at the real width 32 by every oracle in
milliseconds instead of being a divider miter.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = HERE + "/ctl"
os.makedirs(OUT, exist_ok=True)


def write(name, body):
    open(os.path.join(OUT, name), "w").write(body)
    print(name)


HDR = """; AY FP-side BV division bit-blaster -- sign-fix exactness, divider uninterpreted
; unsat == AY's one-call sign normalisation equals the SMT-LIB definitional
;          expansion for EVERY divider function, hence in particular for bvudiv.
(set-logic QF_UFBV)
(declare-fun a () (_ BitVec {n}))
(declare-fun b () (_ BitVec {n}))
(declare-fun D ((_ BitVec {n}) (_ BitVec {n})) (_ BitVec {n}))
(define-fun ms () Bool (= ((_ extract {m} {m}) a) #b1))
(define-fun mt () Bool (= ((_ extract {m} {m}) b) #b1))
(define-fun absa () (_ BitVec {n}) (ite ms (bvneg a) a))
(define-fun absb () (_ BitVec {n}) (ite mt (bvneg b) b))
"""


def gen(n):
    head = HDR.format(n=n, m=n - 1)

    # bvsdiv
    ay = "(define-fun ay () (_ BitVec {n}) (ite (xor ms mt) (bvneg (D absa absb)) (D absa absb)))\n"
    std = """(define-fun std () (_ BitVec {n})
  (ite (and (not ms) (not mt)) (D a b)
  (ite (and ms (not mt)) (bvneg (D (bvneg a) b))
  (ite (and (not ms) mt) (bvneg (D a (bvneg b)))
       (D (bvneg a) (bvneg b))))))
"""
    write(
        "U3_sdiv_signfix_uf_W%d.smt2" % n,
        head + ay.format(n=n) + std.format(n=n) + "(assert (not (= ay std)))\n(check-sat)\n",
    )
    # negative control: negate when the signs AGREE
    write(
        "U3N_sdiv_signfix_uf_and_W%d.smt2" % n,
        head
        + "(define-fun ay () (_ BitVec %d) (ite (and ms mt) (bvneg (D absa absb)) (D absa absb)))\n"
        % n
        + std.format(n=n)
        + "(assert (not (= ay std)))\n(check-sat)\n",
    )

    # bvsrem
    ay_r = "(define-fun ay () (_ BitVec {n}) (ite ms (bvneg (D absa absb)) (D absa absb)))\n"
    std_r = """(define-fun std () (_ BitVec {n})
  (ite (and (not ms) (not mt)) (D a b)
  (ite (and ms (not mt)) (bvneg (D (bvneg a) b))
  (ite (and (not ms) mt) (D a (bvneg b))
       (bvneg (D (bvneg a) (bvneg b)))))))
"""
    write(
        "U4_srem_signfix_uf_W%d.smt2" % n,
        head + ay_r.format(n=n) + std_r.format(n=n) + "(assert (not (= ay std)))\n(check-sat)\n",
    )
    # negative control: take the sign of the divisor
    write(
        "U4N_srem_signfix_uf_divisor_W%d.smt2" % n,
        head
        + "(define-fun ay () (_ BitVec %d) (ite mt (bvneg (D absa absb)) (D absa absb)))\n" % n
        + std_r.format(n=n)
        + "(assert (not (= ay std)))\n(check-sat)\n",
    )

    # bvsmod: AY's nested ite vs the standard's, both over the same u = R(|a|,|b|)
    ay_m = """(define-fun u () (_ BitVec {n}) (D absa absb))
(define-fun ay () (_ BitVec {n})
  (ite (= u (_ bv0 {n})) u
  (ite (and (not ms) (not mt)) u
  (ite (and ms (not mt)) (bvadd (bvneg u) b)
  (ite (and (not ms) mt) (bvadd u b) (bvneg u))))))
"""
    std_m = """(define-fun std () (_ BitVec {n})
  (ite (= u (_ bv0 {n})) u
  (ite (and (= ((_ extract {m} {m}) a) #b0) (= ((_ extract {m} {m}) b) #b0)) u
  (ite (and (= ((_ extract {m} {m}) a) #b1) (= ((_ extract {m} {m}) b) #b0)) (bvadd (bvneg u) b)
  (ite (and (= ((_ extract {m} {m}) a) #b0) (= ((_ extract {m} {m}) b) #b1)) (bvadd u b)
       (bvneg u))))))
"""
    write(
        "U5_smod_signfix_uf_W%d.smt2" % n,
        head
        + ay_m.format(n=n)
        + std_m.format(n=n, m=n - 1)
        + "(assert (not (= ay std)))\n(check-sat)\n",
    )
    # negative control: drop the u = 0 guard
    write(
        "U5N_smod_signfix_uf_no_guard_W%d.smt2" % n,
        head
        + "(define-fun u () (_ BitVec {n}) (D absa absb))\n".format(n=n)
        + """(define-fun ay () (_ BitVec {n})
  (ite (and (not ms) (not mt)) u
  (ite (and ms (not mt)) (bvadd (bvneg u) b)
  (ite (and (not ms) mt) (bvadd u b) (bvneg u)))))
""".format(n=n)
        + std_m.format(n=n, m=n - 1)
        + "(assert (not (= ay std)))\n(check-sat)\n",
    )


for n in [int(x) for x in sys.argv[1:]] or [32]:
    gen(n)
