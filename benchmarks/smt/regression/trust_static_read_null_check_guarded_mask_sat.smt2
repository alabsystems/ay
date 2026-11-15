; A deductive verifier path condition: `finalize_tail_realmir` line 437,
; `[unsafe:sep:deref] null check for *_12.*` (the static read's pointer).
; Satisfiable (pinned z3 5.3.3: sat): the separation lane does not model a
; static's address, so Trust pins this row as a disclosed refutation.
; The two `bv2nat (bvand (int2bv_64 p) (int2bv_64 m))` terms are alignment-mask
; reads whose mask local is pinned by `(= m 7)` only inside each path disjunct,
; so `mk_bv2nat`'s literal-mask residue fold never fires and the BV/LIA bridge
; saw an opaque Int. Its candidate failed the model gate: unknown (incomplete).
; ay 20cf3eea8..b28809bab9 answered unknown. Earlier builds answered sat only
; because their LIA vertex happened to put both pointers at multiples of 8,
; which the reads (each asserted 0) require.
; The bridge's guarded mask residue (#guarded-mask-residue) decides it.
(set-logic ALL)
(set-info :status sat)
(declare-fun _10.0 () Int)
(declare-fun |_10.1#s4_0| () Bool)
(declare-fun _12 () Int)
(declare-fun _14 () Int)
(declare-fun _15 () Int)
(declare-fun _16 () Int)
(declare-fun _17 () Int)
(declare-fun _18 () Bool)
(declare-fun _2 () Bool)
(declare-fun _23 () Bool)
(declare-fun _24 () Int)
(declare-fun _25 () Int)
(declare-fun _26 () Int)
(declare-fun _27 () Int)
(declare-fun _28 () Bool)
(declare-fun _29 () Int)
(declare-fun _3 () Int)
(declare-fun _30 () Int)
(declare-fun _31 () Bool)
(declare-fun _32 () Bool)
(declare-fun _33 () Bool)
(declare-fun _34 () Bool)
(declare-fun _4 () Int)
(declare-fun _4* () Int)
(declare-fun _40 () Bool)
(declare-fun _41 () Int)
(declare-fun _42 () Int)
(declare-fun _43 () Bool)
(declare-fun _44 () Bool)
(declare-fun _45 () Bool)
(declare-fun _46 () Bool)
(declare-fun _5 () Int)
(declare-fun _6.0 () Int)
(declare-fun |_6.1#s10_1| () Bool)
(declare-fun _9 () Int)
(declare-fun __trust_opaque_ref_b0_s0_o0 () Int)
(declare-fun __trust_opaque_ref_b5_s1_o0 () Int)
(declare-fun __trust_sep__ptr__12.* () Int)
(assert (and true (or (and _28 _34 (not |_6.1#s10_1|) (not (> _3 _5)) (not |_10.1#s4_0|) _18 _46 (= _26 7) (= _27 (bv2nat (bvand ((_ int2bv 64) _25) ((_ int2bv 64) _26)))) (= _28 (= _27 0)) (= _31 (not (= 8 0))) (= _32 (= _30 0)) (= _33 (and _32 _31)) (= _34 (not _33)) (and (<= 0 (- 64 8)) (<= (- 64 8) 18446744073709551615)) (= _6.0 (- 64 8)) (and (<= 0 64) (<= 64 18446744073709551615)) (and (<= 0 8) (<= 8 18446744073709551615)) (= _5 56) (= _2 (> _3 _5)) (=> (not _2) (= _4 __trust_opaque_ref_b0_s0_o0)) (=> (not _2) (= _24 _4)) (=> (not _2) (= _25 _24)) (=> (not _2) (= _29 _4)) (=> (not _2) (= _30 _29)) (=> (not _2) (= _3 _4*)) (and (<= 0 (- 64 8)) (<= (- 64 8) 18446744073709551615)) (= _10.0 (- 64 8)) (and (<= 0 64) (<= 64 18446744073709551615)) (and (<= 0 8) (<= 8 18446744073709551615)) (= _9 56) (= _12 __trust_opaque_ref_b5_s1_o0) (= _14 _12) (= _15 _14) (= _16 7) (= _17 (bv2nat (bvand ((_ int2bv 64) _15) ((_ int2bv 64) _16)))) (= _18 (= _17 0)) (= _41 _12) (= _42 _41) (= _43 (not (= 8 0))) (= _44 (= _42 0)) (= _45 (and _44 _43)) (= _46 (not _45)) (= __trust_sep__ptr__12.* 0)) (and _28 _34 (not |_6.1#s10_1|) (> _3 _5) _23 _40 (not |_10.1#s4_0|) _18 _46 (= _26 7) (= _27 (bv2nat (bvand ((_ int2bv 64) _25) ((_ int2bv 64) _26)))) (= _28 (= _27 0)) (= _31 (not (= 8 0))) (= _32 (= _30 0)) (= _33 (and _32 _31)) (= _34 (not _33)) (and (<= 0 (- 64 8)) (<= (- 64 8) 18446744073709551615)) (= _6.0 (- 64 8)) (and (<= 0 64) (<= 64 18446744073709551615)) (and (<= 0 8) (<= 8 18446744073709551615)) (= _5 56) (= _2 (> _3 _5)) (=> (not _2) (= _4 __trust_opaque_ref_b0_s0_o0)) (=> (not _2) (= _24 _4)) (=> (not _2) (= _25 _24)) (=> (not _2) (= _29 _4)) (=> (not _2) (= _30 _29)) (=> (not _2) (= _3 _4*)) (and (<= 0 (- 64 8)) (<= (- 64 8) 18446744073709551615)) (= _10.0 (- 64 8)) (and (<= 0 64) (<= 64 18446744073709551615)) (and (<= 0 8) (<= 8 18446744073709551615)) (= _9 56) (= _12 __trust_opaque_ref_b5_s1_o0) (= _14 _12) (= _15 _14) (= _16 7) (= _17 (bv2nat (bvand ((_ int2bv 64) _15) ((_ int2bv 64) _16)))) (= _18 (= _17 0)) (= _41 _12) (= _42 _41) (= _43 (not (= 8 0))) (= _44 (= _42 0)) (= _45 (and _44 _43)) (= _46 (not _45)) (= __trust_sep__ptr__12.* 0)))))
(check-sat)
