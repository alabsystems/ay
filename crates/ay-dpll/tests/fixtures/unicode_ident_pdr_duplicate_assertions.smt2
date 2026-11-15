; AY-03 regression fixture: a QF_BV query that ay's proof-grade PDR hands its
; SMT executor, from a real compiler_consumer obligation.
;
; Source: compiler_consumer 321aaeda7 (ay 075a482ae) verifying unicode-ident-1.0.24
; `is_xid_start` logged `internal proof checker rejected UNSAT proof,
; error=step t48 has invalid resolution derivation` (95-step proof). The
; obligation (model-checker-consumer request-1-proof-1) was captured with MODEL_CHECKER_CONSUMER_DUMP_CHC,
; rewritten as HORN, and re-run through `engines::solve_pdr_proof` built from
; ay 075a482ae. That run rejected a 95-step proof with the same error at t50,
; and its 47 `assume` steps are the assertions below, in the same order, with
; the 128-bit literals rewritten from #b binary to (_ bvN 128) decimal.
;
; 47 assertions, 45 distinct: `(bvule 0 ch)` and `(bvule ch 4294967295)` are
; each asserted twice. The BV bit-blast collapse rescue turned that repetition
; into an invalid resolution chain before ca0dd42ad.
;
; UNSAT by hand: the last assertion needs (bvmul 64 _23) >u 2^64-1 or
; (bvmul 64 _23) <u 0. The second is impossible, and _23 <=u 255 bounds the
; product by 16320 with no 128-bit wrap, so the first is false too.
(set-option :produce-proofs true)
(set-logic QF_BV)
(declare-fun _21 () (_ BitVec 128))
(declare-fun _23 () (_ BitVec 128))
(declare-fun _26 () (_ BitVec 128))
(declare-fun _27 () (_ BitVec 128))
(declare-fun _28 () (_ BitVec 128))
(declare-fun _32 () (_ BitVec 128))
(declare-fun _39 () (_ BitVec 128))
(declare-fun ch () (_ BitVec 128))
(declare-fun chunk () (_ BitVec 128))
(declare-fun _22 () (_ BitVec 128))
(declare-fun |_24.0#s8_2| () (_ BitVec 128))
(declare-fun |_3*#s0_0| () (_ BitVec 128))
(declare-fun |_9*#s7_t| () (_ BitVec 128))
(declare-fun _17 () Bool)
(declare-fun _18 () Bool)
(declare-fun offset () (_ BitVec 128))
(assert (bvule (_ bv0 128) (bvlshr (bvlshr ch (_ bv3 128)) (_ bv6 128))))
(assert (bvule (_ bv0 128) (bvlshr ch (_ bv3 128))))
(assert (bvule (_ bv0 128) ch))
(assert (bvule (_ bv0 128) _21))
(assert (bvule (_ bv0 128) _23))
(assert (bvule (_ bv0 128) _26))
(assert (bvule (_ bv0 128) _27))
(assert (bvule (_ bv0 128) _28))
(assert (bvule (_ bv0 128) _32))
(assert (bvule (_ bv0 128) _39))
(assert (bvule (_ bv0 128) ch))
(assert (bvule (_ bv0 128) chunk))
(assert (bvule (bvlshr (bvlshr ch (_ bv3 128)) (_ bv6 128)) (_ bv18446744073709551615 128)))
(assert (bvule (bvlshr (bvlshr ch (_ bv3 128)) (_ bv6 128)) (_ bv8388607 128)))
(assert (bvule (bvlshr (bvlshr ch (_ bv3 128)) (_ bv6 128)) (bvlshr ch (_ bv3 128))))
(assert (bvule (bvlshr ch (_ bv3 128)) (_ bv18446744073709551615 128)))
(assert (bvule (bvlshr ch (_ bv3 128)) (_ bv536870911 128)))
(assert (bvule (bvlshr ch (_ bv3 128)) ch))
(assert (bvule ch (_ bv18446744073709551615 128)))
(assert (bvule ch (_ bv4294967295 128)))
(assert (bvule _21 (_ bv18446744073709551615 128)))
(assert (bvule _21 (_ bv8160 128)))
(assert (bvule _22 (_ bv16320 128)))
(assert (bvule _23 (_ bv18446744073709551615 128)))
(assert (bvule _23 (_ bv255 128)))
(assert (bvule |_24.0#s8_2| (_ bv16320 128)))
(assert (bvule _26 (_ bv18446744073709551615 128)))
(assert (bvule _27 (_ bv18446744073709551615 128)))
(assert (bvule _27 (_ bv536870911 128)))
(assert (bvule _28 (_ bv18446744073709551615 128)))
(assert (bvule _28 (_ bv4294967295 128)))
(assert (bvule _32 (_ bv1 128)))
(assert (bvule _32 (_ bv255 128)))
(assert (bvule _39 (_ bv4294967295 128)))
(assert (bvule ch (_ bv1114111 128)))
(assert (bvule ch (_ bv4294967295 128)))
(assert (bvule chunk (_ bv255 128)))
(assert (bvult _26 (_ bv64 128)))
(assert (bvult _39 (_ bv8 128)))
(assert (= _23 chunk))
(assert (= |_3*#s0_0| ch))
(assert (= |_9*#s7_t| chunk))
(assert (not (and (bvule (_ bv55296 128) ch) (bvule ch (_ bv57343 128)))))
(assert (not _17))
(assert (not _18))
(assert (or (bvult (_ bv18446744073709551615 128) (bvadd _21 _26)) (= (bvadd _21 _26) offset)))
(assert (or (bvult (_ bv18446744073709551615 128) (bvmul (_ bv64 128) _23)) (bvult (bvmul (_ bv64 128) _23) (_ bv0 128))))
(check-sat)
