; MODEL_CHECKER_CONSUMER-shaped non-prefix CFG transport canary.
;
; Provenance: minimized from the repository's loop-allocation MODEL_CHECKER_CONSUMER
; fixtures.  This version isolates the argument-flow requirement that a query
; anchor must travel backward through a permutation and then a projection:
;
;   loop(mem, count, tag) -> stage(tag, mem, count) -> check(count, mem)
;
; `tag` is deliberately absent from `check`; matching predicate signatures by
; a common positional prefix cannot carry the array invariant to `loop`.
;
; Expected: sat (safe).  Init establishes mem[0] = 0x2a and no rule mutates
; the array.
(set-logic HORN)

(declare-fun |loop| (
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
  (_ BitVec 8)
) Bool)

(declare-fun |stage| (
  (_ BitVec 8)
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
) Bool)

(declare-fun |check| (
  (_ BitVec 32)
  (Array (_ BitVec 64) (_ BitVec 8))
) Bool)

; Initialization also makes the bounded scalar support candidates inductive.
(assert
  (forall (
    (mem (Array (_ BitVec 64) (_ BitVec 8)))
    (count (_ BitVec 32))
    (tag (_ BitVec 8))
  )
    (=>
      (and
        (= mem
           (store
             ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)
             #x0000000000000000
             #x2A))
        (= count #x00000001)
        (= tag #x07)
      )
      (loop mem count tag)
    )
  )
)

; Pure variable permutation.
(assert
  (forall (
    (mem (Array (_ BitVec 64) (_ BitVec 8)))
    (count (_ BitVec 32))
    (tag (_ BitVec 8))
  )
    (=>
      (loop mem count tag)
      (stage tag mem count)
    )
  )
)

; Projection of the stage-only tag column.
(assert
  (forall (
    (mem (Array (_ BitVec 64) (_ BitVec 8)))
    (count (_ BitVec 32))
    (tag (_ BitVec 8))
  )
    (=>
      (stage tag mem count)
      (check count mem)
    )
  )
)

; The only query anchor is on the projected, reordered signature.
(assert
  (forall (
    (mem (Array (_ BitVec 64) (_ BitVec 8)))
    (count (_ BitVec 32))
  )
    (=>
      (and
        (check count mem)
        (or
          (= count #x00000000)
          (not
            (= (select mem #x0000000000000000) #x2A)))
      )
      false
    )
  )
)

(check-sat)
(exit)
