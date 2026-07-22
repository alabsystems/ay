; QF_ABV: model-checker-consumer-style pattern — pointer arithmetic with multiplication
; Simulates: array[base + i*stride] where stride is a variable
; This is the pattern model-checker-consumer emits for struct field access with variable offset
(set-logic QF_ABV)
(declare-fun mem () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun base () (_ BitVec 32))
(declare-fun i () (_ BitVec 32))
(declare-fun stride () (_ BitVec 32))
(declare-fun val () (_ BitVec 32))

; Address = base + i * stride (32-bit variable*variable mul)
(declare-fun addr () (_ BitVec 32))
(assert (= addr (bvadd base (bvmul i stride))))

; Write val to computed address
(declare-fun mem2 () (Array (_ BitVec 32) (_ BitVec 32)))
(assert (= mem2 (store mem addr val)))

; Read back must equal val
(assert (= (select mem2 addr) val))

; Constraints
(assert (= base #x10000000))
(assert (bvugt stride #x00000004))
(assert (bvult stride #x00000100))
(assert (bvult i #x00000100))
(assert (= val #xDEADBEEF))

; Another access at different index must differ
(declare-fun j () (_ BitVec 32))
(assert (not (= i j)))
(assert (bvult j #x00000100))
(declare-fun addr2 () (_ BitVec 32))
(assert (= addr2 (bvadd base (bvmul j stride))))

; If stride > 0 and i != j, addresses should differ
; (this requires reasoning about multiplication)
(assert (not (= addr addr2)))

(check-sat)
(exit)
