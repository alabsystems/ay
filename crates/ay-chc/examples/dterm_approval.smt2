; CHC Translation of dterm INV-APPROVAL-2
;
; Invariant: ∀ req ∈ requests: req.state.is_terminal() ⟹ ∃ entry ∈ audit_log: entry.request_id == req.id
;
; Models a request/approval state machine with an audit-log invariant.

(set-logic HORN)

;; State: (requests: Array[Id → State], audit: Set[Id], audit_count: Int)
;; State values: 0=absent/pending, 1=terminal
(declare-fun inv ((Array Int Int) (Array Int Bool) Int) Bool)

;; Initial state: empty
(assert (forall ((reqs (Array Int Int)) (audit (Array Int Bool)) (count Int))
    (=> (and (= reqs ((as const (Array Int Int)) 0))
             (= audit ((as const (Array Int Bool)) false))
             (= count 0))
        (inv reqs audit count))))

;; Transition: complete request (no eviction case)
(assert (forall ((reqs (Array Int Int)) (audit (Array Int Bool)) (count Int)
                 (reqs2 (Array Int Int)) (audit2 (Array Int Bool)) (count2 Int)
                 (req_id Int) (max_audit Int))
    (=> (and (inv reqs audit count)
             (< count max_audit)  ;; No eviction needed
             (= (select reqs req_id) 0)  ;; Request exists as pending
             (= reqs2 (store reqs req_id 1))  ;; Mark terminal
             (= audit2 (store audit req_id true))  ;; Add audit
             (= count2 (+ count 1)))
        (inv reqs2 audit2 count2))))

;; Transition: complete request WITH eviction
(assert (forall ((reqs (Array Int Int)) (audit (Array Int Bool)) (count Int)
                 (reqs2 (Array Int Int)) (audit2 (Array Int Bool)) (count2 Int)
                 (req_id Int) (evict_id Int) (max_audit Int))
    (=> (and (inv reqs audit count)
             (>= count max_audit)  ;; Eviction needed
             (select audit evict_id)  ;; evict_id has audit entry
             (= (select reqs evict_id) 1)  ;; evict_id is terminal
             ;; Remove evicted
             (= reqs2 (store (store reqs req_id 1) evict_id 0))
             (= audit2 (store (store audit req_id true) evict_id false))
             (= count2 count))  ;; Net count unchanged
        (inv reqs2 audit2 count2))))

;; Query: Is there a terminal request without audit entry?
(assert (forall ((reqs (Array Int Int)) (audit (Array Int Bool)) (count Int)
                 (req_id Int))
    (=> (and (inv reqs audit count)
             (= (select reqs req_id) 1)  ;; Terminal
             (not (select audit req_id)))  ;; No audit
        false)))

(check-sat)
