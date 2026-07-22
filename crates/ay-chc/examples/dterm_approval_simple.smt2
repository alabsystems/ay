; Simplified CHC Translation of dterm INV-APPROVAL-2
;
; This version tracks a single request's state through its lifecycle.
; The invariant is: if request is terminal, then audit entry exists.
;
; Using integers instead of arrays to make verification feasible.

(set-logic HORN)

;; State of single tracked request:
;; req_state: 0=absent, 1=pending, 2=terminal
;; has_audit: 0=no audit, 1=has audit
(declare-fun inv (Int Int) Bool)

;; Initial state: no request, no audit
(assert (forall ((req Int) (audit Int))
    (=> (and (= req 0) (= audit 0))
        (inv req audit))))

;; Transition: create pending request (no audit)
(assert (forall ((req Int) (audit Int) (req2 Int) (audit2 Int))
    (=> (and (inv req audit)
             (= req 0)          ;; No request exists
             (= req2 1)         ;; Now pending
             (= audit2 audit))  ;; No audit entry yet
        (inv req2 audit2))))

;; Transition: complete request (pending → terminal + add audit)
(assert (forall ((req Int) (audit Int) (req2 Int) (audit2 Int))
    (=> (and (inv req audit)
             (= req 1)          ;; Request is pending
             (= req2 2)         ;; Now terminal
             (= audit2 1))      ;; Add audit entry (KEY INVARIANT MAINTENANCE)
        (inv req2 audit2))))

;; Query: Is there a terminal request without audit entry?
(assert (forall ((req Int) (audit Int))
    (=> (and (inv req audit)
             (= req 2)          ;; Terminal
             (= audit 0))       ;; No audit
        false)))

(check-sat)
