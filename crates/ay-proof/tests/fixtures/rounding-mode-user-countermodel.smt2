; Registered user identities do not inherit builtin meanings from spelling.
; These are the countermodels for the raw namespace-collision regressions:
; a user mode can equal RNA, and user Boolean functions may choose these values.
(set-logic ALL)
(set-info :status sat)
(declare-const user_mode RoundingMode)
(declare-fun user_equal (RoundingMode RoundingMode) Bool)
(declare-fun user_and (Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun user_or (Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
(assert (= user_mode RNA))
(assert (user_equal RNE RNA))
(assert (not (user_and true true true true true true true true true true)))
(assert (user_or false false false false false false false false false false))
(check-sat)
