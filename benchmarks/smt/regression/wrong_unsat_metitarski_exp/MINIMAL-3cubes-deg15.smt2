; MINIMAL REPRODUCER for the meti-tarski wrong-`unsat` (P0 #2), reduced 2026-07-31.
; AY answers `unsat`; z3 5.0.0 answers `sat`. Correct answer is SAT
; (e.g. skoX=3, skoC=3^(1/3), skoCM1=2^(1/3), skoCP1=4^(1/3) — all positive).
; TRIGGER = all THREE cube equations TOGETHER WITH the degree-15 monomial.
; Removing any one cube, or the deg-15 conjunct, removes the wrong verdict.
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun skoC () Real)(declare-fun skoCM1 () Real)
(declare-fun skoCP1 () Real)(declare-fun skoX () Real)
(assert (and (<= (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (- 2)))))))))))))))) 0)
  (= (* skoC (* skoC skoC)) skoX)
  (= (+ 1 (* skoCM1 (* skoCM1 skoCM1))) skoX)
  (= (+ (- 1) (* skoCP1 (* skoCP1 skoCP1))) skoX)
  (not (<= skoX 2)) (not (<= 10 skoX))
  (not (<= skoC 0)) (not (<= skoCM1 0)) (not (<= skoCP1 0))))
(check-sat)
