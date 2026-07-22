# opt-epsilon fixtures (#opt-epsilon)

Probe battery for Real optimization with strict inequalities (delta-rational
objective simplex; unattained optima print z3's `epsilon` grammar).

Comparison baseline updated to z3 5.0.0 on 2026-07-20 (was z3 4.15.4).

Each `<name>.smt2` has a `<name>.z3.expected` beside it: the byte-exact stdout
of **z3 5.0.0** (regenerated 2026-07-20) on that probe. The classification of
every probe — byte parity, cosmetic
divergence, or documented deviation — lives in `../opt_epsilon.rs`, which is
the enforcing test. The deviation-classed random differential loop against z3
lives in `../opt_epsilon_differential.rs`.

z3 5.0.0 FIXED three optimization defects that 4.15.4 got wrong. For the two
that show up here — box-mode strict bounds (`m5`/`m8`) and lex successor
abandonment (`g5`/`adv7`) — AY now AGREES with z3 5.0.0 (or fail-closes sound;
see below), where it previously deviated as more-correct from 4.15.4.

Parity now (z3 5.0.0 defect-fixes):

* `m5`/`m8` — 4.15.4's box mode with any strict bound reported demonstrably
  false optima (`(x 1)` for `0 < x < 3` maximize; bogus `(y oo)`); z3 5.0.0
  now prints the correct independent optima (`(x 3 - ε)` + `(y 5)`), which AY
  already produced — so AY AGREES with z3 5.0.0 (cosmetic `5.0` vs `5` aside).

AY sound-but-incomplete (z3 5.0.0 is now more complete):

* `g5`/`adv7` — 4.15.4's lex mode with an unattained/unbounded non-final
  objective emitted a false successor scalar (`(y (- 1))` where max y = 5);
  z3 5.0.0 now decides the suffix correctly (`(y 5)` / `(y oo)`). AY
  conservatively marks the suffix unavailable (fail-closed, never a wrong
  scalar).

Documented deviations (AY is deliberately NOT byte-identical to z3 there):

* `adv3` — z3 5.0.0 STILL prints `(x epsilon)` for `x <= i (Int), i <= 2.5,
  maximize x` where the true optimum 2 is ATTAINED (`x = i = 2`). One of the
  two defects 5.0.0 did not fix; AY prints the attained value `(x 2.0)`.
* `adv8` — after `unsat`, z3 5.0.0 still prints an oo-interval "objective
  value"; AY errors honestly.
* `m15b` — AY's Int guard fails closed (`unknown`) on `x < i (Int)` upper
  coupling; z3's `5 - ε` happens to be right there, but the LP relaxation is
  not a proof near Int terms (see `adv3` for the same shape where z3 gets it
  wrong). Residual conservatism, documented.

Regenerate a z3 reference with:
`z3-5.0.0 <name>.smt2 > <name>.z3.expected` (or `z3`, now 5.0.0 on PATH).
