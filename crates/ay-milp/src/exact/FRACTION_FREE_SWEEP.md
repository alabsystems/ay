# Fraction-free switch sweep (2026-08-20)

The class is fifteen, not three. Over 46 distinct matrices (14 MILP corpus,
15 witness, and 38 oracle LP relaxations, with 21 repeated matrices), the
switch fires on `blend2`, `mas74`, `mas76`, `pk1`, `harp2`, and all ten
`domset_mw19_*` relaxations. `pk1` (switch at pivot 688) was independently
confirmed at 2.45× on interleaved repetitions.

There is no cheap static predictor. Density crosses the boundary (`mas76` is
90.5% dense and converts; hexgrid is 0.25% and does not), as do matrix
integrality, row count, and λ.

At least nine members of the reduced class would be 1.5×–24.6× faster if they
converted: `air03` 24.60×, `l152lav` 11.66×, `air05` 10.48×, `mod010` 10.32×,
`enigma` 6.50×, `mod008` 3.49×, `misc07` 2.74×, `misc03` 2.14×, and `p0201`
1.50×. Every result was bit-identical at identical pivot counts. Forced
conversion instead costs 3×–7× on `dcmulti`, `gt2`, `lseu`, `p0282`, `p0548`,
`p2756`, `qnet1`, and `qiu`.

## Refuted `Δ·c` trigger (2026-08-21)

The earlier claim that fraction-free inline share separated all measured
models was a whole-solve statistic, while a switch must decide from a prefix.
The implemented trigger failed on both sides:

- `dcmulti`, a 4.9× loser, opens with 29 consecutive 100%-inline windows;
  `khb05250` has 27 and `qnet1` has 9. `enigma` finishes in only 11 windows,
  so no sustain count admits the winners while excluding the losers.
- `mod008`, a measured 3.49× winner, is fraction-free-cold from its second
  window (100%, then 74%, then 3%).
- Determinant width also overlaps: `dcmulti` spans 1–27 bits, inside
  `misc03`'s 14–22 and `p0201`'s 13–19.

The trigger missed the acceptance table (8/9 must-fire and 6/9
must-not-fire) and added a `gen` regression, so it did not ship. Future
classifiers must validate on a held-out prefix, never a whole-solve aggregate.
A safer opportunity is timing an already-licensed conversion: `pk1` and
`blend2` convert late (pivots 688 and 592), while moving `pk1` to pivot 32
reduced 2.57 seconds to 0.317 seconds at identical pivot counts.

## Rim prerequisite and gate coverage

The faster rim converts none of five unsolved hexgrid covering members. At a
900-second rim-only budget, even `ncols_160` finishes in neither
representation: 51,861 reduced pivots versus 87,736 fraction-free, despite
the float lane closing it in 0.594 seconds. The oracle covering leg is 12/17
at 60 seconds and 13/17 at 180 seconds in both arms.

The rim was entered once across 1.36 million MILP nodes, and the LP route is
float-first (`mas76_lprelax`: 0.037 seconds float versus 1.241 seconds rim).
The 19-instance node gate and `corpus_guard` therefore do not exercise this
path: both can pass changes that cost 4.9× on `dcmulti`, 3.9× on `gen`,
3.45× on `qnet1`, and 2.24× on `khb05250`. Changes under `exact::` require
their own pinned evidence.
