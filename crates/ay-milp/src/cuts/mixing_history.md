# Retired Günlük–Pochet mixing separators: measured dead end on `mik`

This file records retired experiments; it does not describe a production cut
family or device API. The type-I separator was hard-disabled after its only
firing class measured net-negative, and its root-loop wiring has since been
removed. The fixed `mixing` attribution index remains reserved so later
separator labels keep their historical indices; with no active separator it
emits no record. The `is_mixed_integer_knapsack` structural classifier also
remains, but only to schedule the active extended MIR-class rounds.

On 2026-07-21 the second Günlük–Pochet family was implemented soundly and
measured apples-to-apples as an experiment. Mapping
`t := S/δ >= z_i − μ_i` to the canonical set
(`s = t, r_i = −z_i, b_i = −μ_i, f_i = 1 − μ_i`) turns the wrap facet into an
extra `μ_[1](z_[1] − 1)` on the smallest-μ chain row. It reweights that row from
`μ_[2] − μ_[1]` to `μ_[2]`, adjusts the stored `>=` right-hand side by
`−δ μ_[1]`, and fits the same μ-sorted dynamic program through a different base
case. Four hundred random mixing sets passed brute-force soundness checks.

The type-II cuts separated about 28 times per root round at violation 0.004,
versus type-I's 0.17, but left the first-round root bound byte-identical at
`−29168.271847`. Enabling them regressed `mik`: separation doubled and fewer
nodes fit in the wall budget. Every `mik` knapsack row shares the same continuous
block, so both GP families act on the same aggregate mixing set. The remaining
dual gap is binary-knapsack cover structure inside `ρ_i(x)`, invisible to any
mixing/continuous family on aggregate `S`; future work should cut that binary
structure instead of re-deriving type II.
