# Why vivification starts at ternary clauses

The `clen < 3` gate in `tier.rs` is both a measured algorithmic boundary and a
soundness boundary. Do not lower it to two without first redesigning binary
propagation in vivification mode.

## Measurement

Binary-clause vivification was prototyped against the
`f6a085f3`/`6ff70a3a` post-factor, binary-dense residuals. On forced full
collapse it plateaued after several vivify/BVE rounds at roughly 2,886 and
1,454 eliminations respectively. Rounds four and five added nothing, so the
limit was structural rather than budget-driven. Fewer than two percent of the
binary clauses disappeared, neither target changed from `UNKNOWN`, and the
result remained far below kissat's roughly 104,496 eliminations.

Kissat also skips actual binary clauses during vivification. It reduces its
binary implication graph through transitive reduction, probing, and hyper
binary resolution. AY already has the corresponding sound transitive-reduction
and failed-literal-unit machinery, including LRAT production, in
`../transred.rs`.
The remaining blocker is BVE's structural ceiling
on the binary-dense extension-variable class: net-neutral resolutions are
rejected by the growth bound. That limitation is documented with the relevant
policy in `../../config_preprocess_policy.rs` (especially lines 124-136).

## Soundness

A naive length-gate change loses constraints. The inline binary-watch BCP paths
in `../../propagation_bcp.rs` and `../../propagation_bcp_unsafe.rs` do not honor
`is_vivify_skipped()`. If a binary candidate is probed unchanged, it can imply
its own literal, appear redundant, and be deleted. This is the same class of
failure caught by the final original-clause ledger after the husk-loss defect.

Any future binary-vivification experiment must first make both binary BCP paths
respect `is_vivify_skipped()` specifically in vivification mode, prove the LRAT
story, and then re-run the residual campaign. Until then, length three is the
minimum supported vivification candidate.
