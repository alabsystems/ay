# ICP exact-grid fallback

The grid is a SAT-only fallback after interval branch-and-prune has returned
`Unknown`. It is deliberately isolated from contraction and certification so
its search heuristics cannot acquire refutation authority accidentally.

## Ordering contract

The first traversal is the established cheap search:

1. Order coordinates from narrowest interval to widest.
2. At each coordinate, try the simplest in-interval rational, then its
   midpoint, then the cumulative fixed dyadic alphabet.
3. If that list is too short, append interval-relative dyadic points.
4. Pin one point, contract the box, and recurse.

Candidate order is observable through budgets: moving a point earlier can
change which prefixes are visited before exhaustion. The extraction therefore
keeps this order exactly. Interval-relative points are appended, never
interleaved with established candidates.

Only when the first traversal finds no model does the second traversal run. It
uses a separate solve-wide budget and revisits prefixes to solve the last free
coordinate as an exact univariate problem. It does not re-enumerate that
coordinate. A run of proven-empty prefixes disables the second traversal early;
an undecided prefix neither resets that streak nor authorizes pruning.

## Soundness boundary

- Rational assignments are accepted only after exact substitution into every
  asserted atom.
- Algebraic last coordinates are accepted only after exact Sturm-sign checks
  against every residual constraint.
- A contracted child may be skipped only when interval arithmetic proves that
  child infeasible.
- An exact `Empty` result rejects one fully pinned prefix only. It never proves
  the parent box or the original problem infeasible.
- Exhausted budgets and unsupported residuals return `None`.

Consequently this subsystem has no `Unsat` return path. The parent ICP search
owns all refutation authority through the typed `SearchAuthority` state.

## Budget rationale

Five candidates per poorly reached coordinate keeps the worst six-variable
product within the 20,000-node per-call cap. Larger widths were measured at 9
and 13 candidates without solving additional residual files, while increasing
wall time. The interval-relative generator is O(candidate count), including on
very wide intervals; it must never materialize every integer or dyadic multiple
between the endpoints.

Exact last-coordinate decisions are much more expensive than contraction, so
they are charged 64 node units each, capped separately, and stopped after eight
consecutive proven-empty prefixes. These limits protect the successful cheap
traversal from a later exact fallback.

The `ay-nra-oracle` crate exercises polynomial and algebraic primitives, not
`NraSolver` search state or these budgets. Its differential tests are useful
for the exact univariate operations underneath this module, but the ICP grid
tests and DPLL soundness canaries remain the verification surface for traversal
ordering and authority.

## Diagnostic contract

ICP diagnostics are carried by `ay_core::misc_cli_flags()` and are strictly
observational. `--nra-diag` emits the decision and grid trace;
`--nra-witness ASSIGNMENTS` supplies inline rational assignments such as
`x=1/2,y=-3`; and `--nra-grid-probe` compares one scoped grid traversal with
that supplied assignment. A probe is owned by one `dyadic_grid_search` call and
borrowed by its DFS. It is not thread-local and none of its methods returns a
value consumed by search.

Trace order is part of the diagnostic interface. Root processing reports atom
normalization, gates, the contracted root, dense-inequality decline, and the
tree result in decision order. Grid processing reports its cap and entry,
resets the probe before each level, reports pass 2 and exit, then prints the
probe summary. DFS records collapsed pins, candidates, starvation, picks, and
contracted refutations at the exact point each event occurs. Exact solving
reports entry, declines, witnesses, and the empty-streak cut without changing
the associated result.

The CLI carrier uses `ASSIGNMENTS` as the value name and documents the input as
an inline known-rational list (`name=p/q,...`). The parsed diagnostic values are
propagated directly into `MiscCliFlags`; there is no environment round-trip.
