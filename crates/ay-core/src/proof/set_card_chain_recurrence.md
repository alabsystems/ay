<!--
Copyright 2026 Andrew Yates
Author: Andrew Yates
Licensed under the Apache License, Version 2.0
-->

The definitional set-cardinality recurrence over a store chain rooted
at the SYNTACTIC empty set -- the elaborated form of
`set.singleton` / `set.insert` / `set.remove`.

```text
(= (set.card R) 0)                                   R syntactically empty
(= (set.card (store B e true))  (+ (set.card B) 1))  e not in B
(= (set.card (store B e true))  (set.card B))        e in B
(= (set.card (store B e false)) (set.card B))        e not in B
(= (set.card (store B e false)) (- (set.card B) 1))  e in B
```

THE EMPTY ROOT IS LOAD-BEARING, not incidental. A finite chain of writes
over the empty carrier denotes a FINITE set, and the recurrence is a
theorem of finite set theory. Over an unrestricted base it is not safe
to hand out: under the interpretation `card(X) = |X|` for finite `X` and
`card(X) = N` for infinite `X` (`N` above every literal-membership count
in the problem) -- which satisfies [`Self::SetCardNonNegative`],
[`Self::SetCardMemberLowerBound`], [`Self::SetCardEmpty`] and the
finite-chain recurrence alike -- an increment over the universal set
reads `N = N + 1`. Requiring the empty root keeps every instance inside
the fragment where the equations are simply true. AY's own producer
imposes the identical restriction (`is_covered_store_chain`).

AY's strict checker establishes the empty root with a walk of its OWN,
separate from the one that decides the membership side condition: the
membership walk stops at the first write on the probed index and can
answer without ever reaching the root, so it cannot be what confines the
schema to the finite fragment.

The membership side condition is likewise re-derived rather than taken
on the producer's word. That walk steps past a write only when the two
indices are syntactically identical or DISTINCT LITERAL constants. Two
symbolic indices may denote the same element, so an undecidable chain is
rejected fail-closed rather than guessed -- the difference between
refusing to certify `|{x, y}| = 2` and asserting it (false when
`x = y`).

Either orientation of the equality is accepted; `=` is symmetric, so
the two spellings are the same claim.

Checkable only by AY's native strict checker; the pinned external
Alethe checker has no rule for the non-standard `set.card` operator.
