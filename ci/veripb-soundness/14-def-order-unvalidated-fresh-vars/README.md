# 14 — `def_order` never validates its fresh-variable lists (FIXED in the fork)

A relation whose strict part contains a **cycle** installs as a "preorder", and dominance
then rests on a descent argument that does not exist.

|                                |                                                                     |
| ------------------------------ | ------------------------------------------------------------------- |
| formula                        | `order.opb` — three ordinary clauses over `x1..x4`                  |
| proof                          | `order.pbp` (one `def_order`, one `load_order`, one `dom`)          |
| **unfixed verdict**            | `s VERIFIED UNSATISFIABLE`, exit 0, with default flags               |
| **truth**                      | **SATISFIABLE** — `x1=0 x2=0 x3=1 x4=0` is a model                  |
| present in stock upstream `4bb10c2c` | yes                                                                 |
| present with `0001` only       | **yes**                                                             |
| present with the pinned patch | no — rejected, no `s` line                                          |

## The bug

Transitivity is `x ⪰ y ∧ y ⪰ z → x ⪰ z` over three **independent** tuples. The order
definition supplies `x` (the `left` variables) and `y` (the `right` variables); `z` has to
come from the `fresh_right` list of the `transitivity` block, and each of the three instances
of the relation needs its own copy of the auxiliary variables (`fresh_aux_1`, `fresh_aux_2`).

`OrderFreshRightVariablesRule::compute`
(`veripb-checker/src/rules/order_fresh_right_vars.rs`) stored the declared list **verbatim**:

```rust
transitivity_context.fresh_right = self.vars.clone();
```

No length check, no distinctness check, no freshness check. `OrderContext::get_transitivity_substitution`
(`veripb-checker/src/order_context.rs`) then built both substitutions with

```rust
for (&left, &right, &fresh) in izip!(left_vars.iter(), right_vars.iter(), fresh_right.iter())
```

and `izip!` **stops at the shortest iterator**. `fresh_right ;` — an empty list — is
grammatically legal (VeriPB's `grammar.tex`: the list is optional), so both substitutions came
out **empty** and each transitivity proofgoal `D_i|x→z` was literally `D_i`, which
`order_proof.rs` has already pushed as a premise. An empty `proof … qed;` discharged all of
them by database lookup, `end_subproof.rs` set `transitivity_proven`, and the relation
entered `context.orders` where `load_order`/`dom` use it as a preorder.

Declaring the **right** variables again (`fresh_right v1 v2 ;`) has the correct arity and does
the same thing through the identity substitution, which is why a length check alone is not
enough.

The `def` block below encodes a 4-cycle, so `dom`'s descent argument is vacuous and a
satisfiable formula is reported UNSAT.

## Evidence chain

```
def_order bogus
    vars  left u1 u2; right v1 v2; aux; end;
    def
        1 u1 1 u2 1 v1 1 ~v2 >= 1;      % the four rows encode a CYCLE in the strict part
        1 u1 1 ~u2 1 ~v1 1 ~v2 >= 1;
        1 ~u1 1 ~u2 1 ~v1 1 v2 >= 1;
        1 ~u1 1 u2 1 v1 1 v2 >= 1;
    end;
    transitivity
        vars fresh_right ; end;          % <- empty; both substitutions collapse
        proof qed; end;                  % <- empty proof, every goal is its own premise
    end;
end;
load_order bogus x1 x2;
dom >= 1 : x1 -> x2 x2 -> ~x1 : subproof … qed;
conclusion UNSAT : -1;
```

## The pair that needs no external oracle

`sat.pbp` is the same formula and the same binary with a logged model, answering
`s VERIFIED SATISFIABLE`, exit 0.

```bash
veripb --opb order.opb order.pbp   # rejected (unfixed: s VERIFIED UNSATISFIABLE)
veripb --opb order.opb sat.pbp     # s VERIFIED SATISFIABLE, before and after
```

## `variants/`

| variant | knob | unfixed | fixed |
| --- | --- | --- | --- |
| `alias-right-vars/alias.pbp` | `fresh_right v1 v2 ;` — right arity, but the "fresh" variables are the `right` variables | `VERIFIED UNSATISFIABLE` | rejected |
| `freshvars-control/control.pbp` | **one knob**: `fresh_right w1 w2 ;`, two genuinely fresh variables, nothing else changed | rejected | rejected |
| `freshvars-control/control-short-by-one.pbp` | the middle of the arity sweep: `fresh_right w1 ;` for a two-variable order | rejected | rejected |
| `missing-fresh-aux/order-input.pbp` | the same truncation on the **second** `izip!`: an order that declares `aux $z` but no `fresh_aux_1`/`fresh_aux_2`, so all three instances shared `$z` | `VERIFIED NO CONCLUSION` (the bogus order installed) | rejected |
| `valid-order/valid.pbp` | **not a forgery**: a real order with correct `fresh_right`, `fresh_aux_1`, `fresh_aux_2` | `VERIFIED NO CONCLUSION` | `VERIFIED NO CONCLUSION` |

`freshvars-control/` is the causation argument: with real fresh variables the transitivity
proofgoals are the real ones, the empty proof no longer discharges them, and the **unfixed**
checker refuses the identical proof. So the forgery is the unvalidated list, not the bogus
`def` rows and not `dom` in general.

`valid-order/` is the over-fixing guard. A validation that refused `def_order` blocks
outright, or demanded lists the format does not require, would satisfy every negative case
above and break every dominance-based proof AY emits.

`missing-fresh-aux/` is honest about its status: it is the identical truncation in the
identical function, and validating one of the three lists while leaving the other two
unchecked would be arbitrary — but **no wrong-verdict witness riding on the shared auxiliary
variable was constructed**. Its "unfixed" column is a bogus order installing, not a forged
verdict. The two demonstrated wrong-verdict routes are `order.pbp` and `alias.pbp`.

## The fix (now in the fork; formerly ay patch `0002`)

`OrderContext::check_transitivity_variables` runs before either substitution is built and
requires:

* `fresh_right.len() == left_vars.len()` and `fresh_aux_{1,2}.len() == aux_vars.len()`, so
  the `izip!`s cannot silently truncate (`debug_assert_eq!`s restate the coupling);
* every entry pairwise distinct across all three lists;
* no entry aliasing a `left`, `right` or `aux` variable of the order —
  `Order::is_order_variable()` already answers that from the table `left`/`right`/`aux`
  populate.

`get_transitivity_substitution` returns `Result` and `order_proof.rs` propagates the error,
so the `transitivity` block is *rejected* rather than trivially proved.

The instance pairs `tests/instances/incorrect/version3/def_order_empty_fresh_right.*`,
`.../def_order_fresh_right_aliases_right_vars.*`, `.../def_order_missing_fresh_aux.*` and the
positive `tests/instances/correct/version3/def_order_transitivity_fresh_vars_valid.*` ride in
the patch.
