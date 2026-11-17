# 15 — an order's auxiliary variables are not order-private (FIXED in the fork)

Four proof lines forge `s VERIFIED UNSATISFIABLE` for an **arbitrary satisfiable formula**.
No arithmetic, no extreme number, nothing needed from the formula at all.

|                                |                                                                          |
| ------------------------------ | ------------------------------------------------------------------------ |
| formula                        | `order.opb` — four ordinary clauses over `x1..x5`, **13 models**         |
| proof                          | `order.pbp` (one `def_order`, one `load_order`, one `red`, one `dom`)   |
| **unfixed verdict**            | `s VERIFIED UNSATISFIABLE`, exit 0, with default flags                    |
| **truth**                      | **SATISFIABLE** — e.g. `x1=0 x2=1 x3=0 x4=0 x5=0`; 13 models by exhaustive enumeration |
| present in stock upstream `4bb10c2c` | yes                                                                      |
| present with `0001` only       | **yes**                                                                  |
| present with the pinned patch | no — rejected, no `s` line                                               |

## The bug

An order's `aux` variables are **existentially quantified by the order's specification**.
`def_order o … aux $a1 … spec red +1 ~$a1 >= 1 : $a1 -> 0; …` says "`$a1` is a variable
whose meaning is fixed by these constraints". They mean something inside the `def_order`
block, and inside a `scope`, where `ScopeRule::compute`
(`veripb-checker/src/rules/scope.rs`) injects that specification as **unconditional
premises**:

```rust
let premises = if let Some(active_order) = &mut context.active_order {
    match self.id {
        ScopeId::LessEqual    => active_order.get_specification_less_equal(&witness),
        ScopeId::GreaterEqual => active_order.get_specification_greater_equal(&witness),
    }
} else { vec![] };
```

They mean **nothing** anywhere else. But they live in the *global* variable namespace, and
the only thing standing between them and the rest of the proof was
`ForwardsChecker::validate_aux_var` (`veripb-checker/src/checker.rs`):

```rust
if !active_order.is_none_or(|order| order.order.is_auxiliary_variable(var_id)) {
    return Err(CheckingError::InvalidAuxVar);
}
```

That is exactly backwards, twice over:

* `is_none_or` — with **no order active** the predicate is vacuously true, so every
  variable is admitted. Naming `$a1` *before* `load_order` was a total no-op.
* with an order active it admits **precisely that order's auxiliary variables** — the
  variables that must not be assertable outside it.

So a top-level

```
red +1 $a1 >= 1 : $a1 -> 1;
```

asserts `$a1` TRUE **for free**: under the witness `$a1 -> 1` the constraint itself is
trivially satisfied, and the order proofgoal is reported optional. The order's
specification says `~$a1`. The next `scope leq` or `scope geq` in any `dom` or `red`
subproof therefore injects a premise that contradicts a live top-level constraint, the
database is contradictory *inside every scope proofgoal*, one `rup >= 1;` discharges them
all, and `qed` publishes the empty contradiction at the top level.

## Evidence chain

```
f 4;                                     % four ordinary clauses over x1..x5 (13 models)
def_order triv
  vars left u1; right v1; aux $a1; end vars;
  spec red +1 ~$a1 >= 1 : $a1 -> 0; end spec;      % the order says  ~$a1
  def  +1 ~u1 +1 v1 >= 1;             end def;
  transitivity … end transitivity;
end def_order;
load_order triv x1;
red +1 $a1 >= 1 : $a1 -> 1;              % <- the whole forgery: the proof says  $a1
dom >= 1 : y1 -> 0 : subproof
  scope geq                              % <- injects  ~$a1  next to the live  $a1
    proofgoal #2  rup >= 1;  qed #2 : -1;
  end scope;
qed dom;
conclusion UNSAT;
```

## The pair that needs no external oracle

`sat.pbp` is the same formula and the same binary with a logged model, answering
`s VERIFIED SATISFIABLE`, exit 0, before and after.

```bash
veripb --opb order.opb order.pbp   # rejected (unfixed: s VERIFIED UNSATISFIABLE)
veripb --opb order.opb sat.pbp     # s VERIFIED SATISFIABLE, before and after
```

## `variants/`

| variant | reach path / knob | unfixed | fixed |
| --- | --- | --- | --- |
| `dom-route/order-input.pbp` | the same forgery on a one-clause formula, through `dom` | `VERIFIED UNSATISFIABLE` | rejected |
| `red-route/order-input.pbp` | through `red … : subproof / scope leq`, no `dom` anywhere | `VERIFIED UNSATISFIABLE` | rejected |
| `before-load-order/order-input.pbp` | the top-level `red` moved **before** `load_order`, where `validate_aux_var` was a total no-op | `VERIFIED UNSATISFIABLE` | rejected |
| `version2-ordinary-identifier/v2.pbp` | the same top-level assertion in **version 2.0**, where auxiliary variables are spelled as ordinary identifiers and the `$` check never runs | `VERIFIED NO CONCLUSION` (the constraint is accepted) | rejected |
| `controls/A_no_toplevel_aux_red.pbp` | **one knob**: drop the top-level `red`, keep the order, the `dom` and the `scope` | rejected | rejected |
| `controls/B_ordinary_var.pbp` | **one knob**: assert an ordinary variable `z1` instead of `$a1` | rejected | rejected |
| `controls/C_spec_agrees.pbp` | **one knob**: the order's spec asserts `$a1` too, so the injected premise agrees instead of contradicting | rejected | rejected |
| `controls/D_no_scope.pbp` | **one knob**: the `dom` subproof with the `scope` block removed, so nothing is injected | rejected | rejected |
| `controls/E_red_route_no_toplevel_aux_red.pbp` | the same knob as A, on the `red` route | rejected | rejected |
| `aux-vars-in-scope-valid/valid.pbp` | **POSITIVE**: VeriPB's own `dominance_with_aux_vars` proof, which names `$a1..$a9` and `$d1..$d10` **inside** two `scope` blocks, with a real `conclusion UNSAT` appended | `VERIFIED UNSATISFIABLE` | `VERIFIED UNSATISFIABLE` |

`controls/` is the causation argument. Each removes exactly one feature and the **unfixed**
checker refuses the result, so the forgery is the top-level assertion of an order-private
variable — not `dom`, not `scope`, not orders in general, and not "asserting something with
a witness".

`aux-vars-in-scope-valid/` is the over-fixing guard, and it is not a toy: it is upstream's
own lexicographic-order dominance proof, 330 lines, with 19 auxiliary variables used
throughout both scopes. A "fix" that refused the `$` namespace, or refused it once an order
was loaded, would pass every negative case above and break every dominance proof that uses
an encoded order.

`version2-ordinary-identifier/` is honest about its status. It reaches the same illegitimate
**state** — a top-level database constraint over a variable that is local to an order — and
the unfixed checker accepts it. It is **not** a wrong-verdict witness: version 2.0 has no
`scope` rule at all (`grep -n scope` in `veripb-parser/src/pbp_parser/legacy_v2/parser.rs`
returns nothing, which is defect 15 next door), so there is no specification-injection
surface to cash the state in on. It is here because the fix has to close the reach path in
both formats and a `$`-only check would not.

## The fix (now in the fork; formerly ay patch `0002`)

Two independent guards, because the two parsers reach the variable by different routes:

1. **Naming.** `validate_aux_var` becomes `validate_variable_use`
   (`veripb-checker/src/checker.rs`) and is called for *every* variable occurrence, not
   only `$`-spelled ones. A variable that is an auxiliary variable of any defined order —
   tracked in `Context::order_aux_vars`, populated by `aux`, `fresh_aux_1` and
   `fresh_aux_2` — may only be named where `Context::in_order_local_scope()` holds: inside
   a `def_order` block (any of `Order`, `Transitivity`, `Reflexivity`, `Specification`
   anywhere on the subcontext stack) or inside an open `scope`. The `None` case now
   rejects instead of accepting.
2. **The constraint.** `ForwardsChecker::execute_rule` refuses to add a constraint
   mentioning such a variable to the **top-level** database. This is the invariant the
   whole defect turns on, and it is where the version 2.0 route is caught: that parser
   reads variables straight through `VarNameRecorder::add_by_name` and never calls
   `process_var_name`. Inside a subproof the question does not arise — everything a
   subproof derives is deleted at its `qed` — which is why the check is on
   `subcontexts.is_empty()` and not on `in_order_local_scope()`; upstream's
   `dominance_proofgoal_outside_scope.pbp` legitimately opens an order proofgoal whose
   premise is the negation of a definition constraint over `$d10`.

`ScopeRule::compute` additionally refuses to inject a specification into a database that
already constrains one of the active order's auxiliary variables. With (1) and (2) in place
that state is unreachable, so this is the claim *checked* rather than assumed, and a future
route into the database cannot re-open the hole silently. It costs one occurrence-list
lookup per auxiliary variable per `scope`, and upstream's `dominance_with_aux_vars` — which
opens a second scope after a first one derived dozens of constraints over those very
variables — is the proof that it does not over-reject.

The instance pairs `tests/instances/incorrect/version3/order_aux_var_asserted_top_level.*`,
`.../order_aux_var_asserted_top_level_red.*`, `.../order_aux_var_before_load_order.*` and
`tests/instances/incorrect/version2/order_aux_var_asserted_top_level.*` ride in the patch,
with upstream's `correct/version3/dominance_with_aux_vars.*` as the positive.
