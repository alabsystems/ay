# 22 — the WCNF parser names variables from the literal's token TEXT (FIXED in the fork)

The defect is in the **formula parser**, so it does not need a clever proof: it hands the
checker a different problem from the one on disk.

|                                |                                                                        |
| ------------------------------ | ---------------------------------------------------------------------- |
| formula                        | `split.wcnf` — hard `(x1)`, hard `(~x1)` written `-01`, soft `(x2)` weight 5 |
| proof                          | `split.pbp` (four lines)                                               |
| **unfixed verdict**            | `s VERIFIED BOUNDS 0 <= obj <= 0`, exit 0                              |
| **truth**                      | **INFEASIBLE** — the two hard clauses are `(x1)` and `(~x1)`; 0 of 4 assignments satisfy them |
| present in stock upstream `4bb10c2c` | yes                                                                    |
| present with `0001` only       | **yes**                                                                |
| present with the pinned patch | no — rejected, no `s` line                                             |

Note the FLAG: this fixture is `--wcnf`, the only one in the directory.

## The bug

`veripb-parser/src/wcnf_parser.rs` parsed the literal into an `i64` — and then built the
variable's name out of the **token text** it came from:

```rust
..0 => current_lits.push(Lit::from_var(
        var_name_manager.add_by_name(&(String::from("x") + &lex.slice()[1..])), true)),
1.. => current_lits.push(Lit::from_var(
        var_name_manager.add_by_name(&(String::from("x") + lex.slice())), false)),
```

DIMACS integers may carry a sign and leading zeros. `1`, `01` and `0001` are **one**
variable; `-1`, `-01` and `-0001` are its negation. Naming from `lex.slice()` split that one
variable into as many variables as there were spellings, so the infeasible

```
h 1 0        ->  (x1)
h -01 0      ->  (~x1)
```

parsed as `(x1) AND (~x01)` over two *different* variables — a satisfiable formula — and the
optimum of a MaxSAT instance with no feasible solution came out as 0.

The value was already in hand (`lex.slice().parse::<i64>()` runs three lines earlier, and
its result drives the `0 / ..0 / 1..` dispatch). Only the name was built from the text.

## Evidence chain

```
c the two hard clauses contradict: (x1) and (~x1)
h 1 0
h -01 0
5 2 0

pseudo-Boolean proof version 3.0
f 2;
output NONE;
conclusion BOUNDS 0 0 : x1 ~x01 x2;   % the hint names BOTH halves of the split variable
end pseudo-Boolean proof;
```

The hint `x1 ~x01` is the fingerprint: it satisfies both hard clauses only because the
parser believes they are about different variables.

## The pair that needs no external oracle

`infeasible.pbp` is the same formula and the same binary, resolving the two hard clauses to
the empty clause and concluding `s VERIFIED BOUNDS INF <= obj <= INF`, exit 0.

This pair is unusual and worth reading carefully: the **honest** proof is the one that only
checks *after* the fix. On the unfixed parser `pol 1 2 +` produces `+1 x1 +1 ~x01 >= 1`
rather than the empty contradiction, so the checker refuses it — the truth about the
instance was not provable at all.

```bash
veripb --wcnf split.wcnf split.pbp        # rejected (unfixed: s VERIFIED BOUNDS 0 <= obj <= 0)
veripb --wcnf split.wcnf infeasible.pbp   # unfixed: refused. fixed: s VERIFIED BOUNDS INF <= obj <= INF
```

## `variants/`

| variant | reach path / knob | unfixed | fixed |
| --- | --- | --- | --- |
| `optimum/opt.pbp` | a **feasible** instance whose optimum is 5, certified as 0: hard `(x1)`, soft `(~x1)` weight 5 written `-0001` | `VERIFIED BOUNDS 0 <= obj <= 0` | rejected |
| `optimum/opt-true.pbp` | **POSITIVE**: the *correct* optimum of that same instance | rejected (not provable) | `VERIFIED BOUNDS 5 <= obj <= 5` |
| `controls/control.pbp` | **one knob**: the forging proof against a formula whose only difference is `-01` spelled `-1` | rejected | rejected |
| `controls/opt-control.pbp` | **one knob**: the true-optimum proof against the same instance with `-0001` spelled `-1` | `VERIFIED BOUNDS 5 <= obj <= 5` | `VERIFIED BOUNDS 5 <= obj <= 5` |
| `sibling-cnf-parser/twin.pbp` | **POSITIVE**: byte-identical literal text (`1 0` / `-01 0`) through the sibling DIMACS **CNF** parser, which uses the parsed integer as the variable index and never had the defect | `VERIFIED UNSATISFIABLE` | `VERIFIED UNSATISFIABLE` |

`controls/` is the causation argument: change five bytes of the *formula* — the spelling of
one literal — and the **unfixed** checker refuses the identical proof, or accepts the
identical honest one. Nothing about the proof, the objective, or MaxSAT in general is
implicated.

`sibling-cnf-parser/` is the audit note the fix direction asked for, made executable. The
OPB and CNF parsers were checked for the same mistake: OPB variables genuinely *are* names,
and the CNF parser writes `Lit::from_var((-integer) as usize, true)`, using the value. Only
WCNF built a name out of text. That is pinned here rather than asserted, so a future "tidy
up" that unifies the three parsers on the wrong one turns the gate red.

## The fix (now in the fork; formerly ay patch `0002`)

Name from the value:

```rust
..0 => … add_by_name(&format!("x{}", integer.unsigned_abs())) …
1.. => … add_by_name(&format!("x{integer}")) …
```

`unsigned_abs()` rather than `-integer`, because negating `i64::MIN` is not representable —
the same escalate-don't-wrap discipline the arithmetic fixes use.

`veripb-parser/tests/parse_wcnf.rs` carries
`wcnf_literal_spellings_of_one_variable_are_one_variable`, which parses an instance using
`1`, `01`, `0001`, `-1` and `-01` and asserts it yields exactly one variable — plus
`cnf_literal_spellings_of_one_variable_are_one_variable`, which pins the sibling parser on
the same input text. There is no integration-test pair: the checker's harness looks for
`.opb` or `.cnf` beside the `.pbp` and cannot drive a `.wcnf` formula, which is a
coverage gap of that harness worth knowing about.
