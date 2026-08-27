# Expected verdicts for the FP-constructor operand tests

`crates/ay-dpll/tests/fp_constructor_operand_plumbing.rs` asserts a verdict for
each of seven queries. Those verdicts are not asserted on AY's own authority:
this directory extracts every SMT block straight out of the test file and has
z3, cvc5 and bitwuzla adjudicate them independently.

```sh
python3 extract_obligations.py \
  ../../crates/ay-dpll/tests/fp_constructor_operand_plumbing.rs cases
./run.sh cases
```

`run.sh` exits non-zero if ANY of the three disagrees with the verdict the test
expects, so a test whose expectation drifts away from the standard is caught
rather than blessed.

## Result (2026-08-25)

z3 4.16.0, cvc5 1.3.0, bitwuzla 0.9.1 — all seven unanimous, `FAIL=0`.

| case | expected |
|---|---|
| `reinterpret_double_from_extracts_is_satisfiable` | sat |
| `sign_field_is_tied_to_its_extract` | unsat |
| `exponent_field_is_tied_to_its_extract` | unsat |
| `significand_field_is_tied_to_its_extract` | unsat |
| `same_operands_give_the_same_float` | unsat |
| `concat_operands_are_constrained` | unsat |
| `mixed_literal_and_composite_fields_all_constrain` | unsat |

The six `unsat` cases are the load-bearing ones: each turns into `sat` — a wrong
answer — if any constructor field is left unconstrained.

## A note on `concat_operands_are_constrained`

Its first version extracted the fields back out on the same boundaries they were
concatenated on. The simplifier folds each operand to a bare variable, a bare
variable is a LEAF, and the leaf-only encoder this test exists to catch handles
leaves correctly — so the test passed even with the fix reverted. It now
straddles the concatenation boundary. Re-check that property before editing it:
a barrier you cannot make fail is not a barrier.
