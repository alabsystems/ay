Proof representation for AY

Proofs can be produced for unsatisfiable formulas.
Supports export to Alethe format for independent verification.

## Alethe Proof Format

The Alethe format (used by carcara proof checker) has three main commands:
- `assume`: Input assertions from the problem
- `step`: Proof steps with a rule name, premises, and conclusion clause
- `anchor`: Subproofs (for nested reasoning)

Example Alethe proof:
```text
(assume h1 (= a b))
(assume h2 (= b c))
(step t1 (cl (= a c)) :rule trans :premises (h1 h2))
(step t2 (cl (not (= a c)) (= a c)) :rule equiv_pos1 :premises (t1))
```
