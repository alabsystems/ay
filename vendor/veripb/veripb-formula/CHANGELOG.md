# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.1.2 - 2026-03-20

### New Features
- New cutting planes rules
  - `-` rule to lower the RHS of a constraint by a positive integer (e.g., `pol 42 3 -;` lowers RHS of constraint `42` by 3)
  - `c` rule for division in variable form, i.e., all literals are positive and negative coefficients are allowed (similar to Chvátal-Gomory cut)
  - `n` rule for mixed integer rounding (MIR) cut on constraints in normalized form (e.g., `pol 42 3 n;` for MIR cut of constraint `42` with divisor 3)
  - `m` rule for mixed integer rounding (MIR) cut on constraints in variable form
- Faster cutting planes checking functions for merged weakening steps and additions of literal axioms

### Changes
- No longer elaborate syntactic implications, as they are now supported in the kernel format

### Bug Fixes
- Fix overflow issues for cutting planes operations

### Commits

- Fix appending IDs for duplicate constraint IDs
- Fix hidden overflow for decrease RHS rule
- Clean up conditions
- Remove unnecessary where clauses
- Also fix same bug for clauses and add further overflow checks.
- Fix embarrassing flipping of expression.
- Fix formatting
- Fix
- Fix not keeping the exact degree for cardinality constraints.
- Fix bug where adding a constraint with no terms and huge degree to a cardinality constraint caused overflow.
- Change general PB constraints watches to HashSet
- Add variable for MIR cut rule
- Add normalized form MIR cut rule
- Add variable form cutting planes division
- Add rule to lower RHS of constraint
- Add elaboration for autoproving using substituted implication
- Add autoproving using substituted syntactic implication
- Change that less trivial constraint is also implied
- Remove elaboartion of implication to cutting planes
- Fix test cases to give full assignment to objectives
- Fix checking upper bound value conclusion with respect to original
- Add documentation and comments to the verifier functions
- optimize consecutive weakenings
- make clippy and format happy
- merge together literal axiom additions
- improve performance merge-terms by avoiding peekable
- Fix indexing error when a constraint was in the derived propagation set, then rup'ed (to make a copy) and the copy was moved to core which did not move the propagation constraint to the core propagator.

## 0.1.1 - 2025-11-02

### New Features
- Tracing for annotated RUP
- Constraint remembers if it is used in a saved trail
- Documentation of library functions

### Changes
- Make use of `Lit` being `Copy`
- `Substitution` uses `SubstitutionValue::MAX` and `SubstitutionValue::MAX - 1` to represent true and false
- Rename `implies` to `implies_weak` and `implies_strong` to `implies`

### Bug Fixes
- Syntactic implication check and elaboration
- Resetting trail correctly

### Commits

- Change substitution to use maximum values for constant true and false
- Add documentation for formula library
- Fix elaboration of syntactic implication to use negated literal for
- Fix resetting trail to respect core only reset
- Add elaboration for syntactic implication from contradiction
- Fix generic syntactic implication algorithm
- Move elaboration into separate functions
- Fix syntactic implication handling trivial constraints
- Improve usability of literals, since they implement Copy
- Rename implies to implies_weak and implies_strong to implies
- Elaboration of syntactic implication: Add missing literal axioms.
- Change constraint to remembers if it is in a saved reason
- Add tracing failed annotated RUP steps
- Exclude VeriPB test instances in published crate; Add metadata
- Add information to prepare release as VeriPB
- Rename PBOxide packages to VeriPB packages

## 0.1.0

This is the initial release of the library.
