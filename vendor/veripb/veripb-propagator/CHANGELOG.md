# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.1.2 - 2026-03-20

### New Features
- Autoproving using syntactic implication using constraints substituted with the assignment propagated at level zero and elaboration for this

### Changes
- Cache which positions we already looked at to find a new watch for general pseudo-Boolean constraints inside one RUP check
- `level_zero` has been changed to `assignment_independent`
- Optimizations for special cases
- Use `HashMap` to store watches of general PB constraints

### Bug Fixes
- Trail saving when switching back from only core propagation

### Commits

- Change propagator reset to only go through touched watchers
- Change propagator reset to use iterator
- Change to compress watchers storage of propagation engine
- Change to cache last watch position in one propagation run
- Change general pb watcher to store coeff
- Change general PB constraints watches to HashSet
- Add elaboration for autoproving using substituted implication
- Add autoproving using substituted syntactic implication
- Fix getting assignment independent proapgations after trail reset
- Fix name of function checking assignment independent propagation
- Improve propagation engine handling special cases more efficiently
- Rename level_zero propagation to assignment_independent
- Fix trail saving after being in core only propagation mode and switching back to core+derived mode.
- Fix formatting.
- Refactor move constraint to core propagation engine.

## 0.1.1 - 2025-11-02

### Changes
- Avoid allocation of watches if `Cardinality` is trivial
- Improve propagator for `Clause`
- Remove unnecessary unwraps to improve performance
- Improve trail saving

### Bug Fixes
- Resetting trail correctly with respect to the core set
- Assertion to respect negative right-hand side for `CardinalityWatcher`
- Early return if constraint is trivial

### Commits

- Fix resetting trail to respect core only reset
- Improve usability of literals, since they implement Copy
- Change to avoid allocation of vector if card is trivial
- Fix to early return initializing watches for trivial constraints
- Fix error message if solution conflicts with saved trail
- Remove checked unwraps
- Improve clause propagator
- Change constraint to remembers if it is in a saved reason
- Fix allocation of cardinality watcher for RHS larger than number literals
- Add constraint ID to error message when propagating conflicting solution
- Fix assertion to respect negative RHS of card constraint

## 0.1.0

This is the initial release of the library.
