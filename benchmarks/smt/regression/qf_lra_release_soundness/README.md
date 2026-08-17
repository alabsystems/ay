# Hermetic QF_LRA release soundness regressions

These three Apache-2.0 inputs are hand-authored structural reductions for the
release-only soundness mechanisms first exposed by external SMT-LIB corpus
benchmarks:

- slack_reason_sat.smt2 exercises the #6564 implied slack-row reason path.
- open_zero_lower_sat.smt2 and open_zero_upper_sat.smt2 exercise both strict
  endpoint directions fixed by #6582.

They are not copied or minimized from the external benchmark corpus. Each has
an obvious rational witness and declares status sat, so the default test gate
is hermetic, does not probe Z3, and is license-safe.

The optional full-corpus differential sweep uses the separately fetched
SMT-LIB 2024 QF_LRA archive from Zenodo record 11061097. Fetch it with:

```sh
scripts/download_smtcomp_benchmarks.sh --logic QF_LRA
```

The fetcher verifies archive SHA-256
`8e551882cf78432953f9e6f452cde098835e6cdc64b301becf42135609ee9881`,
checks the recursive archive contract of exactly 1,753 `.smt2` files, verifies
the installed bytes, and records ignored local provenance. The opt-in sweep
requires that provenance and Z3; none of those external inputs are needed by
the default release gate.
