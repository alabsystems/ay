# Current Z3 discovery baseline

`discovery.json` retains eight complete stdout transcripts from the exact
macOS ARM Z3 5.3.3 executable pinned in `ci/z3.pin`, SHA-256
`9b3df8db3324ac2de9ebdd2841477366ecad0626656f806c2168ebf2732745a4`.
Each invocation exited zero with empty stderr. The existing `_oom_guard.py`
supervisor enforced a five-second deadline and 256 MiB RSS ceiling; each
redirected output file also had a 1 MiB kernel file-size limit.

Invocations were `-version`, `-h`, `-tactics -in`, `-probes -in`,
`-simplifiers -in`, `-p -in`, `-pd -in`, and `-in` with `(help)` and `(exit)`.
The file records each stdout hash and is itself pinned in the source owner.
It defines a discovery baseline, not a behavioral compatibility result.

The independent source checkout is tag `z3-5.3.3`, commit
`430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e`. Its 3,661-file path/blob/size
manifest hashes to
`a48aaa79d461d07f90ffbf4323a7c3b674457145fde1cd5ecf312bbd46343967`.
The current source owner includes all native `Z3_ADD_*` registration files and
matches their literal names and descriptions against these live catalogs.
Any unresolved broad-scan registration candidate remains failed evidence.

`observable-items.tsv` is the canonical 1,635-row source/live owner manifest,
SHA-256 `f5017ff3d0457bff6fc4b74d51024ffa073f06100e79829111ce7a5875b9a464`.
It is a test fixture for generating and validating every behavioral receipt
descriptor before running child processes. Runtime source extraction still
authenticates the pinned source and live registries independently.

`LICENSE.txt` is the upstream Z3 source license for the retained transcripts.
