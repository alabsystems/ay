# SMT-LIB sample corpus (fetched, not committed)

A **deliberately narrow, historical** 5-division slice, kept only because AY's
2026-07 evaluation campaigns were measured on it and `MANIFEST.sha256` pins
exactly what those numbers covered.

> **This tree is 1,500 files across 5 quantifier-free divisions — about 7% of
> SMT-LIB 2024 non-incremental (84 divisions, 4.75 GB compressed).** It contains
> no `QF_BV`, `QF_LIA`, `QF_IDL`, `QF_LRA`, `QF_NIA`, `QF_NRA`, `QF_ABV`, `BV`,
> `AUFBV` or `QF_UFBV` — the logics z3 is most used for. **Do not quote a
> completeness, speed, or "parity" number measured here as a corpus-wide result.**
> For anything load-bearing, use the full corpus in `benchmarks/smtlib-all`.

The `.smt2` files are **gitignored** (~93 MB). Re-fetch this exact slice with the
in-tree CLI tool:

```sh
# the full corpus — what a parity claim actually needs
ay-z3-parity fetch benchmarks/smtlib-all

# or reproduce this historical 1,500-file slice byte-for-byte
ay-z3-parity fetch benchmarks/smtlib-sample \
  --divisions QF_AX,QF_S,QF_SLIA,QF_UF,QF_UFLIA --sample 300
```

The tool downloads the archives below, verifies their MD5s against the values
Zenodo publishes, and applies the deterministic sampling rule. It reports
`coverage: COMPLETE` only when it fetched the whole record, and prints an
`!! INCOMPLETE COVERAGE` block naming every exclusion otherwise — the second
command above is expected to print one. Verify the slice against
`MANIFEST.sha256` (1500 SHA-256 lines, committed) as shown below.

The retired `fetch.sh` / `fetch-all.sh` shell scripts are replaced by that tool.
`fetch-all.sh` defaulted to a 60 MB archive cap, which silently excluded the ten
largest divisions from every corpus it built; the tool has no default cap and
cannot exclude anything silently.

## Source

SMT-LIB release 2024 (non-incremental benchmarks), Zenodo record
[11061097](https://zenodo.org/records/11061097). One `tar.zst` per division;
download URL pattern:

```
https://zenodo.org/api/records/11061097/files/<DIVISION>.tar.zst/content
```

| division | archive | size | archive md5 (Zenodo-published, verified) | files in archive | sampled |
|---|---|---|---|---|---|
| QF_UF | `QF_UF.tar.zst` | 54,287,659 B | `3ce26e05264581931a583bae96b87f34` | 7503 | 300 |
| QF_UFLIA | `QF_UFLIA.tar.zst` | 18,901,126 B | `26d8d7e71c33b10c9767beebddb5da9e` | 659 | 300 |
| QF_AX | `QF_AX.tar.zst` | 131,549 B | `6d323ea02eb4d74e8ac77420bf94e3cb` | 551 | 300 |
| QF_S | `QF_S.tar.zst` | 2,909,837 B | `e7a201b1fff6c952f278154d6513a0c0` | 18940 | 300 |
| QF_SLIA | `QF_SLIA.tar.zst` | 31,834,010 B | `277e586bf556ee33dc638348bc6de50a` | 84395 | 300 |

`QF_AX` exercises free-base reads; `QF_S` and `QF_SLIA` exercise strings,
including out-of-bounds `str.substr`. These historically error-prone theory
families are included in the differential corpus.

## Sampling rule (deterministic — no cherry-picking possible)

For each division:

1. List every `*.smt2` path inside the archive.
2. Sort lexicographically with `LC_ALL=C sort`.
3. Take `N = 300` evenly spaced entries: indices `floor(i * total / N)` for
   `i = 0 .. N-1` (all files when `total <= N`).
4. Copy flat into `benchmarks/smtlib-sample/<DIVISION>/`, replacing `/` in
   the archive-relative path with `__`.

The rule depends only on the archive contents, so any auditor re-running the
`--divisions ... --sample 300` command above obtains the exact same 1,500 files;
`MANIFEST.sha256` pins each file's SHA-256. Verify at any time with:

```sh
cd benchmarks/smtlib-sample && shasum -a 256 -c MANIFEST.sha256
```

## Why this slice is not a baseline

The larger divisions (`QF_BV` 1.7 GB, `QF_LIA` 689 MB, `QF_IDL` 428 MB, `AUFBV`
256 MB, ...) were originally omitted "to keep the fetch fast", via a default size
cap in the retired shell script. Because the cap was a silent default rather than
an explicit choice, that omission propagated into every AY-vs-z3 completeness and
speed figure without ever being stated — which is how a 5-division result came to
be read as a corpus-wide one.

The harness accepts any directory tree of `.smt2`, so use `benchmarks/smtlib-all`
(all 84 divisions, every file) for measurement, and treat this tree strictly as
the pinned record of what the 2026-07 campaign actually covered.
