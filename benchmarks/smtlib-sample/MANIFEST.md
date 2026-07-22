# SMT-LIB sample corpus (fetched, not committed)

Real SMT-LIB divisions used by AY's differential evaluation campaigns. The `.smt2`
files are **gitignored** (~93 MB); anyone can re-fetch the byte-identical corpus
with:

```sh
bash benchmarks/smtlib-sample/fetch.sh
```

which downloads the archives below, verifies their MD5s against the values
Zenodo publishes, applies the deterministic sampling rule, and checks every
resulting file against `MANIFEST.sha256` (1500 SHA-256 lines, committed).

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

The rule depends only on the archive contents, so any auditor re-running
`fetch.sh` obtains the exact same 1,500 files; `MANIFEST.sha256` pins each
file's SHA-256. Verify at any time with:

```sh
cd benchmarks/smtlib-sample && shasum -a 256 -c MANIFEST.sha256
```

Larger divisions (QF_LIA is a 689 MB archive, QF_IDL 428 MB) were not
included to keep the fetch fast; the harness accepts any directory tree of
`.smt2`, so scaling up is a matter of pointing `fetch.sh` at more divisions.
