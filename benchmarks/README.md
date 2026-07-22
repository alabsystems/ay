# Benchmarks

Benchmark corpora used by AY live under this directory.

## Common Subtrees

- `sat/` for SAT and SAT-COMP-style corpora
- `sat/proof-complexity-hard/` for the tracked hard-family slice used by
  proof-complexity experiments
- `smt/` for SMT workloads
- `chc/` for CHC workloads
- `consumers/` for downstream integration fixtures

## Fetching large corpora — `ay corpus`

Bulky benchmark sets (SAT-COMP, SMT-LIB, PB-Comp, security suites, etc.) are
not checked into the source tree. They are described in
[`corpora.toml`](corpora.toml) and fetched on demand via the `ay corpus`
subcommand:

```bash
ay corpus list                       # name / source / size / status
ay corpus download satcomp2024-sample
ay corpus download --all             # everything (slow first time)
ay corpus verify --all               # re-hash cached release tarballs
ay corpus prune <name>               # rm extracted dir
ay corpus check-urls                 # liveness-check every URL (CI gate)
```

Each entry's `source` is one of:

- `release` (default) — a tarball uploaded as a
  [alabsystems/ay release asset](https://github.com/alabsystems/ay/releases),
  SHA256-pinned; the only source that supports two-way `ay corpus upload`.
- `http` — an archive fetched from a fixed upstream URL (`archive` selects
  `tar` (default), `zip`, or `none`).
- `git` — a `git clone --depth <depth>`, with an optional `commit` pin.
- `gbd` — per-file fetch from the Global Benchmark Database, driven by a
  `manifest` CSV with `hash` and `local_path` columns; each row is pulled from
  `https://benchmark-database.de/file/<hash>` and written to its `local_path`.

Adding a new corpus means appending an entry — see the comments at the top of
`corpora.toml` for the schema. To publish a new version of a `release`
corpus, run `ay corpus upload <name>`: it repacks `extract_to`, uploads, and
rewrites the manifest's SHA + size.

The MiniZinc challenge fixtures under `minizinc/challenge/` are intentionally
tracked because `ay-fzn2smt` compile-time tests include them directly.
The SAT multiplier22 sample under `sat/satcomp2024-sample/` is intentionally
tracked because `ay-sat` source tests load that exact compressed fixture.

## Running Evaluations

Benchmarks run through the `bench` subcommand of the `ay` binary (the
`ay-bench` crate is library-only — it has no standalone executable):

```bash
ay bench run --help
ay bench run chccomp-2025-extra-small-lia
ay bench run --domain chc
ay bench list
```

Pass `--output <path>` (or `-o <path>`) to write a combined scorecard JSON;
local evaluation result directories are not part of the published benchmark
corpus.
