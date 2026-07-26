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
ay corpus list                       # name / source / size / status / groups
ay corpus plan --all --json          # read-only dependency/tool/disk preflight
ay corpus download satcomp2024-sample
ay corpus download --all             # everything (slow first time)
ay corpus verify --all               # exact Git/HTTP/row checks; fresh archive tree comparisons
ay corpus prune <name>               # rm extracted dir
ay corpus check-urls                 # liveness-check every URL (CI gate)
```

Archive verification performs a fresh transactional extraction and compares
the complete materialized tree, so allow time and temporary disk space for a
second unpacked copy of each archive.

Before `tar` or `unzip` runs, the CLI preflights every member and link path,
rejecting absolute/non-normal member paths, escaping or missing link targets,
special file types, and link traversal. Absolute symlinks are rejected by
default. Ten organizer SAT 2026 author bundles explicitly enable deterministic
normalization: their exact pinned archive bytes are retained, but an absolute
target is rewritten to a relative target only when it has one unique
in-archive suffix match; missing or ambiguous matches fail. Verification
re-extracts with the same policy and compares the exact normalized tree.

For the audited 2025/2026 competition campaign, use the named acquisition
sets rather than `--all`:

```bash
# Proves all 832 catalog track IDs map exactly once to 39 event records and
# validates corpus references, pins, machine/run profiles, and subset policy.
ay corpus campaign-audit

# Read-only preflight: dependency closure, installed/missing assets, lower-bound
# transfer bytes, unknown-size sources, required tools, and filesystem space.
ay corpus plan \
  --group competition-2025-2026 \
  --group competition-2025-2026-competitors \
  --group competition-2025-2026-external

# Official/public benchmark and result assets used by the campaign.
ay corpus download --group competition-2025-2026

# Exact published competitor bundles currently admitted for same-host work.
ay corpus download --group competition-2025-2026-competitors

# Complete SV-COMP/Test-Comp result and witness evidence: ~135 GiB compressed.
# Required by --require-installed, but excluded from the four-hour recurring fetch.
ay corpus download --group competition-2025-2026-external

ay corpus verify --group competition-2025-2026
ay corpus verify --group competition-2025-2026-competitors
ay corpus verify --group competition-2025-2026-external
ay corpus campaign-audit --require-installed
```

Capacity planning must include extracted files and inodes, not just the
roughly 135 GiB of compressed external evidence. For that external group
alone, the six SV-COMP/Test-Comp archives materialize 755,699,740,029 bytes
(755.7 GB decimal) and 6,949,910
entries in total; the two witness trees alone contain 6,793,817 entries.
Strict verification creates one additional archive staging tree at a time, up
to 294,316,054,041 bytes and 3,563,941 entries for the SV-COMP 2025 witnesses.
Allow roughly 755.7 GB plus the retained archives for installation, another
294.3 GB and at least 3.6 million free inodes during the largest verify.
Additionally reserve headroom for roughly 43.5 GB of known compressed
core/competitor transfers plus retained archives, unknown-size Git checkouts,
extracted trees, and transactional staging.

The plan lists `git-lfs-materialization` only for a Git corpus whose pinned
tree is declared to contain actual LFS pointer blobs. Historical
`filter=lfs` attributes on ordinary Git blobs do not require Git LFS.
ARCH-COMP remains `partial-public`: two old 2023 NNV gitlinks lack
`.gitmodules` mappings. The manifest names those two mode-160000 paths as
exact exceptions, so verification succeeds only when the checkout has exactly
that declared unmapped set; any missing, stale, or additional exception
fails. The 2025/2026 tracks remain partial because category-specific
selections, limits, and runnable adapters are still incomplete.

The campaign crosswalk is
[`competition-assets-2025-2026.toml`](competition-assets-2025-2026.toml);
resource and deterministic-subset classes are in
[`competition-run-profiles.toml`](competition-run-profiles.toml). A
`complete-public` corpus status means the public inputs are acquired and
pinned. It does not mean AY can execute that format, that top submissions are
redistributable, or that this machine matches official hardware.

The 832 identities include secondary public score surfaces where they matter
for regression tracking: 337 SMT-COMP 2025 division/recognition views, 104
SV-COMP 2025/2026 category-score views, and 25 VNN-COMP 2025 category
leaderboards. Those are labeled separately from medal tracks. The TermCOMP
2026 registration repository is pinned as
`termcomp-registration-2026`; eleven newly discovered category candidates
remain conditional until both the benchmark-count threshold and final results
are public.

The competitor group currently acquires 20 official SAT/MaxSAT source
archives: three SAT Competition 2025 submissions, all 14 organizer-published
SAT Competition 2026 Main Track author bundles, and three MaxSAT Evaluation
2026 submissions. It is not a complete executable top-three field: several
packages are source-only, required proof checkers/adapters are not yet
integrated, and most campaign tracks have no downloaded competitor. The
comparable and official profiles are fail-closed policy manifests until those
runner requirements are implemented.

Each entry's `source` is one of:

- `release` (default) — a tarball uploaded as a
  [alabsystems/ay release asset](https://github.com/alabsystems/ay/releases),
  SHA256-pinned; the only source that supports two-way `ay corpus upload`.
- `http` — an archive fetched from a fixed upstream URL (`archive` selects
  `tar` (default), `zip`, or `none`).
- `git` — a shallow fetch at optional exact `commit`; set
  `requires_git_lfs = true` only when that pinned tree contains actual LFS
  pointer blobs. The downloader then fails before cloning if `git-lfs` is
  unavailable and explicitly pulls/materializes LFS content recursively.
- `gbd` — per-file fetch from the Global Benchmark Database, driven by a
  `manifest` CSV with `hash` and `local_path` columns; campaign rows also
  require exact `size_bytes` and `sha256` response pins. Duplicate content IDs
  are fetched once and hard-linked/copied to distinct scored row paths.
- `uri-list` — a tracked HTTPS list. Campaign TSV rows enforce per-response
  byte and SHA-256 pins. GBD CNFs remain compressed; the runner decompresses
  the verified artifact into private per-run storage.

Entries may declare `depends_on`; downloads resolve dependencies
topologically, so fetching `satcomp-2025-main` directly first installs its
pinned official URI list. Manifest destinations are resolved relative to the
repository, so the CLI works when invoked outside the checkout directory.

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
ay bench campaign plan --profile reviewer-full
ay bench campaign run --profile reviewer-full --require-installed
ay bench list
```

Pass `--output <path>` (or `-o <path>`) to write a combined scorecard JSON;
local evaluation result directories are not part of the published benchmark
corpus.

`ay bench campaign run` is the external-reviewer entry point: it attempts every
eligible campaign lane and emits one explicit disposition for all 832 tracks.
`ay bench run --all` means every locally registered executable eval, including
development-only definitions, not all 832 catalog tracks. Unsupported formats
remain explicit in the campaign crosswalk. Official organizer results are
imported evidence; local runs are either same-host-calibrated or proxy runs
unless exact machine, toolchain, checker, limits, and corpus gates all pass.
