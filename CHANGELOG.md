# Changelog

AY had no changelog before 2026-08-28. This file is reconstructed from the
release commits and tags that exist in the repository, so it is a *record of
what was cut*, not a curated feature list. Where the evidence does not support
a description of what changed, this file says so instead of inventing one.

**Versioning.** The patch slot is always `0`; `MINOR` is the knob that moves,
and public tags are always `vMAJOR.MINOR.0`. A non-zero patch version (e.g.
`0.1.1`) is an internal bump, not a public release.

**Commit hashes.** The hashes below name commits in AY's development history.
The public repository is a snapshot repository with rewritten history, so a
development hash does not resolve there. They are recorded as provenance for
the release record, not as links.

**How each entry was derived.**

- *Date* — for a tagged version, the date of the tag (annotated tags carry
  their own date, which can be a day later than the commit they point at). For
  an untagged version, the date of the release commit, and the entry says the
  version is untagged.
- *Release point* — the commit the tag points at, or the release commit when
  there is no tag. `pub bump` writes the version; the snapshot is sometimes cut
  a few commits later, which is why several tags do not sit on their bump.
- *Volume* — non-merge commits between the previous release point and this one,
  with the most common conventional-commit subject prefixes. This is a
  mechanical summary of subject lines. It is not a feature list, and a large
  count does not mean a large release.

## Tagging gaps in this repository

Recorded here because there is no other durable home for it, and because the
tag list is otherwise read as complete:

- **`v0.2.0` is missing.** The release commit `f0c094e74` ("chore(release): ay
  0.2.0", 2026-07-22) exists and is on `main`; no tag points at it.
- **`v0.4.0` is missing.** The release commit `93bf5b3be` ("chore(release):
  0.3.0 -> 0.4.0", 2026-07-25) exists and is on `main`; no tag points at it.
- **`v0.18.0` is not tagged in this tree** even though it was published:
  `bd3a01f15` records that `alabsystems/ay` carries `v0.18.0`, cut from
  `ccc05d91c`.
- **`v0.9.0` is a lightweight tag** — a bare ref with no tag object, unlike
  every other release tag here, which is annotated.
- `v0.1.1` has no tag, and correctly so: `f0c094e74` states that `0.1.1` was
  internal and `X.Y.0` is the public line.

These are recorded, not repaired. Public tags are minted by `pub promote` from
a human terminal against `alabsystems/ay`; retro-tagging a dev tree would
create tags that do not correspond to any published snapshot.

## Releases

### 0.19.0 — 2026-08-28 (untagged; current workspace version)

Release commit `bd3a01f15`. Not yet tagged in this repository or published.
The commit records why the bump was needed: `alabsystems/ay` already carries
`v0.18.0` cut from `ccc05d91c` and tags are immutable, so the next public
snapshot needs its own version. Because AY pins its siblings by explicit
version rather than `version.workspace = true`, the bump moved 61
intra-workspace path-dependency requirements along with `[workspace.package]`.

12 non-merge commits since the 0.18.0 snapshot point (`docs` 3, `test` 2,
`fix` 2, and singletons). A further 13 commits have landed on `main` after the
bump and are not part of any cut snapshot.

### 0.18.0 — 2026-08-28 (no tag in this repository)

Release commit `0c987ad35`; the published snapshot was cut from `ccc05d91c`
per `bd3a01f15`. The bump commit explains that ten commits since `v0.17.0` —
counterexample-contaminated cone certification, the const-array fold
re-derivation, the bv2nat/int2bv substitution recovery, the DPLL strict-walk
memo keying — were already named by a downstream pin, so AY released again
rather than having the downstream walk its pin backward.

39 non-merge commits since `v0.17.0` (`fix` 22, `docs` 4, `test` 3, `style` 2).

### 0.17.0 — 2026-08-27

Tag `v0.17.0` → `d81752e07`. The release commit states the reason for the
bump: `v0.16.0` was already tagged in the dev and staging namespaces so the
engine refused another snapshot at it, while a downstream manifest pinned AY
past the released 0.16.0 revision and could not export until AY published
again.

21 non-merge commits since `v0.16.0` (`docs` 9, `fix` 5, and singletons).

### 0.16.0 — 2026-08-27

Tag `v0.16.0` → `a5a209cac`. The release commit records that the 0.15.0 stage
passed every guard — forbidden content, private refs, gitleaks, cargo
workspace closure, and the public-clone build — but could not be released
because `v0.15.0` was already tagged, and that bumping `[workspace.package]`
alone does not resolve: 61 first-party dependencies pin siblings by explicit
version. `Cargo.lock` was refreshed with 69 first-party entries at 0.16.0.

421 non-merge commits since `v0.15.0` (`fix` 157, `feat` 58, `chore` 49,
`docs` 29, `refactor` 26). Not characterized further here.

### 0.15.0 — 2026-08-21

Tag `v0.15.0` → `09951c0e6`; release commit `5368801e3` ("Minor bump per
VERSIONING.md ... Cut by `pub bump`"), which describes only the bump.

110 non-merge commits since `v0.14.0` (`fix` 27, `feat` 15, `docs` 11,
`chore` 8, `measure` 7).

### 0.14.0 — 2026-08-20

Tag `v0.14.0` → `83495c23b`. The release commit notes it was cut by hand
because `pub` was not installed on that host, and that the diffstat matched the
shape of the 0.12→0.13 cut: 62 version strings, all AY crates plus
`[workspace.package]`, with no third-party dependency sitting at 0.13.0.

102 non-merge commits since `v0.13.0` (`fix` 28, `feat` 13, `docs` 11,
`test` 9, `measure` 6).

### 0.13.0 — 2026-08-20

Tag `v0.13.0` → `4870f6176` (commit dated 2026-08-19; tag dated 2026-08-20).
Release commit describes only the bump.

9 non-merge commits since `v0.12.0`.

### 0.12.0 — 2026-08-19

Tag `v0.12.0` → `682381780`. Release commit describes only the bump.

14 non-merge commits since `v0.11.0`.

### 0.11.0 — 2026-08-19

Tag `v0.11.0` → `ce23a9d3f`. This bump was deliberate rather than routine: the
commit records that `main` was 161 commits past the published `v0.10.0` while
both still declared `version = "0.10.0"`, and that a downstream `[patch]` by
path only checks that the patched source *satisfies* the requirement — so the
drift was being accepted silently. The bump makes that drift fail loudly.

140 non-merge commits since `v0.10.0` (`fix` 34, `docs` 26, `feat` 21,
`measure` 10, `chore` 7).

### 0.10.0 — 2026-08-17

Tag `v0.10.0` → `0c0538325`; release commit `ee5f3f62a` (2026-08-16) describes
only the bump.

608 non-merge commits since `v0.9.0` (`refactor` 174, `fix` 112, `test` 75,
`feat` 68, `chore` 30). Not characterized further here.

### 0.9.0 — 2026-08-12

Tag `v0.9.0` → `1f8238bbc` (lightweight tag). Release commit describes only the
bump.

90 non-merge commits since `v0.8.0` (`fix` 43, `style` 11, and a long tail).

### 0.8.0 — 2026-08-11

Tag `v0.8.0` → `6118a5222`. Release commit describes only the bump.

26 non-merge commits since `v0.7.0` (`fix` 14, and a short tail).

### 0.7.0 — 2026-08-11

Tag `v0.7.0` → `937092bb9`. Release commit describes only the bump.

88 non-merge commits since `v0.6.0` (`fix` 28, `evidence` 9, `test` 8,
`measure` 7).

### 0.6.0 — 2026-08-10

Tag `v0.6.0` → `68a4e19ab`. Release commit describes only the bump.

888 non-merge commits since `v0.5.0` (`fix` 223, `measure` 96, `feat` 85,
`docs` 71, `evidence` 66) — the largest range between two releases in this
history. Not characterized further here.

### 0.5.0 — 2026-07-28

Tag `v0.5.0` → `fc32ad715` ("fix(publish): export ci/veripb.pin so the public
workspace compiles"); release commit `fc48e988f` describes only the bump.

332 non-merge commits since the 0.4.0 release commit (`docs` 75, `measure` 70,
`fix` 57, `feat` 26, `correct` 19).

### 0.4.0 — 2026-07-25 (untagged)

Release commit `93bf5b3be` ("chore(release): 0.3.0 -> 0.4.0"). **No `v0.4.0`
tag exists in this repository** — see "Tagging gaps" above. The commit
describes only the bump.

6 non-merge commits since `v0.3.0`.

### 0.3.0 — 2026-07-25

Tag `v0.3.0` → `0bc9377c4`; release commit `d25432622` (2026-07-23). The
release commit records that the internal workspace-dependency constraints were
moved with the version (caret `^0.2.0` rejects 0.3.0) for a new public snapshot
at a downstream pin.

640 non-merge commits since the 0.2.0 release commit (`fix` 177, `docs` 177,
`feat` 97, `test` 44, `perf` 41). Not characterized further here.

### 0.2.0 — 2026-07-22 (untagged)

Release commit `f0c094e74` ("chore(release): ay 0.2.0; drop dead developer
corpus paths from ay-milp test"). **No `v0.2.0` tag exists in this
repository** — see "Tagging gaps" above. Alongside the bump, the commit
removed hardcoded developer corpus paths from `parallel_ready.rs`, which it
identifies as the only place such a path reached the public export.

1 non-merge commit since the 0.1.1 bump.

### 0.1.1 — 2026-07-22 (internal, not a public release)

Release commit `e524966f0`. Only `[workspace.package].version` changed;
internal caret constraints (`^0.1.0`) already accepted it, so no dependency
lines moved. `f0c094e74` states explicitly that 0.1.1 was internal.

129 non-merge commits since `v0.1.0` (`fix` 32, `docs` 32, `feat` 22,
`perf` 10, `style` 8).

### 0.1.0 — 2026-07-21

Tag `v0.1.0` → `81223f7c0`. The first public release. Everything before it is
initial development — the repository's first commit is dated 2026-05-24 — and
is not characterized here.
