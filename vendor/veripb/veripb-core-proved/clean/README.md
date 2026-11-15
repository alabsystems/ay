# `veripb-core-proved/clean` — the machine-checked kernel and its evidence

Four committed artifacts, and what each one is worth on its own.

| file | what it is | who can check it |
|---|---|---|
| `veripb_kernel.lean` | the kernel: every definition and theorem the Rust in `../src` mirrors, plus the machine-width theorems the `ensures` citations in `../src/trust_surface.rs` name | anyone with `clean` |
| `veripb_kernel.cleancert` | the exported proof bundle: one replayable `ProofCert` per theorem, with the environment it elaborated in | **anyone with any `clean` binary**, without re-elaborating the source |
| `veripb_kernel.manifest.txt` | sorted `name type_hash proof_hash` per bundled theorem, plus a header naming the kernel text it was exported from | anyone, in two halves: `targo --unverified test -p veripb-core-proved --test bundle_sync` checks the **names** against the `.lean` with no verifier at all, and the `bundle identity` stage of `scripts/verify-proofs.sh` re-derives the **hashes** from the bundle, which needs `clean` |
| `proved-core-expected.txt` | every magnitude the gates assert, and the identity of the two toolchains that measured them | anyone |

Regenerate all of it with one command, which is also the only blessing point:

```
scripts/verify-proofs.sh --refresh     # then review the diff
```

`scripts/regen-island.py` regenerates the Clean island inside
`../src/trust_surface.rs` from `veripb_kernel.lean`; run it after any edit to
the `.lean`, and `targo --unverified test -p veripb-core-proved --test island_sync`
will tell you if you forgot.

## Why a manifest exists at all

`downstream proof consumer cert verify` replays every stored proof term against its own
stored statement and reports `passed=N failed=0`. That is a strong result about
the proofs and **no result at all about the statements**: if a hypothesis were
added to `entails_add`, or `checker_sound`'s conclusion weakened, the rewritten
bundle would still replay `N/N` and the count would still be green. Neither does
the count tie the bundle to the source committed beside it — a bundle exported
from an older `.lean` replays perfectly too.

The manifest closes both. Per theorem it pins the **statement** (`type_hash`)
and the **proof term** (`proof_hash`); in its header it pins the kernel text the
bundle was exported from (`island_sha256`). `scripts/verify-proofs.sh`
re-derives the whole file from the bundle and diffs it, so a changed statement
under an unchanged name is a red gate rather than a silent success.

## The export boundary

`veripb_kernel.lean` carries an `-- EXPORT-CERT-BOUNDARY` marker near the end.
Everything below it is type-checked by `clean check` and kernel-checked by
compiler_consumer as part of the island, but is excluded from `clean export-cert`.

The reason is measured, not defensive: `key64` folds a `BitVec 64` through
`Nat.xor _ 9223372036854775808` (and its 128-bit twin `key128` folds through
`Nat.xor _ 2^127`), and elaborating a proof *certificate* for a theorem over
either exhausts all 128 GB of RAM on the reference machine and is SIGKILLed — with the documented debug `clean 0.1.0` and with a release
`clean 1.4.0` alike. With the block excluded the same export finishes in 11 s.
Type checking is unaffected: `clean check` passes on the whole file, all
declarations, in seconds.

So those declarations are *proved*; they are simply not *replayable from the
bundle*, and neither `scripts/verify-proofs.sh` nor the manifest pretends
otherwise. `tests/bundle_sync.rs` splits at the same marker, so the manifest is
still required to cover exactly the theorems above it, and additionally
asserts that no theorem from below the marker appears in the manifest claiming
to have been replayed.

The shared decision lemma `decide_le_exact`, which both width-guard theorems
instantiate, is deliberately stated over bare `Nat`s and placed *above* the
marker, so the reusable half of those proofs is in the bundle even though the
carrier-specific halves are not.

If `clean export-cert` ever grows a bounded-`Nat` representation for this
shape, delete the marker and re-run `--refresh`; the gates need no change.

## Two caveats about the format, neither of which weakens the result

**`clean export-cert` is not byte-reproducible.** The bundle's `certs` /
`xproj_certs` maps and its `Environment` are `HashMap`s, bincoded in randomized
iteration order and then zstd-compressed, so two exports of byte-identical input
differ in their bytes. Consequently neither the bundle's sha256 nor its
top-level `env_hash` is a stable identity, and nothing here gates on either. The
per-theorem `type_hash` / `proof_hash` **are** stable across independent
exports, which is why the manifest pins those instead. Neither the bundle bytes
nor its `env_hash` is recorded in `proved-core-expected.txt` at all — not even
"for reference": a number that moves on every re-export in a file whose whole
purpose is that a changed number is a red gate would be a permanent false
alarm. The closing comment of `proved-core-expected.txt` says so in the file
itself.

**Every locally exported bundle reports `Trust level: unverified`** — printed
by `downstream proof consumer cert verify` and `downstream proof consumer cert inspect` alike, and
accompanied by `Trust chain: absent` in `downstream proof consumer cert stats`. That is a
property of the format, not of these proofs:
`CertBundle::build` stamps `TrustLevel::Unverified` on every entry, because a
serialized manifest is a claim rather than replay evidence, and the
`KernelVerified` level additionally requires a rooted cross-project
certification audit that this project does not perform. The substantive result
is the replay itself: `downstream proof consumer cert verify veripb_kernel.cleancert` ends
`Result: N passed, 0 failed (ALL PASSED)`, which any `clean` binary can
reproduce from the committed file. Note that `cert verify` reports no axiom or
`sorry` figure — `downstream proof consumer cert stats` is what prints `Axioms: 0` for the
bundle, and `clean check veripb_kernel.lean --json` is what reports
`"sorry_axioms": 0` for the source. `scripts/verify-proofs.sh` gates on all
three.

## The two verifying toolchains

Neither is public. `clean` defaults to the aterm-managed binary; `compiler_consumer`
defaults to a `~/trust` dev stage2 (see `TRUSTC_BIN` in the script for why it
is not yet the installed Trust seal). `--version` strings are useless as
identifiers (`clean 0.9.0`), so `proved-core-expected.txt` records a
**revision** for each binary: the `commit-hash` a Trust seal reports in
`compiler_consumer -vV`, otherwise the `git describe` of the checkout the binary sits in,
together with where it comes from, and every run of
`scripts/verify-proofs.sh` prints the revision it actually used and reports
`TOOLCHAIN DRIFT` when it is not the one the numbers were blessed with.

Override the locations with `CLEAN_BIN` and `TRUSTC_BIN`;
`scripts/verify-proofs.sh --which` prints what they resolved to.

A missing binary is a counted, named `SKIP`. A binary that is present but
**cannot verify anything** — the case that actually happened here, a `compiler_consumer`
whose sysroot was empty mid-rebuild and that answered `E0463: can't find crate
for std` to everything — is reported as `BROKEN` with exit status 2, never as a
rejected proof and never as a pass. Under `--strict` (for a machine that is
supposed to have both) a skip and a drift are both failures.
