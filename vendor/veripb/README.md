# VeriPB checking libraries in AY

This source cohort is maintained as part of AY's proof checker. The public
entrypoint is `ay check veripb`; this is not a separately
released ALab product.

The upstream project is [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB),
by Andy Oertel and its contributors, licensed under MIT OR Apache-2.0. Both
license texts and the original crate boundaries are retained here. The imported
cohort has tree `6cf06892dd8bc8c2520abb07efc56cb0769f1a6d` and includes the
maintained ALab soundness fixes, checker, parsers, rules, propagator, second
reader and kernel. Local integration changes must preserve their regressions.

The standalone frontend and its test targets remain reference and regression
tools for this source cohort. AY's public package must use the in-process
libraries and must not require a sibling checkout or a separately installed
VeriPB executable. Kernel cross-checking is a separate, explicitly qualified
claim; its presence does not establish complete kernel coverage.

AY's MaxSAT certificate lane runs `ay check veripb` from its own executable,
under the existing process-group, output, deadline and RSS supervision. It
does not search for an external checker. Development reference checks retain
their separately pinned checker to preserve an independent oracle.

The typed report distinguishes checked bounds, unproved assertions, weakened
guarantees, no conclusion, and FILE versus IMPLICIT output claims. AY refuses
to certify a supplied output file if the proof never checked that file. No
verdict is released before the entire derivation and elaboration complete.
AY also requires strict input header counts and the default input/output path
checks. The typed report records bypassed input checks, which cannot satisfy
its fully verified predicate; the reference frontend retains its legacy modes.

Run the cohort's regressions from this directory with
`targo --unverified test --release --workspace --features reference-cli`.
The existing corpus contains both proof dialects and all imported negative
fixtures. Its optional CakePB calls are additional reference checks; an
unavailable CakePB is not evidence of an independent pass. The six tests
that only checked the old standalone README/CHANGELOG's prose were removed
with those documents; the executable soundness regressions remain.

The [format overview](proof_format_overview.md), grammar,
and proved-core reference accompany the imported source.
The latter describes historical measurements, not qualification of this AY
build. In the AY development checkout, `scripts/verify-proofs.sh --strict`
retains the historical measurement gates and chooses managed tools on PATH;
missing tools or identity drift refuse. That compiler-specific harness is
excluded from the public stock-Rust snapshot. Mathematical source,
certificates, manifests and synchronization tests remain available for replay.
