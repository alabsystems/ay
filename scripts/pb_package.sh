#!/bin/sh
# ay-script: pb-package
# Build a PB-COMP submission tarball from the current git HEAD.
#
# The competition package layout (verified against prior uploads) is:
#   ./build.sh ./run.sh ./solver_description.txt ./COMMIT.txt ./source/<workspace>
# where source/ is a `git archive HEAD` snapshot (tracked files only — this
# auto-excludes target/, local worktrees, and the heavy untracked benchmark
# corpus, while keeping the small tracked benchmarks). The competition host runs
# build.sh once to compile ./ay-pb from source/, then run.sh per instance.
#
# Usage:
#   scripts/pb_package.sh <version> [note]
# e.g.
#   scripts/pb_package.sh 2026-06-27d "adds DEC-gated parallel portfolio"
#
# Output: ~/pbcomp-work/submission/ay-pbcomp26-<version>.tar.gz  (+ sha256, size)
set -eu

VERSION=${1:?usage: pb_package.sh <version> [note]}
NOTE=${2:-}

REPO=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
OUTDIR=${PB_PACKAGE_OUTDIR:-"$HOME/pbcomp-work/submission"}
OUT="$OUTDIR/ay-pbcomp26-$VERSION.tar.gz"
HEAD=$(cd "$REPO" && git rev-parse HEAD)

# Refuse to package a dirty tree: the package must correspond to a committed,
# pushed state so COMMIT.txt's hash is meaningful and reproducible.
if [ -n "$(cd "$REPO" && git status --porcelain)" ]; then
    echo "ERROR: working tree is dirty; commit before packaging (COMMIT.txt must match HEAD)." >&2
    exit 1
fi

STAGE=$(mktemp -d)
trap 'rm -rf "$STAGE"' EXIT
mkdir -p "$STAGE/source" "$OUTDIR"

# source/ = tracked files at HEAD.
(cd "$REPO" && git archive --format=tar HEAD) | tar -x -C "$STAGE/source"

# Root harness files (the competition invokes these directly).
cp "$REPO/competition/pb/build.sh" "$STAGE/build.sh"
cp "$REPO/competition/pb/run.sh" "$STAGE/run.sh"
cp "$REPO/competition/pb/solver_description.txt" "$STAGE/solver_description.txt"
chmod 755 "$STAGE/build.sh" "$STAGE/run.sh"

# COMMIT.txt provenance.
{
    echo "HEAD: $HEAD"
    echo "Built: $VERSION"
    if [ -n "$NOTE" ]; then echo "$NOTE"; fi
} > "$STAGE/COMMIT.txt"

# Deterministic-ish tar (sorted entries) for reproducibility.
(cd "$STAGE" && tar czf "$OUT" ./)

echo "packaged: $OUT"
echo "size:     $(wc -c < "$OUT") bytes"
echo "sha256:   $( (shasum -a 256 "$OUT" 2>/dev/null || sha256sum "$OUT") | awk '{print $1}')"
echo "HEAD:     $HEAD"
