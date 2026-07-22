#!/bin/sh
# ay-script: pb26-build
# PB-COMP build script for the AY pseudo-Boolean solver.
#
# Builds the `ay-pb` competition binary from the bundled Rust source and places
# it next to this script as `./ay-pb`, which run.sh invokes. The competition
# build host runs this once before the evaluation.
#
# Layout expected in the submission root:
#   ./build.sh   ./run.sh   ./source/   (Cargo workspace; this repo)
# If ./source is absent, falls back to the repository root two levels up.
set -eu

DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ -d "${DIR}/source" ]; then
    SRC="${DIR}/source"
else
    SRC=$(CDPATH= cd -- "${DIR}/../.." && pwd)
fi

cd "${SRC}"
# Public packages build with the stock Rust toolchain.
BUILD=cargo
if [ -d "${SRC}/vendor" ]; then
    # Packaged (vendored) tree: require a locked, fully offline build. Missing
    # vendor inputs must fail immediately rather than reaching the network.
    "${BUILD}" build -p ay-pb --release --locked --offline
else
    # Developer convenience path (repo checkout, no vendor dir): keep the
    # lenient re-resolve for the routine [patch.unused] reconciliation.
    "${BUILD}" build -p ay-pb --release --locked || "${BUILD}" build -p ay-pb --release
fi
cp "${SRC}/target/release/ay-pb" "${DIR}/ay-pb"
chmod 755 "${DIR}/ay-pb"
echo "built ${DIR}/ay-pb"
