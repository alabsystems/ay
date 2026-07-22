#!/bin/bash
# ay-script: chccomp-docker-env
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
cd "$ROOT"

echo "Building Docker image ay-chccomp-env..."
docker build -t ay-chccomp-env -f Dockerfile.chccomp .

echo "======================================================================"
echo "Dropping into Docker environment."
echo "The current repository is mounted at /workspace."
echo ""
echo "To build the static Linux binary and package the submission, run:"
echo "  cargo run --bin ay --features=\"cli bench\" -- submission submit chc-comp-zenodo --skip-pr"
echo ""
echo "To run the benchmark harvest (requires benchmarks to be cloned):"
echo "  target/release/ay bench harvest \\"
echo "      --corpus chc-comp-2026 \\"
echo "      --dir benchmarks/chc/chc-comp26-benchmarks \\"
echo "      --solver reference/loat-chc-comp-2025/LoAT/loat_chc_comp.sh \\"
echo "      --timeout 300"
echo "======================================================================"

docker run --rm -it -v "$ROOT:/workspace" ay-chccomp-env
