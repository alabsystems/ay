#!/usr/bin/env bash
# ay-script: mc2026-build
# Copyright 2026 Andrew Yates
# Model Counting Competition build script (SoSy-Lab competition-scripts
# convention): builds the AY exact counter + the FlowCutter TD helper.
set -euo pipefail

cd "$(dirname "$0")/../.."

# 1. AY solver (release, CLI feature set).
cargo build --release -p ay --features cli --bin ay

# 2. FlowCutter (PACE-17) — tree-decomposition helper used for TD-guided
#    branching. Anytime heuristic; prints its best decomposition on SIGTERM.
if [ ! -x target/release/flow_cutter_pace17 ]; then
    rm -rf target/flow-cutter-pace17
    git clone --depth 1 https://github.com/kit-algo/flow-cutter-pace17 \
        target/flow-cutter-pace17
    (cd target/flow-cutter-pace17 && bash build.sh) ||
        (cd target/flow-cutter-pace17 && g++ -O3 -std=c++11 -o flow_cutter_pace17 src/*.cpp)
    cp target/flow-cutter-pace17/flow_cutter_pace17 target/release/
fi

echo "build complete: target/release/ay (+ flow_cutter_pace17)"
