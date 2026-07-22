#!/usr/bin/env bash
# ay-script: setup-audit-tools
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# setup-audit-tools.sh — install the external checkers/solvers that the
# full-replacement self-audit (`ay z3-audit --scope full-replacement`) replays
# real artifacts against, so an external reviewer can reproduce the audit from a
# clean machine with one command.
#
# These are the exact recipes used to provision this repository's audit run; see
# the "External Tool Inventory" section ay z3-audit prints for live presence.
# Nothing here is faked — each tool is built/installed from its upstream source,
# and `ay z3-audit` independently re-validates a genuine drat-trim (a no-op mock
# is rejected). After running this, put the tools on PATH, e.g.:
#
#   export PATH="/tmp/drat-trim:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
#   ay z3-audit --scope full-replacement
#
# Usage:
#   scripts/setup-audit-tools.sh [--check] [--only <tool>]...
#     --check        Report presence of each tool and exit (no building).
#     --only <tool>  Build only the named tool(s): drat-trim carcara lean
#                    cadical golem. Repeatable. Default: all.
#
# Idempotent: a tool already present at its expected path is left untouched.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORK="${AY_AUDIT_TOOLS_WORK:-/tmp}"
CHECK_ONLY=0
ONLY=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --check) CHECK_ONLY=1; shift ;;
    --only) ONLY+=("$2"); shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

want() {
  [[ ${#ONLY[@]} -eq 0 ]] && return 0
  local t
  for t in "${ONLY[@]}"; do [[ "$t" == "$1" ]] && return 0; done
  return 1
}

have() { command -v "$1" >/dev/null 2>&1 || [[ -x "$2" ]]; }

report() {
  printf '  %-10s %s\n' "$1" "$2"
}

# --- drat-trim (DIMACS DRAT external proof replay) -------------------------
DRAT_BIN="/tmp/drat-trim/drat-trim"
setup_drat_trim() {
  if [[ -x "$DRAT_BIN" ]]; then report drat-trim "present: $DRAT_BIN"; return; fi
  echo "[setup] building drat-trim ..."
  rm -rf "$WORK/drat-trim-build"
  git clone --depth 1 https://github.com/marijnheule/drat-trim "$WORK/drat-trim-build"
  ( cd "$WORK/drat-trim-build" && make )
  mkdir -p /tmp/drat-trim
  cp -f "$WORK/drat-trim-build/drat-trim" "$DRAT_BIN"
  cp -f "$WORK/drat-trim-build/lrat-check" /tmp/drat-trim/lrat-check 2>/dev/null || true
  report drat-trim "built: $DRAT_BIN"
}

# --- carcara (SMT Alethe proof replay) -------------------------------------
CARCARA_BIN="$HOME/.cargo/bin/carcara"
setup_carcara() {
  if [[ -x "$CARCARA_BIN" ]] || command -v carcara >/dev/null 2>&1; then
    report carcara "present"; return
  fi
  echo "[setup] building carcara ..."
  rm -rf "$WORK/carcara-src"
  git clone --depth 1 https://github.com/ufmg-smite/carcara "$WORK/carcara-src"
  ( cd "$WORK/carcara-src" && cargo build --release -p carcara-cli )
  mkdir -p "$HOME/.cargo/bin"
  cp -f "$WORK/carcara-src/target/release/carcara" "$CARCARA_BIN"
  report carcara "built: $CARCARA_BIN"
}

# --- lean (Lean4 proof replay) ---------------------------------------------
LEAN_BIN="$HOME/.elan/bin/lean"
setup_lean() {
  if [[ -x "$LEAN_BIN" ]] || command -v lean >/dev/null 2>&1; then
    report lean "present"; return
  fi
  echo "[setup] installing lean via elan ..."
  curl --proto '=https' --tlsv1.2 -sSf https://elan.lean-lang.org/elan-init.sh -o "$WORK/elan-init.sh"
  sh "$WORK/elan-init.sh" -y --default-toolchain stable
  report lean "installed: $LEAN_BIN"
}

# --- cadical (DIMACS SAT reference solver) ---------------------------------
CADICAL_BIN="$REPO_ROOT/reference/cadical/build/cadical"
setup_cadical() {
  if [[ -x "$CADICAL_BIN" ]]; then report cadical "present: $CADICAL_BIN"; return; fi
  echo "[setup] building cadical ..."
  rm -rf "$WORK/cadical-src"
  git clone --depth 1 https://github.com/arminbiere/cadical "$WORK/cadical-src"
  ( cd "$WORK/cadical-src" && ./configure && make -j4 )
  mkdir -p "$REPO_ROOT/reference/cadical/build"
  cp -f "$WORK/cadical-src/build/cadical" "$CADICAL_BIN"
  report cadical "built: $CADICAL_BIN"
}

# --- golem (+ OpenSMT) (CHC reference solver) ------------------------------
GOLEM_BIN="$HOME/.cargo/bin/golem"
setup_golem() {
  if [[ -x "$GOLEM_BIN" ]] || command -v golem >/dev/null 2>&1; then
    report golem "present"; return
  fi
  echo "[setup] building OpenSMT + golem ..."
  # golem requires OpenSMT and bison >= 3 (macOS ships 2.3; install via brew).
  local bison_prefix=""
  if command -v brew >/dev/null 2>&1; then
    brew install bison >/dev/null 2>&1 || true
    bison_prefix="$(brew --prefix bison 2>/dev/null || true)"
  fi
  [[ -n "$bison_prefix" ]] && export PATH="$bison_prefix/bin:$PATH"
  # OpenSMT: full clone (its CMake uses `git describe`, which needs tags).
  rm -rf "$WORK/opensmt-src" "$WORK/opensmt-install"
  git clone https://github.com/usi-verification-and-security/opensmt "$WORK/opensmt-src"
  ( cd "$WORK/opensmt-src" \
      && cmake -B build -DCMAKE_BUILD_TYPE=Release \
           -DCMAKE_INSTALL_PREFIX="$WORK/opensmt-install" \
           -DBUILD_SHARED_LIBS=OFF -DPACKAGE_TESTS=OFF \
      && cmake --build build -j6 --target install )
  rm -rf "$WORK/golem-src"
  git clone --recursive --depth 1 https://github.com/usi-verification-and-security/golem "$WORK/golem-src"
  ( cd "$WORK/golem-src" \
      && cmake -B build -DCMAKE_BUILD_TYPE=Release \
           -DOpenSMT_DIR="$WORK/opensmt-install/lib/cmake/opensmt" \
      && cmake --build build -j6 )
  mkdir -p "$HOME/.cargo/bin"
  cp -f "$WORK/golem-src/build/golem" "$GOLEM_BIN"
  report golem "built: $GOLEM_BIN"
}

if [[ "$CHECK_ONLY" -eq 1 ]]; then
  echo "External audit tool presence:"
  have z3 z3                  && report z3 "present"        || report z3 "MISSING (package manager / Z3Prover/z3)"
  have drat-trim "$DRAT_BIN"  && report drat-trim "present" || report drat-trim "MISSING"
  have carcara "$CARCARA_BIN" && report carcara "present"   || report carcara "MISSING"
  have lean "$LEAN_BIN"       && report lean "present"      || report lean "MISSING"
  have cadical "$CADICAL_BIN" && report cadical "present"   || report cadical "MISSING"
  have golem "$GOLEM_BIN"     && report golem "present"     || report golem "MISSING"
  echo "(z3 itself is provisioned via your package manager; the rest above.)"
  exit 0
fi

echo "Provisioning external audit tools (idempotent) ..."
want drat-trim && setup_drat_trim
want carcara   && setup_carcara
want lean      && setup_lean
want cadical   && setup_cadical
want golem     && setup_golem
echo "Done. Then: export PATH=\"/tmp/drat-trim:\$HOME/.cargo/bin:\$HOME/.elan/bin:\$PATH\""
echo "Verify with: ay z3-audit --scope full-replacement   (see its External Tool Inventory)"
