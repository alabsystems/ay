#!/bin/bash
# Run ONE SMT-COMP 2025 division to a defensible, scoreable result on a worker host.
#
# The campaign has repeatedly lost measurements to preventable conditions. This
# script encodes every one of them as a precondition, because each has already
# cost a run:
#
#   * dirty binary      — a scored row must be traceable to an exact commit
#   * noisy host        — 207 orphaned solvers once drove load to 310 and made a
#                         healthy binary look like a capability regression
#                         (wall 1195s / cpu 48s); the instance solved in 649s once
#                         it actually got a CPU
#   * unenforced memory — the banked SQ QF_Datatypes win solved an instance at
#                         9,477 MB under a declared 6,954 MB envelope, because
#                         --memory was an ignored hint until 2026-08-04
#   * mixed invocations — one invocation, one tag, one binary is what made the
#                         banked run defensible in the first place
#
# Usage:
#   scripts/run_division_on_worker.sh <track> <division> <tag> [--competition]
# e.g.
#   scripts/run_division_on_worker.sh sq QF_Datatypes sqdt-worker1-20260818 --competition
#
# Tracks: sq | uc | mv | inc.  --competition sheds the proof cycle; it is
# in-rules for tracks that do not require proof output, and it is what rescues
# certification-overhead timeouts. Omit it to measure certified-mode cost.
set -euo pipefail
cd "$(dirname "$0")/.."

TRACK=${1:?track (sq|uc|mv|inc)}
DIVISION=${2:?division, e.g. QF_Datatypes}
TAG=${3:?tag, e.g. sqdt-worker1-20260818}
shift 3
EXTRA=("$@")

say() { printf '\n=== %s\n' "$*"; }

say "PRECONDITION 1/5 — clean working tree"
if [ -n "$(git status --porcelain)" ]; then
  echo "REFUSING: tree is dirty. A scored row must name an exact commit." >&2
  git status --porcelain | head -10 >&2
  echo "Hint: test scratch such as benchmarks/sat/**/.ay-dimacs-proof-* is safe to delete." >&2
  exit 1
fi
COMMIT=$(git rev-parse --short HEAD)
echo "commit $COMMIT"

say "PRECONDITION 2/5 — build the CLI (the lib-only build silently skips the binary)"
nice -n 19 cargo build --release -p ay --features cli -j "$(( $(sysctl -n hw.ncpu 2>/dev/null || nproc) - 2 ))"
VER=$(./target/release/ay --version | head -1)
echo "$VER"
case "$VER" in
  *dirty*) echo "REFUSING: binary is stamped dirty despite a clean tree." >&2; exit 1;;
esac

say "PRECONDITION 3/5 — reap orphaned solvers"
scripts/reap_orphan_solvers.sh --kill || true

say "PRECONDITION 4/5 — quiet host"
LOAD=$(uptime | sed 's/.*averages*: *//' | awk '{print int($1)}')
CORES=$(sysctl -n hw.ncpu 2>/dev/null || nproc)
echo "load ${LOAD}, cores ${CORES}"
if [ "$LOAD" -gt "$CORES" ]; then
  echo "REFUSING: load ${LOAD} exceeds ${CORES} cores. A starved run reads as a" >&2
  echo "capability regression and is not scoreable. Wait, or find the noise with:" >&2
  echo "  ps aux | sort -k3 -rn | head" >&2
  exit 1
fi

say "PRECONDITION 5/5 — corpus present"
if [ ! -d benchmarks/smtlib-2025 ]; then
  echo "REFUSING: benchmarks/smtlib-2025 is missing (see scripts/fetch_smtlib2025_corpus.py)." >&2
  exit 1
fi

say "RUN — one invocation, one tag, jobs=1 (memlimit is derived from --jobs)"
set -x
python3 scripts/smtcomp_harness.py run \
  --track "$TRACK" --division "$DIVISION" --solvers ay \
  --timeout 1200 --jobs 1 --tag "$TAG" "${EXTRA[@]}"
set +x

say "POST — reap again, then score"
scripts/reap_orphan_solvers.sh --kill || true
case "$TRACK" in
  mv) echo "MV needs Dolmen validation before scoring:"
      echo "  python3 scripts/smtcomp_harness.py validate-mv --division $DIVISION --tag $TAG --jobs 2" ;;
  uc) echo "UC needs core validation before scoring:"
      echo "  python3 scripts/smtcomp_harness.py validate-uc --division $DIVISION --tag $TAG --jobs 2" ;;
esac
python3 scripts/smtcomp_harness.py score --track "$TRACK" --division "$DIVISION" --tag "$TAG" || true

say "AUDIT — starved rows and envelope compliance (both must be zero)"
python3 - "$TRACK" "$DIVISION" "$TAG" <<'PY'
import json, sys, os, collections
track, div, tag = sys.argv[1:4]
p = f"evals/results/smtcomp-2025/{track}/{div}/{tag}/ay.jsonl"
if not os.path.exists(p):
    print("no rows"); raise SystemExit
rs = [json.loads(l) for l in open(p)]
c = collections.Counter(r.get("answer") for r in rs)
starved = [r for r in rs if (r.get("wall_sec") or 0) > 60
           and (r.get("cpu_sec") or 0) < 0.6 * (r.get("wall_sec") or 1)]
lim = next((r.get("memlimit_mb") for r in rs if r.get("memlimit_mb")), None)
over = [r for r in rs if lim and (r.get("peak_rss_mb") or 0) > lim]
print(f"rows {len(rs)} · {dict(c)}")
print(f"CPU-starved rows: {len(starved)}  <- must be 0, else the run is contaminated")
print(f"over-envelope rows: {len(over)} (limit {lim} MB)  <- must be 0")
for r in starved[:5]:
    print(f"   starved {r['instance'].split('/')[-1][:44]} wall={r.get('wall_sec'):.0f} cpu={r.get('cpu_sec'):.0f}")
PY
