#!/bin/bash
# land.sh — build, gate, and push the current branch, running ONLY the gates
# the diff actually touches. Run BY HAND; this is not a hook and must never
# become one (repo policy: all gates are manual).
#
# WHY THIS EXISTS. On 2026-08-29 seventeen commits — including fixes for FOUR
# certificates the pinned checker rejected — sat unpushed for hours because the
# informal landing procedure was "all five gates on a quiet box", and the box
# was never quiet (the same session kept launching the load). A soundness fix
# was held hostage by contention its own author created. The bar this script
# encodes instead: the gates RELEVANT TO THE DIFF, run promptly, push
# immediately on green.
#
# Hard-won rules encoded here (each one bit this repo at least once):
#   * Exit codes are captured on their own line into $OUT/status — NEVER read a
#     pipeline's exit code as a command's (`cmd | tail` reports tail's).
#   * Exit 2 from a gate is SETUP — neither pass nor fail. We wait and retry,
#     bounded, and report SETUP honestly if the window never comes. Never
#     --allow-busy.
#   * A gate whose log is EMPTY did not run; that is SETUP, not a pass.
#   * macOS bash 3.2: no `declare -A`, no `timeout` binary.
#   * Gate selection is by diff paths, and UNKNOWN paths select ALL gates —
#     fail closed, not open.
set -u
cd "$(git rev-parse --show-toplevel)" || exit 3

OUT="${LAND_OUT:-/tmp/land-$$}"; mkdir -p "$OUT"
BASE="${LAND_BASE:-origin/main}"
RETRIES="${LAND_RETRIES:-20}"        # x 45s = ~15 min of waiting for quiet, max
note() { printf '%s\n' "$*"; }
mark() { printf '%s\n' "$*" >> "$OUT/status"; }

git fetch origin -q || { note "fetch failed"; exit 3; }
AHEAD=$(git log --oneline "$BASE"..HEAD | wc -l | tr -d ' ')
[ "$AHEAD" = "0" ] && { note "nothing to land"; exit 0; }
if ! git diff --quiet || ! git diff --cached --quiet; then
  note "REFUSING: working tree is dirty; commit or stash first."; exit 3
fi

# ---- which gates does this diff need? --------------------------------------
CHANGED=$(git diff --name-only "$BASE"...HEAD)
NEED_PB=0; NEED_MILP=0; NEED_OTHER=0
while IFS= read -r f; do
  case "$f" in
    crates/ay-pb*|crates/ay/src/cmd_pb*|ci/veripb*|ci/cert-instances/*) NEED_PB=1 ;;
    crates/ay-milp/*|scripts/milp_*|.milp_*) NEED_MILP=1 ;;
    reports/*|designs/*|docs/*|census/*|*.md) : ;;              # prose: no gate
    scripts/*) : ;;                                             # harnesses: no solver gate
    *) NEED_OTHER=1 ;;                                          # unknown => everything
  esac
done <<EOF
$CHANGED
EOF
if [ "$NEED_OTHER" = "1" ]; then NEED_PB=1; NEED_MILP=1; fi
note "diff touches: pb=$NEED_PB milp=$NEED_MILP (unknown-paths=>all: $NEED_OTHER)"

# ---- builds (always; verify the feature set that builds each artifact) -----
run_logged() { # name, then command...
  _name=$1; shift
  "$@" > "$OUT/$_name.log" 2>&1
  _rc=$?
  [ -s "$OUT/$_name.log" ] || { mark "$_name=SETUP(empty-log)"; return 2; }
  mark "$_name=$_rc"; return $_rc
}
run_logged build-default cargo build --release --workspace --exclude ay || exit 4
# `-p ay` default features once shipped clean while `--features cli` had seven
# errors; the CLI claim needs the CLI's own feature set.
run_logged build-cli cargo build --release -p ay --features cli || exit 4

# ---- gates, with SETUP-aware retry -----------------------------------------
quiet_wait() { # wait for load < 0.35*ncpu and no foreign cargo, bounded
  i=0
  while [ $i -lt "$RETRIES" ]; do
    LOAD_OK=$(uptime | sed 's/.*averages*: //' | awk -v n="$(sysctl -n hw.ncpu)" '{print ($1 < 0.35*n) ? 1 : 0}')
    if [ "$LOAD_OK" = "1" ] && ! pgrep -q '[c]argo'; then return 0; fi
    sleep 45; i=$((i+1))
  done
  return 1
}
gate() { # name, then command...; retries on exit 2
  _name=$1; shift
  i=0
  while :; do
    "$@" > "$OUT/$_name.log" 2>&1
    _rc=$?
    [ -s "$OUT/$_name.log" ] || _rc=2
    if [ $_rc -ne 2 ]; then mark "$_name=$_rc"; return $_rc; fi
    i=$((i+1))
    [ $i -ge 3 ] && { mark "$_name=SETUP"; return 2; }
    note "$_name: SETUP, waiting for a quiet window ($i/3)..."
    quiet_wait || { mark "$_name=SETUP(no-window)"; return 2; }
  done
}

FAILED=0; SETUPS=0
if [ "$NEED_PB" = "1" ]; then
  gate pb-certified bash scripts/ci/pb_certified_gate.sh
  case $? in 0) : ;; 2) SETUPS=1 ;; *) FAILED=1 ;; esac
  gate pb-core-tests cargo test -p ay-pb-core --release
  case $? in 0) : ;; 2) SETUPS=1 ;; *) FAILED=1 ;; esac
fi
if [ "$NEED_MILP" = "1" ]; then
  gate milp-node python3 scripts/milp_node_gate.py --check --tier all
  case $? in 0) : ;; 2) SETUPS=1 ;; *) FAILED=1 ;; esac
  gate milp-corpus python3 scripts/corpus_guard.py --check
  case $? in 0) : ;; 2) SETUPS=1 ;; *) FAILED=1 ;; esac
  gate milp-rim ./target/release/examples/milp_rim_gate --check --tier fast
  case $? in 0) : ;; 2) SETUPS=1 ;; *) FAILED=1 ;; esac
  gate milp-tests cargo test -p ay-milp --release
  case $? in 0) : ;; 2) SETUPS=1 ;; *) FAILED=1 ;; esac
fi

note "---- status ----"; cat "$OUT/status"
[ "$FAILED" = "1" ] && { note "A GATE FAILED — the failure is the finding. Not pushing."; exit 1; }
[ "$SETUPS" = "1" ] && { note "A gate never got a window (SETUP). Not pushing; re-run land.sh."; exit 2; }

# ---- push, tolerating a race with sibling sessions -------------------------
i=0
while [ $i -lt 3 ]; do
  git fetch origin -q
  BEHIND=$(git log --oneline HEAD..origin/main | wc -l | tr -d ' ')
  if [ "$BEHIND" != "0" ]; then
    OVERLAP=$(comm -12 <(git diff --name-only HEAD...origin/main | sort) \
                       <(git diff --name-only origin/main...HEAD | sort) | wc -l | tr -d ' ')
    note "remote moved ($BEHIND commits, overlap=$OVERLAP files); merging"
    git merge --no-edit origin/main > "$OUT/merge.log" 2>&1 || {
      note "MERGE CONFLICT — resolve by hand; gates must re-run if the resolution touches gated code."
      exit 5
    }
    if [ "$OVERLAP" != "0" ]; then
      note "overlap with incoming commits — re-run land.sh so gates cover the merged tree."
      exit 2
    fi
  fi
  if git push origin HEAD:main > "$OUT/push.log" 2>&1; then
    note "PUSHED: $(git log --oneline -1 | cut -c1-70)"; exit 0
  fi
  i=$((i+1)); sleep 5
done
note "push failed 3x; see $OUT/push.log"; exit 6
