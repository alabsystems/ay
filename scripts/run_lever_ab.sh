#!/usr/bin/env bash
# ay-script: run-lever-ab
#
# ONE command that measures all three default-OFF SAT levers and prints a
# FLIP / NO-FLIP verdict per lever with its evidence.
#
#   scripts/run_lever_ab.sh                    # 300 s, 6 workers, all three
#   scripts/run_lever_ab.sh --dry-run          # plan + cost, runs nothing
#   scripts/run_lever_ab.sh --timeout 1500     # the long budget
#   scripts/run_lever_ab.sh --levers bve-giant-raw
#
# WHAT THIS DOES DIFFERENTLY FROM A FULL-400 A/B
#
#   Each lever is swept over ONLY the instances that can reach its flag
#   (scripts/lever_eligibility.py, which reads `p cnf` headers and applies each
#   gate's own arithmetic).  A full-400 arm-vs-base costs ~10 h per lever and
#   most of those rows are byte-identical pairs that add nothing but timing
#   variance.  Targeting the eligible population is not a shortcut; it is what
#   makes the effect visible above the noise.
#
#   BOTH ARMS RUN IN ONE SWEEP.  sweep.py submits every solver on a CNF
#   together, so the pair is measured under the same machine conditions.  This
#   campaign's between-run drift on the full 400 has been measured at +/-8
#   solves -- wider than any effect these levers could produce -- so a base
#   number from one run and an arm number from another is not a measurement.
#
#   DRAT, always.  crates/ay-sat/src/variant.rs:1100-1102 makes the giant
#   raw-BVE route return false under LRAT BEFORE any band check, so an LRAT run
#   would measure base against base and report a guaranteed null.  DRAT is also
#   what the submission runs (competition/prepare_sat26_submission.sh:784).
#
#   THE DRAIN CANNOT EXIT ON AN EMPTY QUEUE.  On 2026-08-25 a
#   `drain --watch` died and left 39 proofs unverified, which silently converts
#   accepted UNSATs into unscored ones.  The loop below is conditioned on a
#   SENTINEL FILE, not on the queue, retries `--requeue-claimed` every pass to
#   recover rows stranded by a killed inner drain, and is followed by a
#   blocking final drain that will not stop while anything is still pending.
#
# WHY THE BUILD IS PART OF THE RUNNER
#
#   On 2026-08-25 target/release/ay was built at 19:12 and all three lever
#   commits landed AFTER it (21:45 / 23:08 / 23:44).  That binary REJECTS all
#   three flags.  Running the measurement against it would have produced three
#   confident nulls.  This script builds into its own CARGO_TARGET_DIR (never
#   target/, which a concurrent sweep may be executing out of) and then PROBES
#   each flag before spending a single solve.

set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO" || exit 1

CORPUS="${AY_LEVER_CORPUS:-$HOME/ay-bench/main2026-full/cnf}"
OUTDIR="${AY_LEVER_OUTDIR:-$HOME/ay-bench/lever-ab}"
LEVER_TARGET="${AY_LEVER_TARGET_DIR:-$HOME/ay-bench/lever-target}"
MANIFEST="${AY_PROOF_MANIFEST_DIR:-$HOME/ay-bench/proof-manifest-lever}"
PROOFS="${AY_PROOF_DIR:-$HOME/ay-bench/proofs-lever}"
STATS="${AY_LEVER_STATS_DIR:-$OUTDIR/stats}"
BIN_DIR="${AY_LEVER_BIN_DIR:-$HOME/ay-bench/bin}"

TIMEOUT=300
WORKERS=6
MEM_MB=6000
CHECKER_TIMEOUT=1800
LEVERS="vivify-converge mode-equiticks-large bve-giant-raw"
DRY_RUN=0
INCLUDE_CONTROL=0
FORCE=0
WRITE_REPO_EVIDENCE=0

usage() {
  sed -n '2,50p' "$0" | sed 's/^# \{0,1\}//'
  cat <<'EOF'

Options:
  --timeout SECONDS     per-instance solve budget (default 300).
                        NOTE: sweep.py's --timeout is SECONDS; the `ay` binary's
                        own -t is MILLISECONDS and -T:<n> is seconds. sweep.py
                        does the conversion.
  --workers N           concurrent solves (default 6)
  --mem-mb N            per-child memory envelope (default 6000)
  --levers "a b c"      subset of: vivify-converge mode-equiticks-large
                        bve-giant-raw
  --include-control     also sweep --sat-large-rephase-walk, which is ALREADY
                        MEASURED NEGATIVE (it loses a solve). A control only --
                        never a flip candidate.
  --checker-timeout S   per-certificate external budget (default 1800)
  --dry-run             print the plan and the cost estimate; run nothing
  --force               skip THIS script's "another sweep is running" refusal.
                        It does NOT get past _oom_guard's exclusive host
                        resource lease, which sweep.py takes and which will
                        refuse anyway. Useful only with --dry-run.
  --write-repo-evidence re-write benchmarks/sat/lever-ab/lever-populations.json
                        in the repo. OFF by default: a measurement run should
                        not dirty the working tree it is measuring, and this
                        campaign's currency rule reads that dirty flag.
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --timeout) TIMEOUT="$2"; shift 2 ;;
    --workers) WORKERS="$2"; shift 2 ;;
    --mem-mb) MEM_MB="$2"; shift 2 ;;
    --levers) LEVERS="$2"; shift 2 ;;
    --checker-timeout) CHECKER_TIMEOUT="$2"; shift 2 ;;
    --include-control) INCLUDE_CONTROL=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    --force) FORCE=1; shift ;;
    --write-repo-evidence) WRITE_REPO_EVIDENCE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage; exit 64 ;;
  esac
done

mkdir -p "$OUTDIR" "$STATS" "$MANIFEST"/{pending,claimed,verdicts} "$PROOFS"
RUNLOG="$OUTDIR/run-lever-ab.log"
say() { printf '%s %s\n' "$(date '+%H:%M:%S')" "$*" | tee -a "$RUNLOG"; }

say "=== lever A/B harness ==="
say "repo HEAD $(git rev-parse --short HEAD) $(git diff --quiet && git diff --cached --quiet && echo clean || echo DIRTY)"
say "corpus $CORPUS   timeout ${TIMEOUT}s   workers $WORKERS   mem ${MEM_MB}MiB"

# ---------------------------------------------------------------------------
# 1. PREFLIGHT
# ---------------------------------------------------------------------------
if [ "$FORCE" -eq 0 ]; then
  RUNNING=$(pgrep -fl "scripts/sweep.py" 2>/dev/null | grep -v "$$" | head -3)
  if [ -n "$RUNNING" ]; then
    say "REFUSING TO START: another sweep is running --"
    printf '%s\n' "$RUNNING" | tee -a "$RUNLOG"
    say "A concurrent sweep makes every timing number here meaningless AND"
    say "would be corrupted by this one. Wait for it."
    say "NOTE: --force only skips THIS check. scripts/_oom_guard.py takes an"
    say "exclusive host resource lease per harness, so sweep.py itself will"
    say "still refuse with 'another AY benchmark harness already owns the host"
    say "resource lease'. There is no way to run these two at once, by design."
    exit 75
  fi
fi

AY_LEVER_BIN="${AY_LEVER_BIN:-$LEVER_TARGET/release/ay}"
build_lever_binary() {
  say "building the lever binary into $LEVER_TARGET (NEVER into $REPO/target,"
  say "which a concurrent sweep may be executing out of)"
  CARGO_TARGET_DIR="$LEVER_TARGET" \
    nice -n 5 cargo build --release -p ay --bin ay --features cli 2>&1 \
    | tail -20 | tee -a "$RUNLOG"
  return "${PIPESTATUS[0]}"
}

FLAGS_TO_PROBE="--sat-vivify-converge --sat-mode-equiticks-large --sat-bve-giant-raw"
[ "$INCLUDE_CONTROL" -eq 1 ] && FLAGS_TO_PROBE="$FLAGS_TO_PROBE --sat-large-rephase-walk"

probe_flags() {
  # A binary that predates a lever commit REJECTS its flag, and the resulting
  # A/B would be base against base -- a confident, wrong null. Probe on a
  # 2-clause CNF so this costs nothing.
  local probe="${TMPDIR:-/tmp}/ay-lever-probe.$$.cnf"
  printf 'p cnf 2 2\n1 2 0\n-1 2 0\n' > "$probe"
  local bad=0
  for f in $FLAGS_TO_PROBE; do
    if "$AY_LEVER_BIN" solve --competition --no-proof "$f" true "$probe" 2>&1 \
        | grep -q "unexpected argument"; then
      say "  FLAG MISSING: $f is not compiled into $AY_LEVER_BIN"
      bad=1
    else
      say "  flag ok: $f"
    fi
  done
  rm -f "$probe"
  return $bad
}

if [ "$DRY_RUN" -eq 0 ]; then
  if [ ! -x "$AY_LEVER_BIN" ] || ! probe_flags; then
    build_lever_binary || { say "BUILD FAILED"; exit 1; }
    if ! probe_flags; then
      say "ABORT: the freshly built binary still rejects a lever flag. Either"
      say "HEAD does not contain the lever commits (05d1b59745 / 8776347a35 /"
      say "3ee1ae5497) or the flag names changed. Measuring now would report a"
      say "guaranteed null."
      exit 1
    fi
  fi
  export AY_LEVER_BIN
  say "lever binary: $AY_LEVER_BIN"
  "$AY_LEVER_BIN" --version 2>&1 | head -1 | tee -a "$RUNLOG"
fi

export AY_PROOF_DIR="$PROOFS"
export AY_PROOF_MANIFEST_DIR="$MANIFEST"
export AY_LEVER_STATS_DIR="$STATS"

# ---------------------------------------------------------------------------
# 2. ELIGIBLE POPULATIONS
# ---------------------------------------------------------------------------
say "computing eligible populations (header-only reads over $CORPUS)"
# --scan-binary is a full-file read of the ~37 giant-band candidates (~2.7 GB,
# ~2 min). It cannot shrink a population -- it only reports how many in-band
# instances the Default->Probe/Aggressive auto-router steals, which is the
# dilution the giant raw-BVE null would otherwise be blamed on.
REPO_EVIDENCE=""
[ "$WRITE_REPO_EVIDENCE" -eq 1 ] && \
  REPO_EVIDENCE="--json-out $REPO/benchmarks/sat/lever-ab/lever-populations.json"
# shellcheck disable=SC2086
python3 scripts/lever_eligibility.py \
  --corpus "$CORPUS" --timeout "$TIMEOUT" --workers "$WORKERS" \
  --outdir "$OUTDIR" --scan-binary $REPO_EVIDENCE \
  2>&1 | tee -a "$RUNLOG"

if [ "$DRY_RUN" -eq 1 ]; then
  say "--dry-run: stopping before any solve. The wall-clock estimate above is"
  say "the honest cost of the real run."
  exit 0
fi

# ---------------------------------------------------------------------------
# 3. THE DRAIN -- a loop that CANNOT exit when the queue empties
# ---------------------------------------------------------------------------
SENTINEL="$OUTDIR/.drain-active.$$"
DRAINLOG="$OUTDIR/drain.log"
: > "$SENTINEL"
(
  while [ -e "$SENTINEL" ]; do
    # --requeue-claimed each pass: a drain that was itself killed leaves rows
    # stranded in claimed/, and nothing else ever returns them. `|| true` so a
    # crashing checker cannot end the loop -- the loop's life is the sentinel.
    python3 scripts/verify_proof_manifest.py drain \
      --manifest "$MANIFEST" --timeout "$CHECKER_TIMEOUT" --requeue-claimed \
      >> "$DRAINLOG" 2>&1 || true
    sleep 15
  done
) &
DRAIN_PID=$!
cleanup() { rm -f "$SENTINEL"; kill "$DRAIN_PID" 2>/dev/null; }
trap cleanup EXIT INT TERM
say "background drain started (pid $DRAIN_PID) -> $DRAINLOG"

# ---------------------------------------------------------------------------
# 4. ONE PAIRED SWEEP PER LEVER
# ---------------------------------------------------------------------------
# A case, not an associative array: /usr/bin/env bash on this machine is 3.2,
# where `declare -A` does not exist.
arm_of() {
  case "$1" in
    vivify-converge)      echo vivify ;;
    mode-equiticks-large) echo equiticks ;;
    bve-giant-raw)        echo bvegiant ;;
    large-rephase-walk)   echo rephasewalk ;;
    *)                    echo "" ;;
  esac
}
[ "$INCLUDE_CONTROL" -eq 1 ] && LEVERS="$LEVERS large-rephase-walk"

RC_TOTAL=0
for lever in $LEVERS; do
  arm="$(arm_of "$lever")"
  if [ -z "$arm" ]; then say "unknown lever: $lever"; RC_TOTAL=64; continue; fi
  list="$OUTDIR/lever-$lever.list"
  if [ ! -s "$list" ]; then
    say "SKIP $lever: eligible population is EMPTY ($list). A lever that can"
    say "fire on no corpus instance is not worth shipping, whatever its witness"
    say "showed."
    continue
  fi
  n=$(wc -l < "$list" | tr -d ' ')
  out="$OUTDIR/ab-$lever-${TIMEOUT}s.json"
  say "--- $lever: $n instance(s) x 2 arms, paired within one sweep -> $out"
  python3 scripts/sweep.py \
    --list "$list" --timeout "$TIMEOUT" --workers "$WORKERS" --mem-mb "$MEM_MB" \
    --proof-mode --phantom-memout-frac 0.5 \
    --solver "ay-base=$BIN_DIR/ay-lever-base" \
    --solver "ay-$arm=$BIN_DIR/ay-lever-$arm" \
    --out "$out" 2>&1 | tee -a "$RUNLOG"
  [ "${PIPESTATUS[0]}" -eq 0 ] || RC_TOTAL=1
done

# ---------------------------------------------------------------------------
# 5. FINAL BLOCKING DRAIN -- nothing is scored until the queue is genuinely dry
# ---------------------------------------------------------------------------
rm -f "$SENTINEL"
wait "$DRAIN_PID" 2>/dev/null
trap - EXIT INT TERM
say "sweeps done; draining the remaining certificates to empty"
pass=0
while :; do
  pass=$((pass + 1))
  python3 scripts/verify_proof_manifest.py drain \
    --manifest "$MANIFEST" --timeout "$CHECKER_TIMEOUT" --requeue-claimed \
    2>&1 | tail -3 | tee -a "$RUNLOG"
  left=$(( $(ls "$MANIFEST"/pending/*.json 2>/dev/null | wc -l) \
         + $(ls "$MANIFEST"/claimed/*.json 2>/dev/null | wc -l) ))
  say "drain pass $pass: $left row(s) still queued"
  [ "$left" -eq 0 ] && break
  if [ "$pass" -ge 20 ]; then
    say "### $left CERTIFICATE(S) COULD NOT BE DRAINED after $pass passes."
    say "### Every UNSAT behind them is UNSCORED, not accepted. The verdicts"
    say "### below are incomplete and must not be quoted as a flip decision."
    RC_TOTAL=3
    break
  fi
done
python3 scripts/verify_proof_manifest.py status --manifest "$MANIFEST" \
  2>&1 | tee -a "$RUNLOG"

# ---------------------------------------------------------------------------
# 6. VERDICTS
# ---------------------------------------------------------------------------
say ""
say "================= FLIP / NO-FLIP VERDICTS ================="
for lever in $LEVERS; do
  arm="$(arm_of "$lever")"
  out="$OUTDIR/ab-$lever-${TIMEOUT}s.json"
  [ -s "$out" ] || continue
  say ""
  python3 scripts/lever_ab_verdict.py \
    --sweep "$out" --lever "$lever" \
    --base-solver ay-base --arm-solver "ay-$arm" \
    --base-arm base --arm "$arm" \
    --manifest "$MANIFEST" --stats-dir "$STATS" \
    --out "$OUTDIR/verdict-$lever-${TIMEOUT}s.json" 2>&1 | tee -a "$RUNLOG"
  rc=${PIPESTATUS[0]}
  [ "$rc" -eq 2 ] && RC_TOTAL=2
  [ "$rc" -eq 3 ] && [ "$RC_TOTAL" -eq 0 ] && RC_TOTAL=3
done

# Reclaim AY's orphaned proof-staging entries (a SIGKILLed run leaves them; on
# 2026-08-25, 544 GB of them had accumulated in ~/ay-bench/proofs).
python3 scripts/verify_proof_manifest.py gc --proof-dir "$PROOFS" --age-hours 1 --apply \
  2>&1 | tail -3 | tee -a "$RUNLOG"

say ""
say "artifacts in $OUTDIR:"
say "  ab-<lever>-${TIMEOUT}s.json       paired sweep rows"
say "  verdict-<lever>-${TIMEOUT}s.json  the flip decision and its evidence"
say "  lever-populations.json            eligible populations + over-approximations"
say "  stats/                            per-run counters (preprocess_ms, viv_pp_*)"
say "exit $RC_TOTAL  (0 ok, 2 SOUNDNESS ALARM, 3 undrained certificates)"
exit "$RC_TOTAL"
