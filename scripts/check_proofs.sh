#!/usr/bin/env bash
# ============================================================================
# check_proofs.sh — run AY over a corpus and put every emitted Alethe proof
#                   through a REAL external checker (carcara).
#
# WHY THIS EXISTS
# ---------------
# On 2026-07-30 AY was found to be emitting INVALID Alethe proofs for
# QF_Datatypes. Two distinct defects, both on an `unsat` answer:
#
#   1. an INVENTED rule name, e.g. `:rule dt_distinct`. There is no such rule
#      in Alethe. carcara reports "unknown rule" and the whole artifact is
#      rejected — it is not a proof, it is an uncheckable string.
#   2. a 134-byte STUB for the vlsat3_* family:
#          (step t0 (cl false) :rule trust)
#          (step t1 (cl (not false)) :rule bool_tautology)
#          (step t2 (cl) :rule th_resolution :premises (t1 t0))
#      i.e. "false holds, because I say so, therefore unsat". A bare assertion.
#
# Neither was caught by anything, because NOTHING IN THE TEST SUITE EVER RAN AN
# ALETHE CHECKER. The solver said `unsat`, a file appeared next to the input,
# every test went green, and the certificate was worthless. Proof emission that
# is never externally checked is not proof emission; it is a file with the right
# extension.
#
# A WRONG PROOF IS WORSE THAN NO PROOF. So:
#   * `invalid` is a HARD FAILURE (non-zero exit). This includes an invented
#     rule name, a `trust` step, and any proof carcara cannot parse.
#   * `holey`  is a WARNING with a count. `hole` is the HONEST escape hatch for
#     a step AY cannot yet justify: the proof's *structure* is checked, the
#     holes are visible and countable, and nobody is lied to. Emit `hole`, never
#     an invented rule name and never `trust`.
#   * `valid`  is the only thing that counts as a pass.
#
# Run this before claiming AY "produces proofs" for any logic.
#
# NOTE ON `--z3-mode`: AY's default-on proof emission is SUPPRESSED by
# --z3-mode (and by --competition / --no-proof). The competition path therefore
# writes no proof at all. This script deliberately runs AY WITHOUT --z3-mode,
# which is the configuration that actually writes <input>.smt2.alethe.
#
# CORPUS HYGIENE: AY writes the proof next to its INPUT. To avoid littering the
# benchmark tree, this script never hands AY the real file — it hands AY a
# symlink inside a private scratch dir, so `<symlink>.alethe` lands in scratch
# and the corpus is untouched. The scratch dir is removed on exit (including on
# Ctrl-C). As a belt-and-braces measure it also deletes any sibling .alethe that
# appeared next to the original during this run and was not there before.
#
# ---------------------------------------------------------------------------
# USAGE
#   scripts/check_proofs.sh [OPTIONS] <corpus-dir | selection.jsonl>
#
# OPTIONS
#   --limit N         check at most N unsat instances (0 = all). Default 0.
#   --timeout SECS    per-instance AY timeout (passed as -T:SECS). Default 20.
#   --checker-timeout SECS   per-proof carcara timeout. Default 60.
#   --bench-root DIR  root that a jsonl `relpath` resolves against.
#                     Default: the path prefix before /selections/, else
#                     <repo>/benchmarks/smtlib-2025.
#   --ay PATH         AY binary. Default $AY_BIN, else <repo>/target/release/ay.
#   --carcara PATH    carcara binary. Default $CARCARA_BIN, else ~/.cargo/bin/
#                     carcara, else `carcara` on PATH.
#   --keep DIR        copy every non-`valid` proof (+ its problem) into DIR for
#                     inspection. Not deleted on exit.
#   --require-proof   also FAIL when AY answers unsat but writes no proof at all.
#                     Off by default (a missing proof is a gap, not a lie).
#   --report-tsv PATH machine-readable per-instance record:
#                     name / verdict / answer / secs / reason / warnings.
#                     Use this instead of scraping the human table. Opens with
#                     `#` provenance lines naming the ay/carcara binaries that
#                     produced it -- a verdict without its solver is not
#                     evidence, and a copied script silently re-points $AY.
#                     Readers must skip leading `#` lines.
#   --max-no-answer-pct N   measurement guard: FAIL (exit 3) when more than N%
#                     of instances produce NO verdict line at all. Default 20.
#                     0 = any no-answer is fatal.
#   --allow-nothing-checked  disable the guard that FAILS a run in which zero
#                     proofs reached carcara.
#   --quiet           suppress the per-instance lines; print only the table.
#   -h, --help        this text.
#
# INPUT SELECTION
#   *.jsonl  — lines with "expected":"unsat" are used; `relpath` is resolved
#              against --bench-root.
#   dir      — *.smt2 under it whose header declares (set-info :status unsat).
#
# EXIT CODES
#   0  no invalid proofs (holey and missing proofs may still be reported)
#   1  at least one INVALID proof, or a wrong answer, or --require-proof unmet
#   2  usage / environment error (no AY, no carcara, no instances)
#   3  MEASUREMENT GUARD tripped -- the run is not evidence either way:
#      zero proofs reached the checker, or too many instances produced no
#      verdict line at all. Distinct from 1 so a caller can tell "AY emitted a
#      bad proof" from "this number means nothing".
#
# SELF-TEST
#   This script is itself under test. scripts/selftest_proof_harness.py runs it
#   over benchmarks/proof-fixtures/, whose expected classification is known in
#   advance, and fails if any instance is misclassified. Run it after touching
#   anything here.
#
# EXAMPLES
#   scripts/check_proofs.sh --limit 20 \
#     benchmarks/smtlib-2025/selections/SingleQuery/QF_Datatypes.jsonl
#   scripts/check_proofs.sh --limit 50 benchmarks/smtlib-2025/non-incremental/QF_UF
# ============================================================================

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

INPUT=""
LIMIT=0
AY_TIMEOUT=20
CARCARA_TIMEOUT=60
BENCH_ROOT=""
AY="${AY_BIN:-}"
CARCARA="${CARCARA_BIN:-}"
KEEP_DIR=""
REQUIRE_PROOF=0
QUIET=0
REPORT_TSV=""
MAX_NO_ANSWER_PCT=20
ALLOW_NOTHING_CHECKED=0

usage() { sed -n '2,/^# ===*$/p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; }

die() { printf 'check_proofs: %s\n' "$*" >&2; exit 2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --limit)            LIMIT="${2:-}";            shift 2 ;;
    --timeout)          AY_TIMEOUT="${2:-}";       shift 2 ;;
    --checker-timeout)  CARCARA_TIMEOUT="${2:-}";  shift 2 ;;
    --bench-root)       BENCH_ROOT="${2:-}";       shift 2 ;;
    --ay)               AY="${2:-}";               shift 2 ;;
    --carcara)          CARCARA="${2:-}";          shift 2 ;;
    --keep)             KEEP_DIR="${2:-}";         shift 2 ;;
    --require-proof)    REQUIRE_PROOF=1;           shift ;;
    --report-tsv)       REPORT_TSV="${2:-}";       shift 2 ;;
    --max-no-answer-pct) MAX_NO_ANSWER_PCT="${2:-}"; shift 2 ;;
    --allow-nothing-checked) ALLOW_NOTHING_CHECKED=1; shift ;;
    --quiet)            QUIET=1;                   shift ;;
    -h|--help)          usage; exit 0 ;;
    -*)                 die "unknown option: $1 (try --help)" ;;
    *)                  [ -n "$INPUT" ] && die "more than one corpus argument"
                        INPUT="$1";                shift ;;
  esac
done

[ -n "$INPUT" ] || { usage >&2; exit 2; }
[ -e "$INPUT" ] || die "no such corpus: $INPUT"

# EVERY path that reaches a work cell must be ABSOLUTE.
#
# The runner does `ln -sf "$src" "$cell/$base"`, and a RELATIVE target resolves
# against the CELL, not the cwd. The link then dangles, AY reads nothing, and
# every instance is classified "no-answer" in 0s -- which used to print
# `RESULT: PASS` over zero checked proofs. That was fixed once, in the .jsonl
# selection reader only; the DIRECTORY branch below feeds `find`'s output
# straight through, so plain `scripts/check_proofs.sh benchmarks/.../ALIA/piVC`
# still reproduced the original incident verbatim (41/41 no-answer) until
# 2026-08-02, when the measurement guard caught it.
#
# Absolutize the corpus argument ONCE, here, so neither branch can regress; the
# loop asserts the invariant again per instance.
case "$INPUT" in
  /*) ;;
  *)  INPUT="$(cd "$(dirname "$INPUT")" 2>/dev/null && printf '%s/%s' "$(pwd)" "$(basename "$INPUT")")" \
        || die "cannot resolve corpus to an absolute path: $INPUT" ;;
esac

# ---- locate the tools -------------------------------------------------------
[ -n "$AY" ] || AY="$REPO_ROOT/target/release/ay"
[ -x "$AY" ] || die "AY binary not found/executable: $AY
  build it with:  cargo build --release -p ay --features cli
  (WITHOUT --features cli only the library builds and target/release/ay stays STALE)"

if [ -z "$CARCARA" ]; then
  if [ -x "$HOME/.cargo/bin/carcara" ]; then CARCARA="$HOME/.cargo/bin/carcara"
  else CARCARA="$(command -v carcara 2>/dev/null || true)"; fi
fi
[ -n "$CARCARA" ] && [ -x "$CARCARA" ] || die "carcara not found (install it or pass --carcara PATH)"

# `ay` must really be the CLI build, not a stale library-only artifact.
"$AY" --version >/dev/null 2>&1 || die "'$AY --version' failed; is this a real CLI build?"

AY_STAMP="$("$AY" --version 2>/dev/null | head -1)"
CARCARA_STAMP="$("$CARCARA" --version 2>/dev/null | head -1)"

# ---- default bench root -----------------------------------------------------
if [ -z "$BENCH_ROOT" ]; then
  case "$INPUT" in
    */selections/*) BENCH_ROOT="${INPUT%%/selections/*}" ;;
    *)              BENCH_ROOT="$REPO_ROOT/benchmarks/smtlib-2025" ;;
  esac
fi

# ---- scratch ----------------------------------------------------------------
WORK="$(mktemp -d "${TMPDIR:-/tmp}/ay-check-proofs.XXXXXX")" || die "mktemp failed"
CREATED_SIBLINGS="$WORK/created_siblings.txt"
: > "$CREATED_SIBLINGS"

cleanup() {
  # Delete only sibling .alethe files that THIS run created next to a corpus
  # file (should be none: AY writes next to the symlink we hand it).
  if [ -s "$CREATED_SIBLINGS" ]; then
    while IFS= read -r f; do [ -n "$f" ] && rm -f "$f"; done < "$CREATED_SIBLINGS"
  fi
  rm -rf "$WORK"
}
trap cleanup EXIT INT TERM

[ -n "$KEEP_DIR" ] && mkdir -p "$KEEP_DIR"

# ---- build the instance list ------------------------------------------------
LIST="$WORK/instances.txt"
: > "$LIST"

case "$INPUT" in
  *.jsonl)
    command -v python3 >/dev/null 2>&1 || die "python3 required to read a .jsonl selection"
    python3 - "$INPUT" "$LIMIT" "$BENCH_ROOT" > "$LIST" <<'PY'
import json, os, sys
sel, limit, root = sys.argv[1], int(sys.argv[2]), sys.argv[3]
seldir = os.path.dirname(os.path.abspath(sel))
n = 0
with open(sel) as fh:
    for line in fh:
        line = line.strip()
        if not line:
            continue
        try:
            d = json.loads(line)
        except json.JSONDecodeError:
            continue
        if str(d.get("expected", "")).lower() != "unsat":
            continue
        rel = d.get("relpath") or d.get("path") or d.get("file")
        if not rel:
            continue
        for cand in (rel if os.path.isabs(rel) else os.path.join(root, rel),
                     os.path.join(seldir, rel),
                     os.path.abspath(rel)):
            if os.path.isfile(cand):
                # MUST be absolute. The runner symlinks this path into a work
                # cell (`ln -sf "$src" "$cell/$base"`), and a relative target
                # resolves against the CELL, not the cwd — producing a dangling
                # symlink that AY reports as "no-answer" in 0s. That reads as
                # "the instance was not unsat" and silently empties the sweep.
                print(os.path.abspath(cand))
                n += 1
                break
        else:
            print("MISSING:" + rel, file=sys.stderr)
        if limit and n >= limit:
            break
PY
    ;;
  *)
    [ -d "$INPUT" ] || die "not a directory and not a .jsonl: $INPUT"
    n=0
    while IFS= read -r f; do
      # honest unsat selection: trust only a declared :status unsat header
      if head -c 4096 "$f" | tr -d '\n' | grep -qE ':status[[:space:]]+unsat'; then
        printf '%s\n' "$f" >> "$LIST"
        n=$((n + 1))
        [ "$LIMIT" -gt 0 ] && [ "$n" -ge "$LIMIT" ] && break
      fi
    done < <(find "$INPUT" -type f -name '*.smt2' | sort)
    ;;
esac

TOTAL=$(wc -l < "$LIST" | tr -d ' ')
[ "$TOTAL" -gt 0 ] || die "no unsat instances found in: $INPUT"

# ---- carcara with a portable watchdog (macOS has no coreutils `timeout`) ----
#
# REASON EXTRACTION -- read this before "simplifying" it.
#
# carcara puts the VERDICT on stdout and its diagnostics on stderr, warnings
# FIRST:
#     stderr: [WARN] `assume` command 'h3' appears after `step` commands
#     stderr: [ERROR] checking failed on step 't2' with rule 'and_neg': ...
#     stdout: invalid
#
# This function used to record `grep -m1 . "$err"` -- the first stderr line --
# which on any such proof is the WARNING. The real ERROR was discarded, and two
# real instances were filed under an "assume-after-step" defect class THAT DOES
# NOT EXIST (both were actually `and_pos`). The harness was right about the
# verdict and wrong about the cause, which is the more expensive failure: it
# invented a bug class and sent work after it.
#
# So: the reason is the first [ERROR]; warnings are kept, separately, and are
# never promoted to a reason (a `valid` proof can carry a [WARN] -- see fixture
# c06 -- and must still report no reason at all).
CC_VERDICT=""
CC_REASON=""
CC_WARN=""
carcara_check() { # $1 = proof, $2 = problem
  local out="$WORK/cc.out" err="$WORK/cc.err" pid wd rc
  : > "$out"; : > "$err"
  "$CARCARA" check "$1" "$2" > "$out" 2> "$err" &
  pid=$!
  ( sleep "$CARCARA_TIMEOUT"; kill -9 "$pid" ) >/dev/null 2>&1 &
  wd=$!
  wait "$pid"; rc=$?
  kill -9 "$wd" >/dev/null 2>&1; wait "$wd" >/dev/null 2>&1
  CC_VERDICT="$(grep -Eo '^(valid|holey|invalid)$' "$out" | tail -1)"

  # warnings: kept, joined, never used as the reason
  CC_WARN="$(grep -E '^\[WARN\]' "$err" | tr '\t' ' ' | tr '\n' '|' | cut -c1-200)"
  CC_WARN="${CC_WARN%|}"
  # reason: the first real ERROR ...
  CC_REASON="$(grep -m1 -E '^\[ERROR\]' "$err" | tr '\t' ' ' | cut -c1-200)"
  if [ -z "$CC_REASON" ]; then
    # ... else the first stderr line that is NOT a warning (panics, signals,
    # linker noise -- anything carcara says that is not an [ERROR] and not a
    # [WARN] is still more informative than a warning) ...
    CC_REASON="$(grep -vE '^\[WARN\]' "$err" | grep -m1 . | tr '\t' ' ' | cut -c1-200)"
  fi
  # ... and if a FAILING proof somehow left nothing but warnings on stderr, say
  # so explicitly rather than quietly presenting a warning as the cause. Note
  # the guard on the verdict: a `valid`/`holey` proof may carry warnings and
  # must report NO reason at all (fixture c06). Attaching a reason to a passing
  # proof is the same lie in the other direction.
  if [ -z "$CC_REASON" ] && [ -n "$CC_WARN" ] \
     && [ "$CC_VERDICT" != "valid" ] && [ "$CC_VERDICT" != "holey" ]; then
    CC_REASON="(no [ERROR] on stderr; warnings only)"
  fi

  if [ -z "$CC_VERDICT" ]; then
    if [ "$rc" -ge 128 ]; then
      CC_VERDICT="checker-timeout"
      [ -n "$CC_REASON" ] || CC_REASON="carcara killed after ${CARCARA_TIMEOUT}s"
    else
      CC_VERDICT="checker-error"
      [ -n "$CC_REASON" ] || CC_REASON="carcara exited $rc with no verdict"
    fi
  fi
}

# ---- counters ---------------------------------------------------------------
N_VALID=0; N_HOLEY=0; N_INVALID=0; N_NOPROOF=0; N_NOTUNSAT=0; N_CCERR=0; N_WRONG=0
N_NOANSWER=0

# machine-readable per-instance record, so callers (and the harness self-test)
# never have to scrape the human table.
#
# PROVENANCE PREAMBLE -- `#` comment lines before the header, naming WHICH
# binaries produced the rows below.
#
# A verdict is meaningless without the solver that produced it, and this file is
# what gets diffed when someone asks "did my change help?". On 2026-08-02 an A/B
# of this very script compared a repo build against a MONTH-OLD frozen `ay` left
# in a scratch dir: $AY defaults to <script dir>/../target/release/ay, so a COPY
# of the script silently re-points it. The two arms disagreed (invalid vs holey)
# and the difference was read as an effect of the change under test. Nothing in
# the TSV could have revealed that -- it records verdicts and no identity.
#
# So every record now carries the binaries it came from. Readers must skip
# leading `#` lines (scripts/selftest_proof_harness.py does, and asserts these
# lines are present and name the binary actually used).
if [ -n "$REPORT_TSV" ]; then
  : > "$REPORT_TSV" || die "cannot write --report-tsv: $REPORT_TSV"
  {
    printf '# ay\t%s\n'        "$AY"
    printf '# ay-build\t%s\n'  "$AY_STAMP"
    printf '# carcara\t%s\t%s\n' "$CARCARA_STAMP" "$CARCARA"
    printf '# corpus\t%s\n'    "$INPUT"
    printf '# started\t%s\n'   "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  } >> "$REPORT_TSV"
  printf 'name\tverdict\tanswer\tsecs\treason\twarnings\n' >> "$REPORT_TSV"
fi
emit_tsv() { # $1 name  $2 verdict  $3 answer  $4 secs  $5 reason  $6 warnings
  [ -n "$REPORT_TSV" ] || return 0
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" "$5" "$6" >> "$REPORT_TSV"
}
INVALID_LIST="$WORK/invalid.txt"; : > "$INVALID_LIST"
HOLEY_LIST="$WORK/holey.txt";     : > "$HOLEY_LIST"
NOPROOF_LIST="$WORK/noproof.txt"; : > "$NOPROOF_LIST"
OTHER_LIST="$WORK/other.txt";     : > "$OTHER_LIST"

say() { [ "$QUIET" -eq 1 ] || printf '%s\n' "$*"; }

[ "$QUIET" -eq 1 ] || {
  printf 'ay      : %s\n' "$AY"
  printf 'build   : %s\n' "$AY_STAMP"
  printf 'carcara : %s (%s)\n' "$CARCARA_STAMP" "$CARCARA"
  printf 'corpus  : %s\n' "$INPUT"
  printf 'instances: %s (unsat-expected%s)\n' "$TOTAL" \
    "$([ "$LIMIT" -gt 0 ] && printf ', --limit %s' "$LIMIT")"
  printf -- '----------------------------------------------------------------\n'
}

# ---- main loop --------------------------------------------------------------
i=0
while IFS= read -r src; do
  [ -n "$src" ] || continue
  # The invariant, restated where it is actually relied on. A relative $src
  # here produces a dangling work-cell symlink and a silently empty sweep, so
  # refuse rather than measure nothing.
  case "$src" in
    /*) ;;
    *)  die "internal: instance path is not absolute: $src
  (a relative path becomes a dangling symlink in the work cell and every
   instance would be silently classified no-answer)" ;;
  esac
  i=$((i + 1))
  base="$(basename "$src")"
  cell="$WORK/case$i"
  mkdir -p "$cell"
  ln -sf "$src" "$cell/$base"            # AY writes <symlink>.alethe -> scratch
  proof="$cell/$base.alethe"
  sibling="$src.alethe"                  # defensive: should never be written
  sib_pre=0; [ -e "$sibling" ] && sib_pre=1

  t0=$(date +%s)
  ay_out="$("$AY" -T:"$AY_TIMEOUT" "$cell/$base" 2>&1)"
  t1=$(date +%s)
  secs=$((t1 - t0))

  [ "$sib_pre" -eq 0 ] && [ -e "$sibling" ] && printf '%s\n' "$sibling" >> "$CREATED_SIBLINGS"

  answer="$(printf '%s\n' "$ay_out" | grep -Eo '^(unsat|sat|unknown|timeout)$' | tail -1)"
  [ -n "$answer" ] || answer="no-answer"

  CC_REASON=""; CC_WARN=""
  if [ "$answer" = "sat" ]; then
    N_WRONG=$((N_WRONG + 1)); verdict="WRONG-ANSWER"
    CC_REASON="AY said sat on an unsat-expected instance"
    printf '%s\t%s\n' "$base" "$CC_REASON" >> "$OTHER_LIST"
  elif [ "$answer" = "no-answer" ]; then
    # NOT an outcome. `sat`/`unsat`/`unknown`/`timeout` are things AY PRINTS;
    # no-answer is the absence of any of them -- a crash, a missing input, a
    # dangling work-cell symlink. It is the signature of the incident where
    # every instance "completed" in 0s and the sweep printed PASS having checked
    # nothing, so it gets its own counter and its own guard below.
    N_NOANSWER=$((N_NOANSWER + 1)); verdict="no-answer"
    CC_REASON="AY produced no verdict line (crash / unreadable input / broken work cell)"
    printf '%s\t%s\n' "$base" "$CC_REASON" >> "$OTHER_LIST"
  elif [ "$answer" != "unsat" ]; then
    N_NOTUNSAT=$((N_NOTUNSAT + 1)); verdict="$answer"
    CC_REASON="$answer (no proof expected)"
    printf '%s\t%s\n' "$base" "$CC_REASON" >> "$OTHER_LIST"
  elif [ ! -s "$proof" ]; then
    N_NOPROOF=$((N_NOPROOF + 1)); verdict="no-proof"
    printf '%s\n' "$base" >> "$NOPROOF_LIST"
  else
    carcara_check "$proof" "$cell/$base"
    verdict="$CC_VERDICT"
    case "$CC_VERDICT" in
      valid)   N_VALID=$((N_VALID + 1)) ;;
      holey)   N_HOLEY=$((N_HOLEY + 1))
               nh=$(grep -c ':rule hole' "$proof" 2>/dev/null || printf 0)
               printf '%s\t%s hole step(s)\n' "$base" "$nh" >> "$HOLEY_LIST" ;;
      invalid) N_INVALID=$((N_INVALID + 1))
               printf '%s\t%s\n' "$base" "$CC_REASON" >> "$INVALID_LIST" ;;
      *)       N_CCERR=$((N_CCERR + 1))
               printf '%s\t%s: %s\n' "$base" "$CC_VERDICT" "$CC_REASON" >> "$OTHER_LIST" ;;
    esac
    if [ -n "$KEEP_DIR" ] && [ "$CC_VERDICT" != "valid" ]; then
      cp "$proof" "$KEEP_DIR/$base.alethe" 2>/dev/null
      cp "$src"   "$KEEP_DIR/$base"        2>/dev/null
    fi
  fi

  emit_tsv "$base" "$verdict" "$answer" "$secs" "$CC_REASON" "$CC_WARN"
  say "$(printf '[%3d/%3d] %-14s %5ds  %s' "$i" "$TOTAL" "$verdict" "$secs" "$base")"
done < "$LIST"

# ---- report -----------------------------------------------------------------
CHECKED=$((N_VALID + N_HOLEY + N_INVALID + N_CCERR))
printf -- '----------------------------------------------------------------\n'
printf '  %-16s %5d   %s\n' "valid"      "$N_VALID"    "PASS - fully checked by carcara"
printf '  %-16s %5d   %s\n' "holey"      "$N_HOLEY"    "WARN - structure ok, some steps are 'hole'"
printf '  %-16s %5d   %s\n' "invalid"    "$N_INVALID"  "FAIL - not a proof (unknown rule / unparseable)"
[ "$N_CCERR"    -gt 0 ] && printf '  %-16s %5d   %s\n' "checker-error" "$N_CCERR"   "FAIL - carcara produced no verdict"
[ "$N_NOPROOF"  -gt 0 ] && printf '  %-16s %5d   %s\n' "no-proof"      "$N_NOPROOF" "$([ "$REQUIRE_PROOF" -eq 1 ] && echo 'FAIL - unsat with no certificate' || echo 'note - unsat but no certificate written')"
[ "$N_NOTUNSAT" -gt 0 ] && printf '  %-16s %5d   %s\n' "not-unsat"     "$N_NOTUNSAT" "skip - unknown/timeout, no proof expected"
[ "$N_NOANSWER" -gt 0 ] && printf '  %-16s %5d   %s\n' "no-answer"     "$N_NOANSWER" "SUSPECT - AY printed no verdict at all"
[ "$N_WRONG"    -gt 0 ] && printf '  %-16s %5d   %s\n' "WRONG-ANSWER"  "$N_WRONG"   "FAIL - sat on an unsat-expected instance"
printf -- '----------------------------------------------------------------\n'
printf '  %-16s %5d   (%d proofs checked)\n' "total" "$TOTAL" "$CHECKED"
# Named even under --quiet, which suppresses the banner: a table of verdicts with
# no solver attached is exactly what made a stale-binary A/B look like a result.
printf '  measured-with    %s\n' "$AY_STAMP"

if [ -s "$INVALID_LIST" ]; then
  printf '\nINVALID proofs (FAILURE - a wrong proof is worse than no proof):\n'
  while IFS="$(printf '\t')" read -r f r; do printf '  %-40s %s\n' "$f" "$r"; done < "$INVALID_LIST"
fi
if [ -s "$HOLEY_LIST" ] && [ "$QUIET" -eq 0 ]; then
  printf '\nholey proofs (warning - honest, but not certified):\n'
  while IFS="$(printf '\t')" read -r f r; do printf '  %-40s %s\n' "$f" "$r"; done < "$HOLEY_LIST"
fi
if [ -s "$NOPROOF_LIST" ] && [ "$QUIET" -eq 0 ]; then
  printf '\nunsat with no proof written:\n'
  while IFS= read -r f; do printf '  %s\n' "$f"; done < "$NOPROOF_LIST"
fi
if [ -s "$OTHER_LIST" ] && [ "$QUIET" -eq 0 ]; then
  printf '\nother:\n'
  while IFS="$(printf '\t')" read -r f r; do printf '  %-40s %s\n' "$f" "$r"; done < "$OTHER_LIST"
fi

RC=0
[ "$N_INVALID" -gt 0 ] && RC=1
[ "$N_CCERR"   -gt 0 ] && RC=1
[ "$N_WRONG"   -gt 0 ] && RC=1
[ "$REQUIRE_PROOF" -eq 1 ] && [ "$N_NOPROOF" -gt 0 ] && RC=1

# ---- DID WE ACTUALLY MEASURE ANYTHING? --------------------------------------
#
# Three times now this harness has reported success while measuring nothing, and
# every time the giveaway was in the numbers it already had: 0 proofs checked, or
# every instance "finished" in 0s with no answer. A run that measured nothing is
# not a pass. It is a failed measurement, and it gets its own exit code (3) so a
# caller can tell "AY emitted a bad proof" from "this number is not evidence".
#
# GUARD 1 -- nothing reached the checker.
#   The single purpose of this script is to put emitted proofs through carcara.
#   If zero proofs got there, the run says nothing about proof emission, however
#   many instances it walked. (A corpus AY genuinely cannot solve is exactly the
#   case where a green PASS would be most misleading.) Override with
#   --allow-nothing-checked when the emptiness is the thing you are probing.
#
# GUARD 2 -- too many instances produced no verdict line at all.
#   `sat` / `unsat` / `unknown` / `timeout` are printed OUTCOMES and are all
#   fine. `no-answer` is the absence of an outcome: a crash, an unreadable
#   input, a dangling symlink in the work cell. A healthy run is at ~0%; the
#   collapse that printed PASS was at 100%. The default threshold is 20% -- an
#   order of magnitude above healthy, still far below any collapse -- and it is
#   a RATE rather than a count so it does not fire on the odd crashed instance
#   in a large sweep. --max-no-answer-pct 0 makes any no-answer fatal.
NO_ANSWER_PCT=$(( N_NOANSWER * 100 / TOTAL ))
MEASURE_FAIL=0

if [ "$CHECKED" -eq 0 ] && [ "$ALLOW_NOTHING_CHECKED" -eq 0 ]; then
  printf '\nMEASUREMENT GUARD: 0 proofs reached carcara out of %d instance(s).\n' "$TOTAL"
  printf '  This run measured NOTHING about proof emission. Not a pass.\n'
  printf '  (%d no-answer, %d not-unsat, %d unsat-with-no-proof)\n' \
    "$N_NOANSWER" "$N_NOTUNSAT" "$N_NOPROOF"
  printf '  Pass --allow-nothing-checked if an empty result is what you are probing.\n'
  MEASURE_FAIL=1
fi

if [ "$N_NOANSWER" -gt 0 ] && [ "$NO_ANSWER_PCT" -gt "$MAX_NO_ANSWER_PCT" ]; then
  printf '\nMEASUREMENT GUARD: %d/%d instance(s) (%d%%) produced no verdict line at all,\n' \
    "$N_NOANSWER" "$TOTAL" "$NO_ANSWER_PCT"
  printf '  over the %d%% limit. That is a broken harness/binary/corpus, not a result.\n' \
    "$MAX_NO_ANSWER_PCT"
  printf '  Check: is the AY binary a real --features cli build? do the work-cell\n'
  printf '  symlinks resolve? is the corpus readable?\n'
  MEASURE_FAIL=1
fi

if [ "$MEASURE_FAIL" -eq 1 ]; then
  printf '\nRESULT: FAIL (measurement not trustworthy)\n'
  exit 3
fi

if [ "$RC" -eq 0 ]; then
  printf '\nRESULT: PASS (0 invalid, %d proof(s) actually checked)%s\n' "$CHECKED" \
    "$([ "$N_HOLEY" -gt 0 ] && printf ' - %d holey proof(s) still uncertified' "$N_HOLEY")"
else
  printf '\nRESULT: FAIL\n'
fi
exit "$RC"
