#!/usr/bin/env bash
# ay-script: unsat-cert-census
# unsat_cert_census.sh — run the UNSAT-certification census over a corpus.
#
# One process per `.smt2` file, `ay solve --no-proof -T:10`, bounded
# parallelism, a hard per-file wall enforced by `perl -e 'alarm'` (this box has
# no `timeout(1)`). `--no-proof` is LOAD-BEARING: the default synthesises an
# artifact path that disables the independent rescue lanes and silently changes
# what the census measures.
#
# The census rows themselves come from a TEMPORARY, env-gated probe
# (`AY_CENSUS=1`) in the strict-check rejection path
# (`executor/unsat_cert/certification_source.rs`), which is removed before the
# census is committed. Without that probe this harness still produces the
# verdict/exit-code ledger, which is what makes a re-run comparable.
#
# Usage:
#   scripts/unsat_cert_census.sh --list FILE --out DIR [--jobs N] [--wall S]
#                                [--ay PATH]
#
#   --list <F>   file of newline-separated .smt2 paths (one per line)
#   --out <D>    output directory; per-file `<key>.out` / `<key>.err`, plus
#                `files.txt` (the key set this run OWNS — never glob the dir,
#                another session's census has contaminated shared scratch
#                twice) and `ledger.tsv` (exit code, wall seconds, verdict).
#   --jobs <N>   parallel processes (default 8)
#   --wall <S>   hard per-file kill in seconds (default 30). A kill is a WALL,
#                not a verdict: it is recorded as exit 142 and excluded from
#                every verdict aggregate.
#   --ay <P>     solver binary (default target/release/ay)
set -euo pipefail

LIST=""
OUT=""
JOBS=8
WALL=30
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
AY="$ROOT/target/release/ay"

usage() { sed -n '2,30p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; }

while [ "$#" -gt 0 ]; do
  case "$1" in
    --list) LIST="${2:-}"; shift 2 ;;
    --out) OUT="${2:-}"; shift 2 ;;
    --jobs) JOBS="${2:-}"; shift 2 ;;
    --wall) WALL="${2:-}"; shift 2 ;;
    --ay) AY="${2:-}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "error: unknown argument '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

[ -n "$LIST" ] || { echo "error: --list is required" >&2; exit 2; }
[ -n "$OUT" ] || { echo "error: --out is required" >&2; exit 2; }
[ -x "$AY" ] || { echo "error: solver binary not executable: $AY" >&2; exit 2; }

mkdir -p "$OUT"
cp "$LIST" "$OUT/files.txt"
: > "$OUT/ledger.tsv"

export AY WALL OUT

census_one() {
  file="$1"
  key="$(printf '%s' "$file" | tr '/' '~')"
  start="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
  set +e
  AY_CENSUS=1 perl -e 'alarm shift; exec @ARGV' "$WALL" \
    "$AY" solve --no-proof -T:10 "$file" \
    > "$OUT/$key.out" 2> "$OUT/$key.err" < /dev/null
  rc=$?
  set -e
  end="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
  verdict="$(grep -m1 -E '^(sat|unsat|unknown)$' "$OUT/$key.out" 2>/dev/null || true)"
  [ -n "$verdict" ] || verdict="none"
  printf '%s\t%s\t%s\t%s\n' "$rc" "$(perl -e "printf '%.2f', $end - $start")" \
    "$verdict" "$file" >> "$OUT/ledger.tsv"
}
export -f census_one

tr -d '\r' < "$LIST" | grep -v '^$' | xargs -P "$JOBS" -I{} bash -c 'census_one "$@"' _ {}

echo "census: $(wc -l < "$OUT/ledger.tsv" | tr -d ' ') files -> $OUT"
