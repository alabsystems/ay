#!/bin/bash
# Every bin target must arm the kernel memory bound as the first thing it does.
#
# WHY THIS IS A GATE AND NOT A CONVENTION
# ---------------------------------------
# On 2026-08-02 this machine took its fourth memory kernel panic: `ay-fixed`
# 137.9 GB + `ay-base` 134.4 GB + 13 more `ay` processes at 26.3 GB = 355.7 GB
# resident on a 128 GB box. `ay-base`/`ay-fixed` were COPIES of the ay binary at
# /private/tmp paths, under names that appeared in no allowlist -- so a
# path-shimming model could not have covered them even in principle. (Such a tool
# existed and has since been retired; this in-image bound is what replaced it.)
#
# The bound therefore lives in the image (`ay_sys::govern::arm()`). But an
# in-image bound that a new bin target forgets to call is worse than none: it
# looks armed from the outside. A binary that can allocate without bound and
# does not arm itself must fail the BUILD, not ship and get discovered by the
# next panic.
#
# Exit 0 = every bin target arms. Exit 1 = at least one does not.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Bin targets deliberately exempt, with the reason. Keep this list SHORT and
# justified: the default answer for a new binary is "arm it".
#   (none today -- every bin target arms)
EXEMPT=()

# macOS ships bash 3.2, which has no `mapfile`. Read into a temp file instead --
# a gate that only runs on a newer bash is a gate that does not run here.
rows_file="$(mktemp)"
trap 'rm -f "$rows_file"' EXIT
cargo metadata --no-deps --format-version 1 2>/dev/null | python3 -c '
import json, sys, os
m = json.load(sys.stdin)
root = os.getcwd() + "/"
for p in m["packages"]:
    for t in p["targets"]:
        if "bin" in t["kind"]:
            print(t["name"] + "\t" + t["src_path"].replace(root, ""))
' > "$rows_file"

if [ ! -s "$rows_file" ]; then
  echo "check_govern_armed: FATAL: could not enumerate bin targets" >&2
  exit 1
fi

bad=0 ok=0 exempt=0
while IFS=$'\t' read -r name src; do
  [ -n "$name" ] || continue

  skip=0
  for e in ${EXEMPT+"${EXEMPT[@]}"}; do
    [ "$e" = "$name" ] && skip=1
  done
  if [ "$skip" -eq 1 ]; then
    echo "  $name: exempt"
    exempt=$((exempt + 1)); continue
  fi

  if [ ! -f "$src" ]; then
    echo "check_govern_armed: UNARMED  $name  (source $src not found)" >&2
    bad=$((bad + 1)); continue
  fi

  # The call must be the first executable statement of main -- arm() re-execs,
  # so anything before it is discarded work, and it calls set_var, which is only
  # sound while single-threaded. Take the first non-blank, non-comment line of
  # the main body and require it to be the arm call.
  first="$(awk '
    /^[[:space:]]*(pub[[:space:]]+)?fn[[:space:]]+main[[:space:]]*\(/ { inmain = 1; next }
    inmain {
      line = $0
      sub(/^[[:space:]]+/, "", line)
      if (line == "") next
      if (line ~ /^\/\//) next
      print line
      exit
    }
  ' "$src")"

  case "$first" in
    *"govern::arm()"*)
      ok=$((ok + 1)) ;;
    *)
      echo "check_govern_armed: UNARMED  $name  ($src)" >&2
      echo "        first statement of main is: ${first:-<none>}" >&2
      echo "        expected: ay_sys::govern::arm();" >&2
      bad=$((bad + 1)) ;;
  esac
done < "$rows_file"

echo
if [ "$bad" -eq 0 ]; then
  echo "check_govern_armed: OK ($ok armed, $exempt exempt)"
  exit 0
fi
echo "check_govern_armed: FAIL -- $bad bin target(s) can allocate without a kernel bound" >&2
echo "Add \`ay_sys::govern::arm();\` as the first statement of main. See crates/ay-sys/src/govern.rs" >&2
exit 1
