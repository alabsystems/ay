#!/usr/bin/env bash
# Emit the OFFICIAL MSE24 exact-weighted instance list (539 instances).
#
# Why this exists: benchmarks/maxsat/mse24-exact-weighted/ was extracted from
# mse24-exact-weighted.zip (571 instances). The organizers later published
# mse24-exact-weighted-fixed.zip, which WITHDRAWS 32 of those instances
# (15 upgradeability, 9 timetabling, 8 warehouses). Measuring over all 571
# therefore scores 32 instances that are not part of the official set.
#
# Usage:
#   ./official-set.sh                  # print 539 instance basenames
#   ./official-set.sh --paths          # print paths to the .xz files
#   ./official-set.sh --withdrawn      # print the 32 excluded instead
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
dir="$here/mse24-exact-weighted"
manifest="$here/WITHDRAWN-mse24-exact-weighted.txt"

[ -d "$dir" ]      || { echo "missing instance dir: $dir" >&2; exit 1; }
[ -f "$manifest" ] || { echo "missing manifest: $manifest" >&2; exit 1; }

withdrawn=$(grep -v '^#' "$manifest" | grep -v '^[[:space:]]*$' | sort -u)
all=$(cd "$dir" && ls *.wcnf.xz 2>/dev/null | sed 's/\.xz$//' | sort -u)

case "${1:-}" in
  --withdrawn) printf '%s\n' "$withdrawn" ;;
  --paths)     comm -23 <(printf '%s\n' "$all") <(printf '%s\n' "$withdrawn") \
                 | sed "s|^|$dir/|; s|$|.xz|" ;;
  *)           comm -23 <(printf '%s\n' "$all") <(printf '%s\n' "$withdrawn") ;;
esac
