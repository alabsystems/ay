#!/usr/bin/env bash
# Regenerate the decompressed .wcnf instances from the retained .xz set.
# The original competition zips were deleted 2026-08-20 to reclaim disk;
# every instance survives compressed, so this is a purely local restore.
# Old-format (-oldfmt) conversions were NOT retained and are not restored here.
set -euo pipefail
for d in mse24-exact-weighted mse24-exact-unweighted; do
  [ -d "$d" ] || continue
  echo "restoring $d ..."
  ( cd "$d" && ls *.xz 2>/dev/null | while read -r f; do
      [ -f "${f%.xz}" ] || xz -dk "$f"
    done )
done
echo "done. NOTE: mse24-exact-weighted still contains the 32 instances the"
echo "organizers withdrew -- see WITHDRAWN-mse24-exact-weighted.txt."
