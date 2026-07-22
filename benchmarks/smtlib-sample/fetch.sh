#!/bin/bash
# ay-script: smtlib-sample-fetch
# Re-fetch the SMT-LIB sample corpus used by `ay-z3-parity bench`.
#
# Source: SMT-LIB release 2024 (non-incremental), Zenodo record 11061097
#         https://zenodo.org/records/11061097
#
# Sampling rule (deterministic, no cherry-picking): for each division, list
# every *.smt2 path inside the archive, sort lexicographically (LC_ALL=C),
# and take N=300 evenly spaced entries at indices floor(i*total/N) for
# i = 0..N-1. Files are copied flat, with '/' in the archive path replaced
# by '__'. Verify the result against MANIFEST.sha256:
#     (cd benchmarks/smtlib-sample && shasum -a 256 -c MANIFEST.sha256)
#
# Requires: curl, unzstd (zstd), tar, python3, md5 (macOS) or md5sum.
set -euo pipefail

DEST="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
N=300
ZENODO="https://zenodo.org/api/records/11061097/files"

# division  expected-md5-of-archive (as published by Zenodo)
# QF_AX = the free-base-read wrong-SAT family; QF_S / QF_SLIA = the str.substr
# OOB wrong-SAT family. Both shipped-bug theories are permanently covered.
DIVISIONS=(
  "QF_UF    3ce26e05264581931a583bae96b87f34"
  "QF_UFLIA 26d8d7e71c33b10c9767beebddb5da9e"
  "QF_AX    6d323ea02eb4d74e8ac77420bf94e3cb"
  "QF_S     e7a201b1fff6c952f278154d6513a0c0"
  "QF_SLIA  277e586bf556ee33dc638348bc6de50a"
)

md5_of() {
  if command -v md5 >/dev/null 2>&1; then md5 -q "$1"; else md5sum "$1" | cut -d' ' -f1; fi
}

TMP="$(mktemp -d "${TMPDIR:-/tmp}/smtlib-sample.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

for entry in "${DIVISIONS[@]}"; do
  read -r LOGIC WANT_MD5 <<<"$entry"
  AR="$TMP/$LOGIC.tar.zst"
  echo "== $LOGIC: downloading ..."
  curl -fSL --retry 3 --max-time 1800 "$ZENODO/$LOGIC.tar.zst/content" -o "$AR"
  GOT_MD5="$(md5_of "$AR")"
  if [ "$GOT_MD5" != "$WANT_MD5" ]; then
    echo "error: $LOGIC.tar.zst md5 mismatch: got $GOT_MD5 want $WANT_MD5" >&2
    exit 1
  fi
  echo "== $LOGIC: md5 ok ($GOT_MD5); extracting ..."
  XD="$TMP/x-$LOGIC"
  mkdir -p "$XD"
  tar --use-compress-program=unzstd -xf "$AR" -C "$XD"
  ( cd "$XD" && find . -name '*.smt2' | sed 's|^\./||' | LC_ALL=C sort ) > "$TMP/$LOGIC.all"
  TOTAL="$(wc -l < "$TMP/$LOGIC.all" | tr -d ' ')"
  echo "== $LOGIC: sampling $N of $TOTAL ..."
  mkdir -p "$DEST/$LOGIC"
  python3 - "$TMP/$LOGIC.all" "$TOTAL" "$N" "$XD" "$DEST/$LOGIC" <<'EOF'
import sys, shutil, os
listing, total, n, src, dst = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
paths = [l.rstrip("\n") for l in open(listing)]
n = min(n, total)
idxs = sorted({i * total // n for i in range(n)})
for i in idxs:
    p = paths[i]
    shutil.copyfile(os.path.join(src, p), os.path.join(dst, p.replace("/", "__")))
print(f"   sampled {len(idxs)}/{total}")
EOF
  rm -rf "$XD" "$AR"
done

echo "== verifying against MANIFEST.sha256 ..."
( cd "$DEST" && shasum -a 256 -c MANIFEST.sha256 --quiet ) && echo "OK: corpus matches MANIFEST.sha256"
