#!/usr/bin/env bash
# ay-script: satcomp24-sample-fetch
# Fetch the SAT-COMP 2024 sample corpus listed in
# benchmarks/sat/satcomp2024-sample/manifest.csv from the public GBD mirror
# (https://benchmark-database.de/file/<md5>), verify each download against
# the manifest's size_bytes, and decompress alongside the .xz.
#
# The instances are intentionally NOT committed (benchmarks/.gitignore
# excludes *.cnf / *.cnf.xz); this script is the provisioning step the
# manifest was designed for. Total download ~232 MB (~2.9 GB decompressed;
# the two giants are bmc_QICE 179 MB and shuffling-2 34 MB compressed).
#
# Usage: scripts/fetch_satcomp_sample.sh
set -u
cd "$(dirname "${BASH_SOURCE[0]}")/../benchmarks/sat/satcomp2024-sample"

# manifest.csv's `track` column is quoted and contains commas, so parse
# positionally from both ends: hash and filename lead the row; size_bytes
# is the second-to-last field.
tail -n +2 manifest.csv | while IFS= read -r line; do
    hash=$(echo "$line" | cut -d, -f1)
    filename=$(echo "$line" | cut -d, -f2)
    size_bytes=$(echo "$line" | awk -F, '{print $(NF-1)}')
    xzname="${hash}-${filename}"
    cnfname="${xzname%.xz}"
    if [ -f "$cnfname" ]; then
        echo "SKIP $cnfname"
        continue
    fi
    if [ ! -f "$xzname" ]; then
        echo "GET  $xzname (${size_bytes} bytes)"
        curl -sL --max-time 900 -o "$xzname.part" \
            "https://benchmark-database.de/file/$hash" \
            || { echo "FAIL download $hash"; rm -f "$xzname.part"; continue; }
        actual=$(stat -c %s "$xzname.part" 2>/dev/null || stat -f %z "$xzname.part")
        if [ "$actual" != "$size_bytes" ]; then
            echo "FAIL size $xzname: got $actual want $size_bytes"
            rm -f "$xzname.part"
            continue
        fi
        mv "$xzname.part" "$xzname"
    fi
    xz -dkf "$xzname" && echo "OK   $cnfname" || echo "FAIL decompress $xzname"
done
echo "inventory: $(ls -1 ./*.cnf 2>/dev/null | wc -l) decompressed instances"
