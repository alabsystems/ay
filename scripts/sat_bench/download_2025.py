#!/usr/bin/env python3
# ay-script: sat-download-2025
"""Download a stratified sample of SAT-COMP main_2025 from GBD by content hash.

Reads a `hash|filename` list (sqlite3 pipe-separated), dedups by hash, sorts by
filename to spread families, then downloads .cnf.xz from benchmark-database.de
(skipping oversized compressed files) and decompresses to .cnf.
"""
import subprocess, sys, os, urllib.request, urllib.error

LIST = sys.argv[1] if len(sys.argv) > 1 else "/tmp/main_2025_list.tsv"
OUT = sys.argv[2] if len(sys.argv) > 2 else "/tmp/satcampaign/cnf"
TARGET = int(sys.argv[3]) if len(sys.argv) > 3 else 60
MAX_XZ = int(sys.argv[4]) if len(sys.argv) > 4 else 20 * 1024 * 1024  # 20MB compressed cap

os.makedirs(OUT, exist_ok=True)

# dedup by hash, keep first filename
seen = {}
for line in open(LIST):
    line = line.rstrip("\n")
    if not line or "|" not in line:
        continue
    h, fn = line.split("|", 1)
    if h not in seen:
        seen[h] = fn
items = sorted(seen.items(), key=lambda kv: kv[1])  # sort by filename -> family spread
n = len(items)
print(f"unique instances: {n}; targeting {TARGET} via even stride")

# even stride selection
if TARGET >= n:
    order = list(range(n))
else:
    step = n / TARGET
    order = sorted(set(int(i * step) for i in range(TARGET)))

got = 0
attempted = 0
manifest = []
for idx in order:
    if got >= TARGET:
        break
    h, fn = items[idx]
    base = fn.replace(".cnf.xz", "").replace(".cnf", "").replace(".xz", "")
    base = "".join(c if c.isalnum() or c in "-_." else "_" for c in base)[:80]
    out_cnf = os.path.join(OUT, f"{h[:12]}_{base}.cnf")
    if os.path.exists(out_cnf) and os.path.getsize(out_cnf) > 0:
        got += 1
        manifest.append((h, fn, out_cnf))
        continue
    url = f"https://benchmark-database.de/file/{h}?context=cnf"
    attempted += 1
    try:
        req = urllib.request.Request(url, method="HEAD")
        with urllib.request.urlopen(req, timeout=30) as r:
            clen = int(r.headers.get("content-length", "0"))
        if clen == 0 or clen > MAX_XZ:
            print(f"SKIP (size {clen}) {fn}")
            continue
        xz_path = out_cnf + ".xz"
        urllib.request.urlretrieve(url, xz_path)
        subprocess.run(["xz", "-df", xz_path], check=True)
        if os.path.exists(out_cnf) and os.path.getsize(out_cnf) > 0:
            got += 1
            manifest.append((h, fn, out_cnf))
            print(f"[{got}/{TARGET}] {fn}  ({clen} xz)")
    except Exception as e:
        print(f"FAIL {fn}: {e}")

with open(os.path.join(os.path.dirname(OUT), "manifest_2025_sample.tsv"), "w") as f:
    for h, fn, p in manifest:
        f.write(f"{h}\t{fn}\t{p}\n")
print(f"\nDownloaded {got} instances (attempted {attempted}). Manifest written.")
