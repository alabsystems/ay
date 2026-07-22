#!/usr/bin/env python3
# ay-script: sat-download-2025
"""Download a stratified sample of SAT-COMP main_2025 from GBD by content hash.

Reads a `hash|filename` list (sqlite3 pipe-separated), dedups by hash, sorts by
filename to spread families, then downloads .cnf.xz from benchmark-database.de
(skipping oversized compressed files) and decompresses to .cnf.
"""
import contextlib
import lzma
import os
import signal
import sys
import tempfile
import urllib.error
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from _oom_guard import copy_stream_limited  # noqa: E402

LIST = sys.argv[1] if len(sys.argv) > 1 else "/tmp/main_2025_list.tsv"
OUT = sys.argv[2] if len(sys.argv) > 2 else "/tmp/satcampaign/cnf"
TARGET = int(sys.argv[3]) if len(sys.argv) > 3 else 60
MAX_XZ = int(sys.argv[4]) if len(sys.argv) > 4 else 20 * 1024 * 1024  # 20MB compressed cap
MAX_CNF = int(sys.argv[5]) if len(sys.argv) > 5 else 2 * 1024 * 1024 * 1024
DECOMPRESS_TIMEOUT_S = int(sys.argv[6]) if len(sys.argv) > 6 else 300

if TARGET <= 0 or MAX_XZ <= 0 or MAX_CNF <= 0 or DECOMPRESS_TIMEOUT_S <= 0:
    raise SystemExit("target, byte caps, and decompression timeout must be positive")
if not hasattr(signal, "SIGALRM"):
    raise SystemExit("bounded SAT corpus decompression requires POSIX SIGALRM")

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
        if clen > MAX_XZ:
            print(f"SKIP (size {clen}) {fn}")
            continue
        with tempfile.TemporaryDirectory(prefix=".ay-download-", dir=OUT) as temporary:
            xz_path = os.path.join(temporary, "payload.cnf.xz")
            staged_cnf = os.path.join(temporary, "payload.cnf")
            downloaded = 0
            with urllib.request.urlopen(url, timeout=30) as response, \
                    open(xz_path, "xb") as compressed:
                while True:
                    chunk = response.read(min(1024 * 1024, MAX_XZ - downloaded + 1))
                    if not chunk:
                        break
                    downloaded += len(chunk)
                    if downloaded > MAX_XZ:
                        raise ValueError(
                            f"compressed download exceeds fixed {MAX_XZ}-byte cap"
                        )
                    compressed.write(chunk)
                compressed.flush()
                os.fsync(compressed.fileno())
            if downloaded == 0:
                raise ValueError("download was empty")

            def decompression_timeout(_signum, _frame):
                raise TimeoutError(
                    f"decompression exceeded {DECOMPRESS_TIMEOUT_S}s"
                )

            previous_handler = signal.signal(signal.SIGALRM, decompression_timeout)
            signal.alarm(DECOMPRESS_TIMEOUT_S)
            try:
                with lzma.open(xz_path, "rb") as source, open(staged_cnf, "xb") as output:
                    written = copy_stream_limited(source, output, MAX_CNF)
                    output.flush()
                    os.fsync(output.fileno())
            finally:
                signal.alarm(0)
                signal.signal(signal.SIGALRM, previous_handler)
            if written == 0:
                raise ValueError("decompressed benchmark was empty")
            try:
                os.link(staged_cnf, out_cnf)
            except FileExistsError:
                if os.path.getsize(out_cnf) <= 0:
                    raise
        if os.path.exists(out_cnf) and os.path.getsize(out_cnf) > 0:
            got += 1
            manifest.append((h, fn, out_cnf))
            print(f"[{got}/{TARGET}] {fn}  ({clen} xz)")
    except Exception as e:
        print(f"FAIL {fn}: {e}")

manifest_path = os.path.join(os.path.dirname(OUT), "manifest_2025_sample.tsv")
with tempfile.NamedTemporaryFile(
        "w", dir=os.path.dirname(manifest_path), prefix=".manifest-", delete=False
) as f:
    temporary_manifest = f.name
    try:
        for h, fn, p in manifest:
            f.write(f"{h}\t{fn}\t{p}\n")
        f.flush()
        os.fsync(f.fileno())
    except BaseException:
        with contextlib.suppress(OSError):
            os.unlink(temporary_manifest)
        raise
os.replace(temporary_manifest, manifest_path)
print(f"\nDownloaded {got} instances (attempted {attempted}). Manifest written.")
