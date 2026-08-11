import subprocess, pathlib, collections, json, sys, os
D = pathlib.Path("evals/results/smtcomp-2025/mv/QF_Datatypes/mv-perfect-44d40f56/models/ay")
BENCH = pathlib.Path("benchmarks/smtlib-2025")
DOL = ".competitors/dolmen/dolmen"
MAP = {3:"E:parsing-error", 6:"E:partial-dstr", 0:"Sat", 2:"LimitReached"}
res = collections.Counter(); bad = []
models = sorted(D.rglob("*.out"))
for i, m in enumerate(models):
    rel = m.relative_to(D).as_posix()[:-4]      # strip .out -> benchmark relpath
    bench = BENCH / rel
    if not bench.is_file():
        res["MISSING_BENCH"] += 1; bad.append((rel, "missing bench")); continue
    argv = [DOL, "--time=1h", "--size=40G", "--strict=false",
            "--check-model=true", "--report-style=minimal", "--warn=-all", str(bench)]
    with open(m, "rb") as fh:
        p = subprocess.run(argv, stdin=fh, capture_output=True, timeout=300)
    tag = MAP.get(p.returncode, f"exit{p.returncode}")
    res[tag] += 1
    if p.returncode != 0 and len(bad) < 25:
        bad.append((rel, tag, p.stderr.decode("utf-8", "replace").strip()[:90]))
    if (i+1) % 250 == 0:
        print(f"  {i+1}/{len(models)} {dict(res)}", flush=True)
print("\n=== DOLMEN 0.10 REPLAY OVER ARCHIVED mv-perfect MODELS ===")
print(f"models: {len(models)}")
for k, v in res.most_common(): print(f"   {k:18s} {v}")
print(f"\nreproduces Sat=1943? {'YES' if res.get('Sat')==1943 else 'NO'}")
for b in bad[:12]: print("   !", b)
