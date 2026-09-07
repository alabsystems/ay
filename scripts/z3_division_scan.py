#!/usr/bin/env python3
"""Division scan: stratified AY-vs-z3 differential over an SMT-LIB corpus root.

For every division directory under ROOT (or the --divisions subset), take N
evenly spaced files (seeded shuffle), run AY with an internal deadline (-T) and
z3 with the same deadline, and append one JSON line per file to OUT. AY's
reason-unknown is captured from `--stats`. Never SIGKILLs a bare wrapper: AY
self-terminates on -T and any straggler is killed as a whole process group.

Summary per division: ay_decided, z3_decided, both, z3_only, ay_only,
disagreements, and an AY-unknown reason histogram.
"""
import argparse, collections, concurrent.futures as cf, json, os, random, re, subprocess, sys, time

AY = os.path.expanduser(os.environ.get("AY", "~/ay-bench/target-z3/release/ay"))
Z3 = os.environ.get("Z3", "/opt/homebrew/bin/z3")
VERDICTS = ("sat", "unsat", "unknown")
AYFLAGS = os.environ.get("AYFLAGS", "").split()
# The campaign asks two different questions and they need different runs:
#
#   apples-to-apples  AY doing the same work as z3 (no proof recorded, no
#                     certificate minted) against z3. This is the only fair
#                     read on raw solving efficiency and capability.
#   the product       AY doing what AY is for: deciding AND standing behind it
#                     with a checkable certificate or a confirmed model.
#
# The bar is not parity on the first. AY has to be SUPERIOR to z3 — decide at
# least what z3 decides, in the same envelope — while also carrying evidence z3
# does not produce at all. Reporting only the first flatters the certified
# posture; reporting only the second hides an efficiency gap behind proof work.
Z3_EXACT_FLAGS = os.environ.get("Z3_EXACT_FLAGS", "--z3-mode").split()
BOTH_POSTURES = os.environ.get("BOTH_POSTURES", "") not in ("", "0")


def _provenance():
    """Identify both solvers exactly. Two campaign conclusions have already been
    wrong because a number was read without knowing which oracle produced it:
    z3 4.16 answers through error recovery on logic names it cannot parse, so a
    verdict line is not evidence the input was understood."""
    import hashlib
    out = {}
    for key, path in (("ay", AY), ("z3", Z3)):
        rec = {"path": path}
        try:
            rec["version"] = subprocess.run([path, "--version"], capture_output=True, text=True, timeout=30).stdout.strip()
        except Exception as err:
            rec["version"] = f"<unavailable: {err}>"
        try:
            with open(path, "rb") as fh:
                h = hashlib.sha256()
                for chunk in iter(lambda: fh.read(1 << 20), b""):
                    h.update(chunk)
            rec["sha256"] = h.hexdigest()
        except Exception as err:
            rec["sha256"] = f"<unavailable: {err}>"
        out[key] = rec
    out["ay_flags"] = AYFLAGS
    return out


PROVENANCE = None

def run(cmd, to):
    t0 = time.time()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        so, se = p.communicate(timeout=to + 5)
    except subprocess.TimeoutExpired:
        try: os.killpg(p.pid, 9)
        except ProcessLookupError: pass
        p.communicate()
        return "timeout", time.time() - t0, "", ""
    wall = time.time() - t0
    lines = [l.strip() for l in so.splitlines() if l.strip() in VERDICTS]
    # A solver that printed any (error ...) diagnostic is classified as "error": z3's
    # error recovery prints a degraded verdict after e.g. "unknown sort 'FloatingPoint'",
    # which would otherwise manufacture a false disagreement.
    if "(error" in so or "(error" in se:
        v = "error"
    else:
        v = lines[-1] if lines else ("error" if (p.returncode not in (0,1)) else "none")
    return v, wall, so[-2000:], se[-4000:]

CERT_RE = re.compile(
    r"ay\.proof\.certificate\s+path=\S+\s+unproved_steps=(\d+)\s+"
    r"foreign_assumes=(\w+)\s+trust_free=(\w+)\s+ay_self_checkable=(\w+)"
)


def ay_certificate(so, se):
    """Whether this run published a checkable certificate, and what it cost.

    Proofs and certificates are the reason to use AY, so a verdict without one
    is only half a result. `ay_self_checkable=yes` means AY's own strict checker
    accepts the artifact; `unproved_steps > 0` means the sidecar carries `hole`
    steps and is not externally checkable whatever the verdict says.
    """
    blob = so + "\n" + se
    m = CERT_RE.search(blob)
    out = {}
    if m:
        out["cert_unproved_steps"] = int(m.group(1))
        out["cert_foreign_assumes"] = m.group(2) == "yes"
        out["cert_trust_free"] = m.group(3) == "yes"
        out["cert_self_checkable"] = m.group(4) == "yes"
    for key, stat in (("cert_mint_ns", "cert.mint_nanos"), ("solve_ns", "time")):
        mm = re.search(r":%s\s+([0-9.]+)" % re.escape(stat), blob)
        if mm:
            out[key] = float(mm.group(1))
    # SAT has no certificate; its evidence is the independent model gate.
    mg = re.search(r':model_check_gate\.result\s+"([a-z-]+)"', blob)
    if mg:
        out["model_gate"] = mg.group(1)
    return out


def ay_reason(so, se):
    m = re.search(r"\(:reason-unknown\s+([^)]*)\)", so + "\n" + se)
    if m:
        r = m.group(1).strip().strip('"')
        return re.sub(r"\s+", " ", r)[:80]
    return ""

def one(job):
    div, f, to = job
    # --stats-full, not --stats: both evidence signals we care about
    # (`ay.proof.certificate` and `:model_check_gate.result`) are absent from the
    # curated set, so a scan run with --stats records verdicts with no way to
    # tell whether AY stood behind them.
    a_v, a_w, a_so, a_se = run([AY, "--quiet", "--stats-full", f"-T:{to}"] + AYFLAGS + [f], to)
    z_v, z_w, z_so, z_se = run([Z3, f"-T:{to}", f], to)
    rec = {"division": div, "file": f, "ay": a_v, "ay_wall": round(a_w, 3), "z3": z_v, "z3_wall": round(z_w, 3)}
    if BOTH_POSTURES:
        # Same file, AY stripped to z3's workload: the apples-to-apples arm.
        x_v, x_w, _, _ = run([AY, "--quiet", f"-T:{to}"] + Z3_EXACT_FLAGS + [f], to)
        rec["ay_z3exact"] = x_v
        rec["ay_z3exact_wall"] = round(x_w, 3)
    rec.update(ay_certificate(a_so, a_se))
    if a_v not in ("sat", "unsat"):
        rec["ay_reason"] = ay_reason(a_so, a_se) or (a_se.strip().splitlines()[-1][:120] if a_se.strip() else "")
    if a_v in ("sat", "unsat") and z_v in ("sat", "unsat") and a_v != z_v:
        rec["DISAGREE"] = True
    return rec

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("--per-division", type=int, default=20)
    ap.add_argument("--timeout", type=int, default=20)
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--divisions", default="")
    ap.add_argument("--out", required=True)
    ap.add_argument("--resume", action="store_true")
    a = ap.parse_args()
    divs = sorted(d for d in os.listdir(a.root) if os.path.isdir(os.path.join(a.root, d)))
    if a.divisions:
        want = set(a.divisions.split(","))
        divs = [d for d in divs if d in want]
    done = set()
    if a.resume and os.path.exists(a.out):
        for l in open(a.out):
            try:
                rec = json.loads(l)
                if "file" in rec:
                    done.add(rec["file"])
            except Exception:
                pass
    jobs = []
    for d in divs:
        files = sorted(x for x in os.listdir(os.path.join(a.root, d)) if x.endswith(".smt2"))
        rng = random.Random(f"{a.seed}:{d}")
        rng.shuffle(files)
        for x in files[: a.per_division]:
            p = os.path.join(a.root, d, x)
            if p not in done:
                jobs.append((d, p, a.timeout))
    global PROVENANCE
    PROVENANCE = _provenance()
    print(f"{len(divs)} divisions, {len(jobs)} files to run (jobs={a.jobs}, T={a.timeout}s)", flush=True)
    print("provenance: " + json.dumps(PROVENANCE), flush=True)
    out = open(a.out, "a")
    # Every run records exactly which binaries produced it, as its first line.
    out.write(json.dumps({"record": "provenance", **PROVENANCE}) + "\n")
    out.flush()
    stats = collections.defaultdict(lambda: collections.Counter())
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        for rec in ex.map(one, jobs):
            out.write(json.dumps(rec) + "\n"); out.flush()
            s = stats[rec["division"]]
            s["n"] += 1
            ad, zd = rec["ay"] in ("sat", "unsat"), rec["z3"] in ("sat", "unsat")
            s["ay"] += ad; s["z3"] += zd; s["both"] += ad and zd; s["z3_only"] += (zd and not ad); s["ay_only"] += (ad and not zd)
            if "ay_z3exact" in rec:
                xd = rec["ay_z3exact"] in ("sat", "unsat")
                s["ay_x"] += xd
                s["x_beats_z3"] += (xd and not zd)
                s["z3_beats_x"] += (zd and not xd)
            s["DISAGREE"] += bool(rec.get("DISAGREE"))
            if ad:
                evidenced = rec.get("cert_self_checkable") or rec.get("model_gate") == "confirmed-sat"
                if evidenced:
                    s["certified"] += 1
                elif rec.get("cert_unproved_steps", 0) > 0:
                    s["cert_holes"] += 1
                elif "cert_unproved_steps" in rec:
                    s["cert_other"] += 1
                else:
                    s["cert_none"] += 1
            if not ad: s["r:" + (rec["ay"] if rec["ay"] != "unknown" else rec.get("ay_reason", "?"))] += 1
            if rec.get("DISAGREE"): print("DISAGREE", rec, flush=True)
    print()
    if BOTH_POSTURES:
        print("apples-to-apples = AY with z3's workload; product = AY's own posture")
        print(f"{'division':22} {'n':>3} {'z3':>3} {'AYx':>4} {'x>z3':>5} {'z3>x':>5} {'AY':>3} {'cert':>5} {'hole':>4} {'DIS':>3}  ay-unknown reasons")
    else:
        print(f"{'division':22} {'n':>3} {'ay':>3} {'z3':>3} {'both':>4} {'z3only':>6} {'ayonly':>6} {'DIS':>3} {'cert':>5} {'hole':>4}  ay-unknown reasons")
    for d in divs:
        s = stats[d]
        if not s["n"]: continue
        reasons = ", ".join(f"{k[2:]}={v}" for k, v in s.most_common() if k.startswith("r:"))
        if BOTH_POSTURES:
            print(f"{d:22} {s['n']:>3} {s['z3']:>3} {s['ay_x']:>4} {s['x_beats_z3']:>5} {s['z3_beats_x']:>5} {s['ay']:>3} {s['certified']:>5} {s['cert_holes']:>4} {s['DISAGREE']:>3}  {reasons}")
        else:
            print(f"{d:22} {s['n']:>3} {s['ay']:>3} {s['z3']:>3} {s['both']:>4} {s['z3_only']:>6} {s['ay_only']:>6} {s['DISAGREE']:>3} {s['certified']:>5} {s['cert_holes']:>4}  {reasons}")

if __name__ == "__main__":
    main()
