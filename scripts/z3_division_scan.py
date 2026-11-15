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
import argparse, collections, concurrent.futures as cf, json, os, random, re, shutil, subprocess, sys, tempfile, time

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
    # Return the FULL text, never a tail.
    #
    # This used to be `so[-2000:], se[-4000:]`, and that silently destroyed the
    # thing the scan exists to measure. `--stats-full` writes about 12 KB to
    # STDERR; `:model_check_gate.result` sits roughly 5.4 KB from the end on an
    # ordinary QF_LRA file, so the 4 KB tail dropped it and the scan recorded a
    # confirmed `sat` as unevidenced. The loss was biased: the more statistics a
    # run produced, the more likely its evidence signal fell off the front, so
    # harder problems lost their evidence preferentially. Measured 2026-09-07 on
    # QF_LRA `2019-ezsmt__blending__14`: stderr 11,917 bytes, gate line at offset
    # 6,477, dropped. Cap only against a runaway printer.
    cap = 4 << 20
    return v, wall, so[-cap:], se[-cap:]

CERT_RE = re.compile(
    r"ay\.proof\.certificate\s+path=\S+\s+unproved_steps=(\d+)\s+"
    r"foreign_assumes=(\w+)\s+trust_free=(\w+)\s+ay_self_checkable=(\w+)"
)
ADMISSION_RE = re.compile(r"ay\.proof\.certificate\s.*?\bunsat_admission=([\w-]+)")
DECLINE_RE = re.compile(
    r"ay\.proof\.decline\s+path=\S+\s+mechanism=([\w-]+)(?:\s+recorded=([\w-]+))?")
CORROB_RE = re.compile(r"ay\.proof\.corroboration\s+method=([\w-]+)\s+scope=([\w-]+)")
# #evidence-stage-3, the tier-B signal at ZERO code cost. Every narrow
# semantic-certificate lane already writes `:verdict_certification.<lane> 1`
# into the statistics, and `--stats-full` already dumps them; nothing in AY had
# to change for this scan to read them. Measured on a 59-file sample of the
# class that emits no certificate at all: 16 (27%) carry one of these tokens, so
# without this line a verdict admitted by a CHECKED lane that renders no
# document is indistinguishable from one admitted by nothing.
#
# What the EXPENSIVE version would buy, and why it is not done here: putting the
# token on the user-visible `ay.proof.*` disclosure needs a new public executor
# accessor, because `crates/ay/src/` cannot see `CommandUnsatAdmission`'s
# certificate payload. That would make the signal readable by a human running
# one file instead of by a corpus scan grepping statistics, and it would let the
# tier-B population be defined without a regex over `--stats-full`. It buys no
# new evidence and moves no verdict, so it is the second thing to do, not the
# first.
VCERT_RE = re.compile(r"^\s*:(verdict_certification\.[\w.]+)\s+(\S+)", re.M)


def ay_certificate(so, se):
    """Whether this run published a checkable certificate, and what it cost.

    Proofs and certificates are the reason to use AY, so a verdict without one
    is only half a result.

    Two DIFFERENT questions, and conflating them has already produced one false
    alarm in this campaign:

    * `cert_self_checkable` / `cert_unproved_steps` are facts about the emitted
      DOCUMENT, and the correct reading of them depends on which binary
      produced the line.

      **Before the stage-0 disclosure fix**, `ay_self_checkable` was computed
      from AY's in-memory terminal-trust report alone, which is blind to the
      printer's own `wire_rule_name` downgrade of rules with no Alethe
      counterpart. 78 corpus certificates carrying up to 148 `hole` steps
      therefore scored as evidence, reporting 698 of 1,181 decided (59.1%) where
      the honest number is 620 (52.5%), and 60 of 592 refutations where the
      honest number is 33. **After the fix**, `ay_self_checkable=yes` means the
      file on disk carries no `hole` step AND the terminal chain is trust-free
      and provenance-backed, so it implies `unproved_steps == 0`.

      This scan buckets on `unproved_steps == 0 AND cert_self_checkable`
      regardless. On a fixed binary the conjunction is redundant; on an older
      one it is the only honest predicate; and keeping it means a jsonl from
      either era reads the same way. `selfchk_inflated` counts documents where
      the flag says yes over a holey document, so it is the size of the old
      over-count on old data and a REGRESSION DETECTOR on new data, where it
      must be 0.

      `cert_self_checkable == False` says the document is not externally
      checkable. It does NOT say any rigor level withheld the verdict.
    * `cert_admission` is the authority behind the VERDICT. `--rigor certified`
      accepts a strict Alethe proof, a native BV DRAT re-check, or a replayed
      SAT-resolution refutation, so a `hole`-bearing document sits happily
      beside a `checked-sat-refutation` verdict. Bucket evidence coverage on
      this field, not on `cert_self_checkable`, when the question is "what
      stands behind the answer".
    """
    blob = so + "\n" + se
    m = CERT_RE.search(blob)
    out = {}
    if m:
        out["cert_unproved_steps"] = int(m.group(1))
        out["cert_foreign_assumes"] = m.group(2) == "yes"
        out["cert_trust_free"] = m.group(3) == "yes"
        out["cert_self_checkable"] = m.group(4) == "yes"
    ma = ADMISSION_RE.search(blob)
    if ma:
        out["cert_admission"] = ma.group(1)
    # Exactly one named mechanism per unevidenced refutation is the stage-3
    # acceptance criterion, so count them rather than taking the first.
    declines = DECLINE_RE.findall(blob)
    if declines:
        out["cert_decline"] = declines[0][0]
        out["cert_declines_seen"] = len(declines)
        if declines[0][1]:
            out["cert_decline_recorded"] = declines[0][1]
    mc = CORROB_RE.search(blob)
    if mc:
        out["cert_corroboration"] = mc.group(1)
        out["cert_corroboration_scope"] = mc.group(2)
    vcert = sorted({k for k, _ in VCERT_RE.findall(blob)})
    if vcert:
        out["verdict_certification"] = vcert
    for key, stat in (("cert_mint_ns", "cert.mint_nanos"), ("solve_ns", "time")):
        mm = re.search(r":%s\s+([0-9.]+)" % re.escape(stat), blob)
        if mm:
            out[key] = float(mm.group(1))
    # SAT has no certificate; its evidence is the independent model gate.
    mg = re.search(r':model_check_gate\.result\s+"([a-z-]+)"', blob)
    if mg:
        out["model_gate"] = mg.group(1)
    return out


def ay_evidence_tier(rec):
    """Three tiers, and only tier A counts toward the evidence goal.

    A — externally shaped: a hole-free Alethe document AY's own strict checker
        accepts and a pinned external checker can read, or a `sat` the mandatory
        independent model gate confirmed.
    B — internally checked, sealed and self-corroborated, with NO external
        surface: a `hole`-bearing document, or a verdict admitted by a
        non-Alethe authority such as a replayed SAT-resolution refutation. Real
        work stands behind these; nothing outside AY can re-run it. Never
        counted toward 100%.
    C — nothing: no artifact and no confirmation.

    `unproved_steps == 0` is required for A because the flag alone is inflated
    (see `ay_certificate`).
    """
    # Any `confirmed-sat*` value is a confirmation. The independent model gate
    # writes a bare "confirmed-sat"; the constructive lanes name the authority
    # that confirmed them, e.g. "confirmed-sat-checked-projection", so an exact
    # string match silently scored those verdicts as UNEVIDENCED. That is how the
    # census reported 587 of 589 rather than 589: the two exceptions were a
    # criterion gap on this side, not missing confirmation on AY's side.
    # `model-violates` and `cannot-confirm` must never match.
    if str(rec.get("model_gate", "")).startswith("confirmed-sat"):
        return "A"
    if rec.get("cert_self_checkable") and rec.get("cert_unproved_steps", 0) == 0:
        return "A"
    if "cert_unproved_steps" in rec:
        return "B"
    if rec.get("cert_admission") and rec.get("cert_admission") != "none-recorded":
        return "B"
    # #evidence-stage-3, zero code cost: a `verdict_certification.*` token is a
    # narrow semantic certificate AY's own checker minted and re-checked at
    # emission. It renders no document, so it can never be tier A, but a verdict
    # standing on one is not "nothing" either, and filing it under C overstated
    # the size of the wholly-unbacked population.
    if rec.get("verdict_certification"):
        return "B"
    return "C"


def ay_reason(so, se):
    m = re.search(r"\(:reason-unknown\s+([^)]*)\)", so + "\n" + se)
    if m:
        r = m.group(1).strip().strip('"')
        return re.sub(r"\s+", " ", r)[:80]
    return ""


STATUS_RE = re.compile(r"\(set-info\s+:status\s+([a-z]+)\)")

def declared_status(path):
    """The benchmark author's `:status`, the second reference every verdict is
    checked against (z3 is the first). `none` when the file declares nothing,
    `mixed:a,b` when an incremental file declares more than one."""
    try:
        with open(path, errors="replace") as fh:
            found = STATUS_RE.findall(fh.read(400000))
    except OSError:
        return "none"
    if not found:
        return "none"
    if len(set(found)) > 1:
        return "mixed:" + ",".join(sorted(set(found)))
    return found[0]


def _load1():
    try:
        return round(os.getloadavg()[0], 2)
    except OSError:
        return None

def one(job):
    div, f, to = job
    # Load at job start, so every timing in the row carries the machine state
    # it was taken under (README: "state the load with every number").
    load1 = _load1()
    # SOLVE A PRIVATE COPY, NEVER THE CORPUS FILE.
    #
    # AY writes `<input>.alethe` next to the input. Scanning in place therefore
    # (a) mutates a read-only benchmark tree and (b) makes every LATER run of
    # the same file emit NO certificate line at all, because the sidecar path
    # already exists — and under `--rigor strict` it downgrades a good `unsat`
    # to `unknown` for the filesystem reason "File exists (os error 17)". The
    # corpus already holds roughly 936 stale `.alethe` / `.alethe.tmp-*` files
    # written by earlier in-place scans (QF_AX 138, QF_AUFLIA 131,
    # QF_UFFPDTNIRA 68, ...), so an in-place scan UNDER-REPORTS evidence by an
    # amount that depends on who scanned the directory last. That is not a
    # measurement. z3 writes nothing, so it reads the original.
    workdir = tempfile.mkdtemp(prefix="ayscan-")
    try:
        local = os.path.join(workdir, os.path.basename(f))
        shutil.copyfile(f, local)
        # --stats-full, not --stats: both evidence signals we care about
        # (`ay.proof.certificate` and `:model_check_gate.result`) are absent from
        # the curated set, so a scan run with --stats records verdicts with no way
        # to tell whether AY stood behind them.
        a_v, a_w, a_so, a_se = run([AY, "--quiet", "--stats-full", f"-T:{to}"] + AYFLAGS + [local], to)
        z_v, z_w, z_so, z_se = run([Z3, f"-T:{to}", f], to)
        rec = {"division": div, "file": f, "ay": a_v, "ay_wall": round(a_w, 3), "z3": z_v, "z3_wall": round(z_w, 3)}
        if BOTH_POSTURES:
            # Same file, AY stripped to z3's workload: the apples-to-apples arm.
            # Fresh copy: the arm above just wrote a sidecar next to `local`.
            x_dir = tempfile.mkdtemp(prefix="ayscanx-", dir=workdir)
            x_local = os.path.join(x_dir, os.path.basename(f))
            shutil.copyfile(f, x_local)
            x_v, x_w, x_so, x_se = run([AY, "--quiet", f"-T:{to}"] + Z3_EXACT_FLAGS + [x_local], to)
            rec["ay_z3exact"] = x_v
            rec["ay_z3exact_wall"] = round(x_w, 3)
            if x_v not in ("sat", "unsat"):
                # The z3-exact arm's own explanation. Under `--z3-mode` AY
                # remaps its native vocabulary to z3's: timeout / resourceout /
                # memout / interrupted all print as "canceled", and every other
                # reason is kept inside "(incomplete <reason>)". Read the
                # default arm's `ay_reason` for the native token when the two
                # arms ended the same way.
                rec["ay_z3exact_reason"] = ay_reason(x_so, x_se) or (
                    x_se.strip().splitlines()[-1][:120] if x_se.strip() else "")
    finally:
        shutil.rmtree(workdir, ignore_errors=True)
    rec["status"] = declared_status(f)
    rec["load1"] = load1
    rec.update(ay_certificate(a_so, a_se))
    if a_v not in ("sat", "unsat"):
        rec["ay_reason"] = ay_reason(a_so, a_se) or (a_se.strip().splitlines()[-1][:120] if a_se.strip() else "")
    if a_v in ("sat", "unsat") and z_v in ("sat", "unsat") and a_v != z_v:
        rec["DISAGREE"] = True
    # Soundness is checked against BOTH references, for BOTH AY arms, and the
    # oracle itself is checked against the declared status. Any of these must
    # be zero; a non-zero outranks every capability number in the run.
    st = rec["status"]
    if st in ("sat", "unsat"):
        for key, v in (("ay", a_v), ("ay_z3exact", rec.get("ay_z3exact")), ("z3", z_v)):
            if v in ("sat", "unsat") and v != st:
                rec["DISAGREE_STATUS_" + key] = True
    xv = rec.get("ay_z3exact")
    if xv in ("sat", "unsat") and z_v in ("sat", "unsat") and xv != z_v:
        rec["DISAGREE_Z3EXACT"] = True
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
            # Stamp the tier BEFORE writing: the jsonl is the artifact later
            # analyses read, and a tier computed only into the in-memory counters
            # is invisible to them.
            if rec["ay"] in ("sat", "unsat"):
                rec["tier"] = ay_evidence_tier(rec)
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
            s["DISAGREE"] += bool(rec.get("DISAGREE_Z3EXACT"))
            s["DISAGREE"] += sum(1 for k in rec if k.startswith("DISAGREE_STATUS_"))
            if ad:
                # Tier A is the ONLY thing counted toward the 100% evidence
                # goal: an externally shaped, hole-free Alethe document, or a
                # model the independent gate confirmed. Tier B is internally
                # sealed but has no external surface and is never evidence.
                s["tier" + rec["tier"]] += 1
                if rec["tier"] != "A" and rec.get("cert_unproved_steps", 0) > 0:
                    s["cert_holes"] += 1
                # The size of the old over-count, kept visible on purpose.
                if rec.get("cert_self_checkable") and rec.get("cert_unproved_steps", 0) > 0:
                    s["selfchk_inflated"] += 1
            if not ad: s["r:" + (rec["ay"] if rec["ay"] != "unknown" else rec.get("ay_reason", "?"))] += 1
            if any(k.startswith("DISAGREE") for k in rec): print("DISAGREE", rec, flush=True)
    print()
    print("tierA = evidence (hole-free Alethe, or a gate-confirmed model); tierB = internally")
    print("sealed, no external surface, NEVER counted toward 100%; infl = printed")
    print("ay_self_checkable=yes on a document that carries unproved steps.")
    if BOTH_POSTURES:
        print("apples-to-apples = AY with z3's workload; product = AY's own posture")
        print(f"{'division':22} {'n':>3} {'z3':>3} {'AYx':>4} {'x>z3':>5} {'z3>x':>5} {'AY':>3} {'tierA':>5} {'tierB':>5} {'tierC':>5} {'infl':>4} {'DIS':>3}  ay-unknown reasons")
    else:
        print(f"{'division':22} {'n':>3} {'ay':>3} {'z3':>3} {'both':>4} {'z3only':>6} {'ayonly':>6} {'DIS':>3} {'tierA':>5} {'tierB':>5} {'tierC':>5} {'infl':>4}  ay-unknown reasons")
    tot = collections.Counter()
    for d in divs:
        s = stats[d]
        if not s["n"]: continue
        for k, v in s.items():
            if not k.startswith("r:"):
                tot[k] += v
        reasons = ", ".join(f"{k[2:]}={v}" for k, v in s.most_common() if k.startswith("r:"))
        if BOTH_POSTURES:
            print(f"{d:22} {s['n']:>3} {s['z3']:>3} {s['ay_x']:>4} {s['x_beats_z3']:>5} {s['z3_beats_x']:>5} {s['ay']:>3} {s['tierA']:>5} {s['tierB']:>5} {s['tierC']:>5} {s['selfchk_inflated']:>4} {s['DISAGREE']:>3}  {reasons}")
        else:
            print(f"{d:22} {s['n']:>3} {s['ay']:>3} {s['z3']:>3} {s['both']:>4} {s['z3_only']:>6} {s['ay_only']:>6} {s['DISAGREE']:>3} {s['tierA']:>5} {s['tierB']:>5} {s['tierC']:>5} {s['selfchk_inflated']:>4}  {reasons}")
    decided = tot["ay"]
    if decided:
        pct = 100.0 * tot["tierA"] / decided
        print()
        print(f"TOTAL decided={decided} tierA={tot['tierA']} ({pct:.1f}%) tierB={tot['tierB']} "
              f"tierC={tot['tierC']} inflated-by-flag-alone={tot['selfchk_inflated']} "
              f"disagreements={tot['DISAGREE']}")

if __name__ == "__main__":
    main()
