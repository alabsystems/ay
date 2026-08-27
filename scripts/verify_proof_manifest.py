#!/usr/bin/env python3
# ay-script: proof-manifest-verifier
"""Verify retained SAT certificates OUTSIDE the solve budget, then score.

Why this exists
---------------
``~/ay-bench/bin/ay-proofmode`` used to run ``dsr-trim`` inline, inside the
region ``scripts/sweep.py`` hard-kills at ``timeout_s + 20``.  On an instance
where AY solved late and the proof was large, the process group was SIGKILLed
*mid-verification* and the sweep booked a TIMEOUT for an instance AY had already
SOLVED.  In ``~/ay-bench/proofmode-full400-aug25.json`` that is exactly the 8
rows with ``rc=-9`` at wall 320.08-320.11 s -- all ground-truth UNSAT, all
solved by 27-28 of the official field.  ``vdw_4_7_n109`` reproduces it: AY
answers ``s UNSATISFIABLE`` in 157.9 s with a 1.33 GB proof, and dsr-trim needs
another ~205 s on it; 157.9 + 205.6 = 363 s > the 320 s hard kill.

SAT-COMP verifies proofs OFFLINE, after the run; checker time is never charged
to the solver's budget.  Charging it, as the harness did, biased the undercount
toward precisely the instances the campaign cares about: hard UNSAT with big
proofs.

The honest-score rule is MOVED, not weakened.  An UNSAT still counts only when
an external checker accepts its certificate -- it just happens here, on its own
generous budget, instead of on the solver's.

Pipeline
--------
1. ``ay-proofmode`` runs AY, echoes its output, and on rc=20 retains the proof,
   writes ``<manifest>/pending/<token>.json`` (atomic tmp+rename) and exits 20
   immediately.  Nothing about checking is inside the timed region.
2. ``verify_proof_manifest.py drain`` claims rows by an atomic rename into
   ``claimed/``, runs ``dsr-trim <cnf> <proof>`` under its own timeout (default
   1800 s), writes ``verdicts/<token>.json``, and DELETES the proof.  Safe to
   run concurrently with the sweep and safe to run in several processes: the
   rename is the lock.
3. ``verify_proof_manifest.py score`` joins a sweep JSON against the verdicts
   directory and reports the honest count.

The three configurations
------------------------
Read this before quoting any number from a sweep.  This campaign kept
mis-measuring because the distinction lived in people's heads, not the tooling.

  (1) ``--competition --no-proof``   [== ``--rigor fast``, no certificate]
      NOT what ships.  Every campaign number before 2026-08-09 is this.  An
      UPPER BOUND only; never report it as a score.

  (2) ``--competition --proof P --proof-format drat --no-verify-proof``
      [== ``--rigor fast`` + an explicit certificate]
      WHAT THE SUBMISSION ACTUALLY RUNS -- ``prepare_sat26_submission.sh:784``
      asserts every generated ``run.sh`` passes exactly this.  A proof is
      WRITTEN but deliberately NOT re-checked in-process, because the
      organizers verify offline.  **This configuration's wall time is the solve
      time**, and its solved count is the figure comparable with the official
      field's 276.  ``~/ay-bench/bin/ay-proofmode`` is configuration (2).

  (3) (2) plus offline certificate verification -- the honest,
      disqualification-safe score.  ``drain`` here IS that offline pass.

``score`` therefore prints two headline numbers side by side and never blends
them: **SOLVED (competition mode)**, priced at AY's own wall clock and the basis
for PAR-2, and **SCORED (certificate accepted)**.

Dev is not competition mode
---------------------------
AY's default rigor level is ``standard``: runtime result validation ON, default
proof emission ON, and the emitted proof re-checked afterward (the built-in
``--verify-proof``).  So a bare ``ay solve --proof ...`` **already checks its own
work** -- for everyday development and CI that alarm stays on, and it is the
cheapest soundness check this project has.  ``--competition`` (== ``--rigor
fast``) is the documented exception that turns it off, used here *only* for
measurement fidelity with the submission; ``--rigor strict`` and ``--rigor
certified`` sit above ``standard``.  **The deferred external pass in this file
exists precisely because competition mode gives up the built-in re-check.**
Nothing here changes a developer-facing or test default.  The same checker is
available for an ordinary dev artefact via ``verify-now``.

Per-instance status (``score`` never collapses these):
  * ``solved+verified``   -- AY answered and an external checker accepted.  A win.
  * ``solved+model``      -- AY answered SAT.  The model is its own certificate;
                             the campaign rule requires an external one for UNSAT
                             only.  Stated rather than folded into "verified".
  * ``solved+rejected``   -- AY answered UNSAT, the checker REFUSED.  Not a win,
                             and a soundness alarm; ``score`` exits 2.
  * ``solved+unverified`` -- a verdict EXISTS and is not an acceptance (checker
                             timed out / crashed / was killed, or the proof was
                             dropped for disk).  NOT a win.
  * ``solved+unmeasured`` -- NO verdict row exists at all.  Distinct from
                             ``unverified`` on purpose: this is an ABSENT
                             measurement, not a failed one, and it means the
                             score cannot be reproduced from what is on disk.
                             The usual cause is a deleted verdict JSON.  Booking
                             it as ``unverified`` would silently degrade a
                             healthy run toward the alarming direction, so it
                             gets its own bucket and ``score`` exits 3.
  * ``unsolved``          -- timeout / memout / unknown / error.

Verdict JSONs are small and are the durable record of a measurement: ``drain``
deletes the multi-GB PROOF once checked, never the verdict, and ``gc`` touches
only AY's ``.ay-dimacs-proof-*`` staging.  Do not prune ``verdicts/``.

Disk budget
-----------
Peak bytes  <=  RETAIN_CAP  +  W_solve x MAX_IN_FLIGHT_PROOF

``RETAIN_CAP`` (default 64 GiB, ``AY_PROOF_RETAIN_CAP_BYTES``) bounds the
finished-but-unverified queue and is enforced by the wrapper as
refusal-to-retain: a solve that would breach it drops its certificate and is
booked ``unverified`` -- visible, never a silent win.  A second gate refuses to
retain when the filesystem drops below ``AY_PROOF_FREE_FLOOR_KB`` (100 GiB).
The queue is drained -- and each proof deleted -- by ``drain``, so it does not
grow monotonically.  The in-flight term is the proof a running AY is still
writing; it is the solver's, not ours, and on this corpus AY's staging file has
been observed at 36 GB, so at 6 workers the whole bound is ~280 GB.

``gc`` reclaims AY's orphaned ``.ay-dimacs-proof-*`` staging entries -- the ones
a SIGKILLed run leaves behind.  (2026-08-25: 544 GB of them had accumulated in
``~/ay-bench/proofs``.)

Usage
-----
  verify_proof_manifest.py drain  [--manifest DIR] [--checker PATH]
                                  [--timeout 1800] [--jobs 1] [--watch SECONDS]
  verify_proof_manifest.py score  --sweep sweep.json [--manifest DIR]
  verify_proof_manifest.py status [--manifest DIR]
  verify_proof_manifest.py gc     [--proof-dir DIR] [--age-hours 6] [--apply]
"""
import argparse
import concurrent.futures as cf
import glob
import json
import os
import re
import signal
import subprocess
import sys
import time

DEFAULT_MANIFEST = os.path.expanduser("~/ay-bench/proof-manifest")
DEFAULT_CHECKER = os.path.expanduser("~/ay-bench/bin/dsr-trim")
DEFAULT_PROOF_DIR = os.path.expanduser("~/ay-bench/proofs")
ACCEPT_RE = re.compile(rb"s VERIFIED UNSAT")

# Statuses. Only VERIFIED counts toward a score.
VERIFIED = "verified"
REJECTED = "rejected"
UNVERIFIED = "unverified"


def _dirs(manifest):
    return (os.path.join(manifest, "pending"),
            os.path.join(manifest, "claimed"),
            os.path.join(manifest, "verdicts"))


def ensure_dirs(manifest):
    for d in _dirs(manifest):
        os.makedirs(d, exist_ok=True)


def _read_row(path):
    try:
        with open(path) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return None


def write_verdict(manifest, token, row):
    """Publish one verdict atomically so a concurrent `score` never half-reads it."""
    _, _, vdir = _dirs(manifest)
    os.makedirs(vdir, exist_ok=True)
    tmp = os.path.join(vdir, f".{token}.{os.getpid()}.tmp")
    with open(tmp, "w") as fh:
        json.dump(row, fh)
        fh.write("\n")
    os.replace(tmp, os.path.join(vdir, f"{token}.json"))


def claim(manifest, pending_path):
    """Atomically take ownership of a pending row. None if someone else won."""
    _, cdir, _ = _dirs(manifest)
    dest = os.path.join(cdir, os.path.basename(pending_path))
    try:
        os.rename(pending_path, dest)
    except OSError:
        return None
    return dest


def run_checker(checker, cnf, proof, timeout_s):
    """Run the external checker on its OWN budget. Never the solver's."""
    start = time.monotonic()
    try:
        proc = subprocess.Popen([checker, cnf, proof],
                                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                start_new_session=True)
    except OSError as exc:
        return UNVERIFIED, 0.0, None, f"checker-spawn-failed: {exc}"
    try:
        out, _ = proc.communicate(timeout=timeout_s)
        wall = time.monotonic() - start
        if ACCEPT_RE.search(out or b""):
            return VERIFIED, wall, proc.returncode, "s VERIFIED UNSAT"
        # The checker ran to completion and did NOT accept. That is a rejection,
        # not an inconvenience: it must never be counted.
        tail = (out or b"").decode("utf-8", "replace").strip().splitlines()
        return REJECTED, wall, proc.returncode, (tail[-1][:200] if tail else "no output")
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except OSError:
            proc.kill()
        proc.communicate()
        return UNVERIFIED, time.monotonic() - start, None, f"checker-timeout>{timeout_s}s"


def verify_one(manifest, claimed_path, checker, timeout_s, keep_proof=False):
    row = _read_row(claimed_path)
    token = os.path.basename(claimed_path)[:-len(".json")]
    if row is None:
        verdict = {"token": token, "status": UNVERIFIED, "note": "unreadable-manifest-row"}
        write_verdict(manifest, token, verdict)
        os.remove(claimed_path)
        return verdict
    cnf, proof = row.get("cnf", ""), row.get("proof", "")
    if not proof or not os.path.exists(proof) or os.path.getsize(proof) == 0:
        status, wall, rc, note = UNVERIFIED, 0.0, None, "proof-missing-or-empty"
    elif not os.path.exists(cnf):
        status, wall, rc, note = UNVERIFIED, 0.0, None, "cnf-missing"
    else:
        status, wall, rc, note = run_checker(checker, cnf, proof, timeout_s)
    verdict = dict(row)
    verdict.update({"status": status, "checker_wall_s": round(wall, 2),
                    "checker_rc": rc, "note": note, "checker": checker,
                    "checker_timeout_s": timeout_s,
                    "verified_epoch": int(time.time())})
    write_verdict(manifest, token, verdict)
    # Delete the proof whatever the outcome -- that is what keeps the retained
    # set bounded. The verdict, not the artefact, is the durable record.
    if not keep_proof and proof and os.path.exists(proof):
        try:
            os.remove(proof)
        except OSError:
            pass
    try:
        os.remove(claimed_path)
    except OSError:
        pass
    return verdict


def cmd_drain(args):
    manifest = args.manifest
    ensure_dirs(manifest)
    pdir, cdir, _ = _dirs(manifest)
    # A drain that was itself killed leaves rows stranded in claimed/, and
    # nothing ever picks them up again: `drain` only reads pending/. Those rows
    # then score as `solved+unmeasured` forever -- a real solve quietly demoted
    # to a non-win. That is exactly what happened on 2026-08-26: 38 rows sat in
    # claimed/ for hours while a drain loop next to them reported "drained 0
    # row(s); 0 still pending" over and over.
    #
    # So reclaim by AGE, automatically. A row whose claim is older than twice
    # the checker timeout cannot still be under a live checker -- that checker
    # would have been killed by its own budget long ago. Rows younger than that
    # are left alone, so this never races a drain that is genuinely working.
    # --requeue-claimed keeps the unconditional form for the case where you KNOW
    # no other drain is running.
    stranded_after = 2 * args.timeout
    now = time.time()
    for p in sorted(glob.glob(os.path.join(cdir, "*.json"))):
        try:
            if not args.requeue_claimed and now - os.path.getmtime(p) < stranded_after:
                continue
            os.rename(p, os.path.join(pdir, os.path.basename(p)))
        except OSError:
            pass
    deadline = time.monotonic() + args.watch if args.watch else None
    done = 0
    while True:
        rows = sorted(glob.glob(os.path.join(pdir, "*.json")))
        claimed = [c for c in (claim(manifest, r) for r in rows) if c]
        if claimed:
            if args.jobs > 1:
                with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
                    futs = [ex.submit(verify_one, manifest, c, args.checker,
                                      args.timeout, args.keep_proof)
                            for c in claimed]
                    for f in cf.as_completed(futs):
                        v = f.result()
                        done += 1
                        print(f"  [{v['status']:10s}] {v.get('token')} "
                              f"checker={v.get('checker_wall_s')}s {v.get('note','')}",
                              flush=True)
            else:
                for c in claimed:
                    v = verify_one(manifest, c, args.checker, args.timeout,
                                   args.keep_proof)
                    done += 1
                    print(f"  [{v['status']:10s}] {v.get('token')} "
                          f"checker={v.get('checker_wall_s')}s {v.get('note','')}",
                          flush=True)
        if deadline is None:
            break
        if time.monotonic() >= deadline:
            break
        time.sleep(args.poll)
    remaining = len(glob.glob(os.path.join(pdir, "*.json")))
    print(f"drained {done} row(s); {remaining} still pending", flush=True)
    return 0


def load_verdicts(manifest):
    _, _, vdir = _dirs(manifest)
    by_cnf = {}
    for p in sorted(glob.glob(os.path.join(vdir, "*.json"))):
        row = _read_row(p)
        if not row:
            continue
        key = os.path.basename(row.get("cnf", "")) or row.get("token", "")
        # Several rows can exist for one CNF (A/B arms, retries). An accepted
        # certificate for the instance is what the campaign rule asks for, so a
        # verified row wins; otherwise keep the most informative failure.
        rank = {VERIFIED: 3, REJECTED: 2, UNVERIFIED: 1}
        cur = by_cnf.get(key)
        if cur is None or rank.get(row.get("status"), 0) > rank.get(cur.get("status"), 0):
            by_cnf[key] = row
    return by_cnf


def cmd_status(args):
    ensure_dirs(args.manifest)
    pdir, cdir, _ = _dirs(args.manifest)
    pend = sorted(glob.glob(os.path.join(pdir, "*.json")))
    claimed = sorted(glob.glob(os.path.join(cdir, "*.json")))
    retained = 0
    for p in pend + claimed:
        row = _read_row(p) or {}
        retained += int(row.get("proof_bytes") or 0)
    verdicts = load_verdicts(args.manifest)
    counts = {}
    for v in verdicts.values():
        counts[v.get("status", "?")] = counts.get(v.get("status", "?"), 0) + 1
    print(f"manifest: {args.manifest}")
    print(f"  pending : {len(pend)}")
    print(f"  claimed : {len(claimed)}")
    print(f"  verdicts: {len(verdicts)}  {counts}")
    print(f"  retained proof bytes (pending+claimed): {retained/1e9:.2f} GB")
    cap = int(os.environ.get("AY_PROOF_RETAIN_CAP_BYTES", 68719476736))
    print(f"  retain cap: {cap/1e9:.2f} GB  -> headroom {(cap-retained)/1e9:.2f} GB")
    return 0


# The three configurations this campaign has conflated. A number from one is
# never a number from another, so the scorer always names the one it was given.
CONFIGURATIONS = {
    "no-proof": (
        "(1) --competition --no-proof -- NOT what ships. Every campaign number "
        "before 2026-08-09 is this. UPPER BOUND ONLY; never report as a score."),
    "competition": (
        "(2) --competition --proof P --proof-format drat --no-verify-proof -- "
        "what the submission actually runs. A proof is WRITTEN, not checked "
        "inline. This configuration's WALL TIME is the solve time, and its "
        "solved count is the figure comparable to the official field's 276."),
    "competition+offline-verify": (
        "(3) configuration (2) plus OFFLINE certificate verification -- the "
        "honest, disqualification-safe score. Checker time is never in the "
        "solver's budget, exactly as SAT-COMP does it."),
    "UNRECORDED": (
        "sweep JSON predates the configuration field and none was asserted via "
        "--config. TREAT EVERY NUMBER BELOW AS UNATTRIBUTED."),
}


def _solve_seconds(sweep_row, verdict_row):
    """AY's OWN wall clock for this row, in seconds, with its provenance.

    Configuration (2) is priced at the solver's clock, not the harness's: the
    harness clock carries wrapper fork overhead and -- before this fix -- the
    external checker's entire runtime.
    """
    ms = (verdict_row or {}).get("ay_wall_ms")
    if ms is None:
        ms = sweep_row.get("solver_wall_ms")
    if ms is not None and ms >= 0:
        return round(ms / 1000.0, 3), "solver"
    return sweep_row.get("time"), "harness"


def cmd_score(args):
    sweep = json.load(open(args.sweep))
    verdicts = load_verdicts(args.manifest)
    config = args.config or sweep.get("solver_configuration") or "UNRECORDED"
    timeout = float(sweep.get("timeout_s") or 0.0)
    rows = []
    for r in sweep["results"]:
        cnf = r["cnf"]
        v = verdicts.get(cnf)
        verdict = r["verdict"]
        if verdict == "unsat":
            if v is None:
                # NOT the same thing as a checker that ran and declined. No
                # verdict row means the measurement is ABSENT -- the usual
                # cause is that the verdict JSON was deleted, which makes the
                # score irreproducible. Booking it as "unverified" would
                # silently degrade a healthy run toward the alarming
                # direction, so it gets its own bucket and its own alarm.
                status, note = "solved+unmeasured", "no verdict row"
            elif v.get("status") == VERIFIED:
                status, note = "solved+verified", v.get("note", "")
            elif v.get("status") == REJECTED:
                status, note = "solved+rejected", v.get("note", "")
            else:
                status, note = "solved+unverified", v.get("note", "")
        elif verdict == "sat":
            # Parity with the pre-fix wrapper: the campaign rule requires an
            # external certificate for UNSAT only. Stated explicitly rather
            # than silently folded into "verified".
            status, note = "solved+model", "sat: no external certificate required"
        else:
            status, note = "unsolved", verdict
        solve_s, clock = _solve_seconds(r, v)
        rows.append({"cnf": cnf, "sweep_verdict": verdict,
                     "solve_seconds": solve_s, "solve_clock": clock,
                     "harness_time": r.get("time"), "rc": r.get("rc"),
                     "status": status,
                     "checker_wall_s": (v or {}).get("checker_wall_s"),
                     "proof_bytes": (v or {}).get("proof_bytes"), "note": note})
    counts = {k: 0 for k in ("solved+verified", "solved+model", "solved+rejected",
                             "solved+unverified", "solved+unmeasured", "unsolved")}
    for row in rows:
        counts[row["status"]] = counts.get(row["status"], 0) + 1

    solved = len(rows) - counts["unsolved"]          # configuration (2)
    scored = counts["solved+verified"] + counts["solved+model"]   # configuration (3)
    harness_clocked = sum(1 for r in rows if r["solve_clock"] == "harness")

    def par2(counted):
        tot = 0.0
        for r in rows:
            if r["status"] in counted and r["solve_seconds"] is not None:
                tot += r["solve_seconds"]
            else:
                tot += 2 * timeout
        return tot

    solved_set = {"solved+verified", "solved+model", "solved+rejected",
                  "solved+unverified", "solved+unmeasured"}
    scored_set = {"solved+verified", "solved+model"}
    p2_solved, p2_scored = par2(solved_set), par2(scored_set)
    n = max(1, len(rows))

    rejected = [r for r in rows if r["status"] == "solved+rejected"]
    unverified = [r for r in rows if r["status"] == "solved+unverified"]
    unmeasured = [r for r in rows if r["status"] == "solved+unmeasured"]

    print(f"sweep        : {args.sweep}")
    print(f"manifest     : {args.manifest}")
    print(f"instances    : {len(rows)}   local timeout {timeout:g}s")
    print(f"configuration: {config}")
    print(f"               {CONFIGURATIONS.get(config, 'UNKNOWN LABEL')}")
    if harness_clocked:
        print(f"               NOTE: {harness_clocked} row(s) priced at the "
              f"HARNESS clock (no solver wall_time_ms available)")
    print()
    print("  ==================================================================")
    print(f"  SOLVED (competition mode, config 2) : {solved:3d}/{len(rows)}"
          f"   PAR-2 sum {p2_solved:>10.1f}  mean {p2_solved/n:>8.1f}")
    print(f"  SCORED (certificate accepted, cfg 3): {scored:3d}/{len(rows)}"
          f"   PAR-2 sum {p2_scored:>10.1f}  mean {p2_scored/n:>8.1f}")
    print("  ==================================================================")
    print("  SOLVED is the figure comparable to the official field's solved")
    print("  counts (organizers check proofs offline; checker time is never in")
    print("  the solver's budget). SCORED is what we may claim as an honest")
    print("  standing. They are never the same number and never blended.")
    print()
    print("  per-row status (printed even at zero, so an unverified pile can")
    print("  never masquerade as a healthy run):")
    for k in ("solved+verified", "solved+model", "solved+rejected",
              "solved+unverified", "solved+unmeasured", "unsolved"):
        print(f"    {k:20s} {counts[k]:4d}")
    if rejected:
        print(f"\n*** {len(rejected)} REJECTED CERTIFICATE(S) -- POTENTIAL "
              f"DISQUALIFICATION, NOT A ROUNDING ERROR ***")
        for r in rejected:
            print(f"    {r['cnf']}: {r['note']}")
    if unverified:
        print(f"\n!!! {len(unverified)} SOLVED-BUT-UNVERIFIED: counted in SOLVED, "
              f"NOT in SCORED !!!")
        for r in unverified:
            print(f"    {r['cnf']}: {r['note']}")
    if unmeasured:
        print(f"\n### {len(unmeasured)} SOLVED-BUT-UNMEASURED: no verdict row "
              f"exists, so this score is NOT REPRODUCIBLE ###")
        print("    A missing verdict is an ABSENT measurement, not a failed")
        print("    one -- the usual cause is a deleted verdict JSON. Re-drain")
        print("    the manifest or restore the verdicts before quoting this.")
        for r in unmeasured[:10]:
            print(f"    {r['cnf']}: {r['note']}")
        if len(unmeasured) > 10:
            print(f"    ... and {len(unmeasured) - 10} more")
    if args.out:
        with open(args.out, "w") as fh:
            json.dump({"sweep": args.sweep, "manifest": args.manifest,
                       "solver_configuration": config,
                       "configuration_note": CONFIGURATIONS.get(config),
                       "timeout_s": timeout, "counts": counts,
                       "solved_competition_mode": solved, "scored": scored,
                       "par2_solved_sum": round(p2_solved, 1),
                       "par2_solved_mean": round(p2_solved / n, 1),
                       "par2_scored_sum": round(p2_scored, 1),
                       "par2_scored_mean": round(p2_scored / n, 1),
                       "rows_priced_at_harness_clock": harness_clocked,
                       "n_instances": len(rows), "rows": rows}, fh, indent=2)
        print(f"\nwrote {args.out}")
    # A rejected certificate is a soundness alarm; make it impossible to miss in
    # a pipeline that only looks at exit codes. An unmeasured row is a weaker
    # but still disqualifying-for-quotation condition: the number cannot be
    # reproduced from what is on disk.
    if rejected:
        return 2
    return 3 if unmeasured else 0


def cmd_verify_now(args):
    """Point the same external checker at one ordinary (non-sweep) artefact.

    The machinery is not sweep-only: a developer who produced a proof by hand --
    or who ran with ``--competition`` and so gave up AY's built-in re-check --
    can get the same external verdict here without a manifest.
    """
    status, wall, rc, note = run_checker(args.checker, args.cnf, args.proof,
                                         args.timeout)
    size = os.path.getsize(args.proof) if os.path.exists(args.proof) else 0
    print(f"cnf     : {args.cnf}")
    print(f"proof   : {args.proof}  ({size/1e6:.1f} MB)")
    print(f"checker : {args.checker}  budget {args.timeout:g}s")
    print(f"verdict : {status.upper()}  ({wall:.2f}s, rc={rc})  {note}")
    if args.delete and status != UNVERIFIED and os.path.exists(args.proof):
        os.remove(args.proof)
        print("proof deleted")
    return {VERIFIED: 0, REJECTED: 2}.get(status, 1)


def cmd_gc(args):
    """Reclaim AY proof-staging entries orphaned by a killed run."""
    now = time.time()
    victims, total = [], 0
    for p in glob.glob(os.path.join(args.proof_dir, ".ay-dimacs-proof-*")):
        try:
            st = os.stat(p)
        except OSError:
            continue
        age_h = (now - st.st_mtime) / 3600.0
        if age_h < args.age_hours:
            continue
        m = re.search(r"\.ay-dimacs-proof-(\d+)-", os.path.basename(p))
        if m:
            try:
                os.kill(int(m.group(1)), 0)
                continue          # owner still alive: leave it alone
            except (OSError, ProcessLookupError):
                pass
        if os.path.isdir(p):
            sz = sum(os.path.getsize(os.path.join(dp, f))
                     for dp, _, fs in os.walk(p) for f in fs
                     if os.path.exists(os.path.join(dp, f)))
        else:
            sz = st.st_size
        victims.append((p, sz))
        total += sz
    print(f"{len(victims)} orphaned staging entr(ies), {total/1e9:.2f} GB, "
          f"older than {args.age_hours}h with no live owner")
    if not args.apply:
        print("(dry run; pass --apply to delete)")
        return 0
    import shutil
    for p, _ in victims:
        try:
            shutil.rmtree(p) if os.path.isdir(p) else os.remove(p)
        except OSError as exc:
            print(f"  could not remove {p}: {exc}")
    print(f"reclaimed {total/1e9:.2f} GB")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    d = sub.add_parser("drain", help="verify pending certificates out-of-band")
    d.add_argument("--manifest", default=DEFAULT_MANIFEST)
    d.add_argument("--checker", default=DEFAULT_CHECKER)
    d.add_argument("--timeout", type=float, default=1800.0,
                   help="per-certificate checker budget in SECONDS (default 1800); "
                        "this is the checker's own budget and is never charged "
                        "to the solver")
    d.add_argument("--jobs", type=int, default=1)
    d.add_argument("--watch", type=float, default=0.0,
                   help="keep draining for this many seconds (run alongside a sweep)")
    d.add_argument("--poll", type=float, default=10.0)
    d.add_argument("--keep-proof", action="store_true",
                   help="do not delete the proof after checking (debug only; "
                        "breaks the retained-set bound)")
    d.add_argument("--requeue-claimed", action="store_true",
                   help="requeue EVERY claimed row immediately, regardless of "
                        "age. Rows stranded longer than 2x --timeout are "
                        "requeued automatically anyway; use this only when you "
                        "know no other drain is running, since it will also "
                        "steal rows a live drain is still checking")
    d.set_defaults(func=cmd_drain)

    s = sub.add_parser("score", help="join a sweep JSON against the verdicts")
    s.add_argument("--sweep", required=True)
    s.add_argument("--manifest", default=DEFAULT_MANIFEST)
    s.add_argument("--config", choices=sorted(CONFIGURATIONS),
                   help="assert which of the three configurations produced the "
                        "sweep, for JSONs written before sweep.py recorded it")
    s.add_argument("--out")
    s.set_defaults(func=cmd_score)

    vn = sub.add_parser("verify-now",
                        help="externally check one proof (dev runs, not just sweeps)")
    vn.add_argument("--cnf", required=True)
    vn.add_argument("--proof", required=True)
    vn.add_argument("--checker", default=DEFAULT_CHECKER)
    vn.add_argument("--timeout", type=float, default=1800.0)
    vn.add_argument("--delete", action="store_true",
                    help="remove the proof once a conclusive verdict exists")
    vn.set_defaults(func=cmd_verify_now)

    t = sub.add_parser("status", help="pending / claimed / retained bytes")
    t.add_argument("--manifest", default=DEFAULT_MANIFEST)
    t.set_defaults(func=cmd_status)

    g = sub.add_parser("gc", help="reclaim orphaned AY proof-staging entries")
    g.add_argument("--proof-dir", default=DEFAULT_PROOF_DIR)
    g.add_argument("--age-hours", type=float, default=6.0)
    g.add_argument("--apply", action="store_true")
    g.set_defaults(func=cmd_gc)

    args = ap.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
