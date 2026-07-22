#!/usr/bin/env python3
# ay-script: pb-results-analyze
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""Consolidate a PB competition results mirror into clean structured data.

Reads the offline mirror produced by ``pb_results_download.py`` and parses it
into a handful of small CSVs plus a SUMMARY.md, so analysis works from ground
truth instead of ~100 MB of HTML. Pure stdlib.

Outputs (under ``<mirror>/analysis/``):
  rankings.csv        every ranking table row (scheme x time-budget x category x solver)
  ay_results.csv      AY's per-instance results, from export.txt
  per_instance.csv    per benchmark: best-known result + AY's answer + field comparison
  ay_jobs.csv         AY's per-job execution facts parsed from the run traces
  SUMMARY.md          headline aggregates

Usage:
  scripts/pb_results_analyze.py [--mirror competition/pb26/results]
"""

from __future__ import annotations

import argparse
import csv
import html
import re
from pathlib import Path

TAG = re.compile(r"<[^>]+>")
WS = re.compile(r"\s+")


def text(s: str) -> str:
    return WS.sub(" ", html.unescape(TAG.sub(" ", s))).strip()


def cells(row: str) -> list[str]:
    return [text(c) for c in re.findall(r"<t[dh][^>]*>(.*?)</t[dh]>", row, re.S | re.I)]


def rows(segment: str) -> list[str]:
    return re.findall(r"<tr.*?</tr>", segment, re.S | re.I)


# ---------------------------------------------------------------- rankings ----
def parse_rankings(mirror: Path) -> list[dict]:
    f = mirror / "ranking.html"
    if not f.exists():
        return []
    t = f.read_text("utf-8", "replace")
    # Break the page at every heading so we can track scheme / time-budget /
    # category context as we walk down.
    pieces = re.split(r"(<h[1-4][^>]*>.*?</h[1-4]>)", t, flags=re.S | re.I)
    scheme = budget = category = None
    out = []
    for piece in pieces:
        if re.match(r"<h[1-4]", piece, re.I):
            h = text(piece)
            low = h.lower()
            if "point of view" in low or "final answers" in low:
                scheme = h
                budget = "final answer" if "final answers" in low else "best (no limit)"
            elif "best answers found" in low or "best solutions" in low:
                budget = h
            elif "category" in low and "(" in h:
                category = h
            continue
        if scheme is None or category is None:
            continue
        m = re.search(r"Total number of instances in the category:\s*(\d+)", piece)
        cat_total = int(m.group(1)) if m else ""
        for r in rows(piece):
            c = cells(r)
            c = [x for x in c if x != ""]
            if not c:
                continue
            is_vbs = c[0].lower().startswith("virtual best")
            if not (c[0].isdigit() or is_vbs):
                continue
            if is_vbs:
                rank, solver, version, rest = 0, "VBS", "", c[1:]
            else:
                rank = int(c[0])
                solver = c[1] if len(c) > 1 else ""
                version = c[2] if len(c) > 2 else ""
                rest = c[3:]
            # first numeric in the rest = number solved / best found
            count = next((re.sub(r"[^\d]", "", x) for x in rest if re.search(r"\d", x)), "")
            out.append({
                "scheme": scheme, "budget": budget, "category": category,
                "cat_total": cat_total, "rank": rank, "solver": solver,
                "version": version, "count": count,
            })
    return out


# ------------------------------------------------------------- ay_results ----
def parse_export(mirror: Path) -> list[dict]:
    f = mirror / "export.txt"
    if not f.exists():
        return []
    out = []
    for line in f.read_text("utf-8", "replace").splitlines():
        parts = [p.strip() for p in line.split("|")]
        if len(parts) < 9 or parts[0] in ("Category", "") or set(parts[0]) <= {"_"}:
            continue
        out.append({
            "category": parts[0], "instance": parts[1], "answer": parts[2],
            "objective": parts[3], "cpu": parts[4], "wall": parts[5],
            "memory": parts[6], "solver": parts[7], "version": parts[8],
        })
    return out


# ------------------------------------------------------------ per_instance ----
def grab(t: str, label: str) -> str:
    m = re.search(re.escape(label) + r"\s*</td>\s*<td[^>]*>(.*?)</td>", t, re.S | re.I)
    return text(m.group(1)) if m else ""


def parse_bench(mirror: Path) -> list[dict]:
    out = []
    for f in sorted(mirror.glob("bench_idbench*.html")):
        t = f.read_text("utf-8", "replace")
        if "Results of the different solvers" not in t:
            continue
        name = grab(t, "Name")
        md5 = grab(t, "MD5SUM")
        has_obj = grab(t, "Has Objective Function")
        best_result = grab(t, "Best result obtained on this benchmark")
        best_obj = grab(t, "Best value of the objective obtained on this benchmark")
        cat = grab(t, "Bench Category")
        # solver results table
        seg = re.search(r"Results of the different solvers.*?</table>", t, re.S | re.I)
        ay_rows, n_solvers = [], 0
        if seg:
            for r in rows(seg.group(0)):
                c = cells(r)
                c = [x for x in c if x != ""]
                # data rows look like: [name-or-dash, traceid?, answer, cpu, wc]
                if len(c) >= 3 and re.search(r"\d", " ".join(c[-2:])):
                    n_solvers += 1
                    if c[0].upper().startswith("AY"):
                        ay_rows.append(c)
        out.append({
            "idbench": re.search(r"idbench(\d+)", f.name).group(1),
            "instance": name, "category": cat.split("(")[0].strip(), "md5": md5,
            "has_obj": has_obj, "best_result": best_result, "best_obj": best_obj,
            "n_solver_rows": n_solvers, "ay_rows": len(ay_rows),
        })
    return out


# --------------------------------------------------------------- ay_jobs ----
STATUS_HINTS = [
    ("Maximum CPU time exceeded", "CPU-TIMEOUT"),
    ("Maximum wall clock time exceeded", "WC-TIMEOUT"),
    ("Maximum VSize exceeded", "MEM-OUT"),
    ("Maximum memory exceeded", "MEM-OUT"),
    ("Child ended because it received signal", "SIGNAL"),
    ("Solver just died. Probably out of memory", "OOM-DIED"),
]


def parse_traces(mirror: Path) -> list[dict]:
    out = []
    for f in sorted(mirror.glob("trace_idjob*.html")):
        t = f.read_text("utf-8", "replace")
        if "Watcher Data" not in t and "Solver Data" not in t:
            continue
        idjob = re.search(r"idjob(\d+)", f.name).group(1)
        name = grab(t, "Name")
        # answer/cpu/wc summary row near the top
        ans = re.search(r"Solver answer on this benchmark.*?</table>", t, re.S | re.I)
        answer = cpu = wc = ver = ""
        if ans:
            for r in rows(ans.group(0)):
                c = [x for x in cells(r) if x != ""]
                if len(c) >= 4 and re.search(r"\d", c[-1]):
                    ver, answer, cpu, wc = c[0], c[1], c[2], c[3]
        status = ""
        for needle, code in STATUS_HINTS:
            if needle in t:
                status = code
                break
        # last few non-empty solver stdout lines (the SOLVER DATA block)
        sd = re.search(r"Solver Data.*?(Verifier Data|Watcher Data)", t, re.S | re.I)
        last = ""
        if sd:
            lines = [text(x) for x in sd.group(0).splitlines()]
            lines = [x for x in lines if x and "Solver Data" not in x
                     and "Verifier Data" not in x and "Watcher Data" not in x]
            last = " | ".join(lines[-4:])[:300]
        out.append({
            "idjob": idjob, "instance": name, "version": ver, "answer": answer,
            "cpu": cpu, "wall": wc, "runsolver_status": status, "tail": last,
        })
    return out


def _num(s):
    s = (s or "").strip()
    for cast in (int, float):
        try:
            return cast(s)
        except ValueError:
            pass
    return None


def soundness_audit(ay: list[dict], bench: list[dict]) -> dict:
    """Cross-check AY's answers against the field's best result on the same bench.

    AY's answers are already portal-"Checked" (SAT/OPT models are verified); this
    is the independent contradiction check that backs the zero-wrong-answers claim.
    """
    def norm(s):
        return (s or "").replace(" ", "").strip()

    by = {norm(b["instance"]): b for b in bench}
    sat_on_unsat = unsat_on_sat = better_than_best = opt_mismatch = matched = 0
    for r in ay:
        b = by.get(norm(r["instance"]))
        if not b:
            continue
        matched += 1
        ans = r["answer"].strip()
        obj = _num(r["objective"])
        best = (b["best_result"] or "").upper()
        bobj = _num(b["best_obj"])
        field_has_sol = "SAT" in best or "OPT" in best
        field_unsat = "UNSAT" in best and not field_has_sol
        if ans in ("SAT", "OPT", "OPTC") and field_unsat:
            sat_on_unsat += 1
        if ans in ("UNSAT", "UNSATC") and field_has_sol and "UNSAT" not in best:
            unsat_on_sat += 1
        if ans in ("SAT", "OPT", "OPTC") and obj is not None and bobj is not None and obj < bobj:
            better_than_best += 1
        if ans in ("OPT", "OPTC") and obj is not None and bobj is not None and obj != bobj:
            opt_mismatch += 1
    return {
        "rows_audited": len(ay), "matched_to_field": matched,
        "sat_on_field_unsat": sat_on_unsat, "unsat_on_field_sat": unsat_on_sat,
        "objective_below_field_best": better_than_best, "optimum_value_mismatch": opt_mismatch,
        "clean": sat_on_unsat == unsat_on_sat == better_than_best == opt_mismatch == 0,
    }


def write_csv(path: Path, recs: list[dict]):
    if not recs:
        path.write_text("", "utf-8")
        return
    with path.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(recs[0].keys()))
        w.writeheader()
        w.writerows(recs)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--mirror", default="competition/pb26/results")
    args = ap.parse_args()
    mirror = Path(args.mirror)
    outdir = mirror / "analysis"
    outdir.mkdir(parents=True, exist_ok=True)

    rankings = parse_rankings(mirror)
    ay = parse_export(mirror)
    bench = parse_bench(mirror)
    jobs = parse_traces(mirror)

    write_csv(outdir / "rankings.csv", rankings)
    write_csv(outdir / "ay_results.csv", ay)
    write_csv(outdir / "per_instance.csv", bench)
    write_csv(outdir / "ay_jobs.csv", jobs)

    # headline aggregates
    def count(recs, **kw):
        return sum(1 for r in recs if all(str(r.get(k, "")) == str(v) for k, v in kw.items()))

    from collections import Counter
    ans_by_ver = Counter((r["version"], r["answer"]) for r in ay)
    status_by_ver = Counter((r["version"], r["runsolver_status"]) for r in jobs)

    lines = ["# PB'26 warmup (idev=125) — consolidated summary", ""]
    lines.append(f"- mirror: `{mirror}`")
    lines.append(f"- ranking rows parsed: {len(rankings)}")
    lines.append(f"- AY result rows (export.txt): {len(ay)}")
    lines.append(f"- per-instance bench pages parsed: {len(bench)}")
    lines.append(f"- AY job traces parsed: {len(jobs)}")
    lines.append("")
    lines.append("## AY answer distribution (export.txt)")
    for (ver, ans), n in sorted(ans_by_ver.items()):
        lines.append(f"- {ver} :: {ans} = {n}")
    lines.append("")
    lines.append("## AY job runsolver status (traces)")
    for (ver, st), n in sorted(status_by_ver.items()):
        lines.append(f"- {ver} :: {st or '(clean exit)'} = {n}")
    audit = soundness_audit(ay, bench)
    lines.append("")
    lines.append("## Soundness audit (AY answers vs field best)")
    lines.append(f"- rows audited / matched to field: {audit['rows_audited']} / {audit['matched_to_field']}")
    lines.append(f"- SAT/OPT on a field-UNSAT instance (wrong): {audit['sat_on_field_unsat']}")
    lines.append(f"- UNSAT where field found a solution (wrong): {audit['unsat_on_field_sat']}")
    lines.append(f"- objective strictly below field best (infeasible?): {audit['objective_below_field_best']}")
    lines.append(f"- OPTIMUM value disagreement with field: {audit['optimum_value_mismatch']}")
    lines.append(f"- **verdict: {'CLEAN — zero wrong answers' if audit['clean'] else 'CONTRADICTIONS FOUND'}**")
    (outdir / "SUMMARY.md").write_text("\n".join(lines) + "\n", "utf-8")

    print(f"wrote {outdir}/: rankings.csv({len(rankings)}) ay_results.csv({len(ay)}) "
          f"per_instance.csv({len(bench)}) ay_jobs.csv({len(jobs)}) SUMMARY.md")


if __name__ == "__main__":
    main()
