#!/usr/bin/env python3
# ay-script: lever-eligibility
"""Compute the ELIGIBLE POPULATION of each default-OFF SAT lever over a corpus.

Why this exists
---------------
Three levers landed default-OFF and contribute nothing until a measurement
flips them.  A naive full-400 A/B per lever costs ~10 h each AND DILUTES the
signal: most instances cannot reach the flag at all, so their two rows are
byte-identical and contribute nothing but timing variance.  This script reads
`p cnf <vars> <clauses>` headers (cheap, header-only I/O) and applies each
lever's own gate arithmetic to produce the subset where the arm can possibly
differ from base.

Every threshold below is read off the source, and every one carries its
`file:line`.  If a constant moves, re-read this file against it -- a stale
population silently measures base against base and reports a guaranteed null.

The three levers
----------------
1. `--sat-vivify-converge`   (05d1b59745)
2. `--sat-mode-equiticks-large` (8776347a35)
3. `--sat-bve-giant-raw`     (3ee1ae5497)

Direction of approximation
--------------------------
Every gate that cannot be decided from a header is OVER-approximated, never
under-approximated.  An over-approximation costs run time on instances whose
two arms turn out identical; an under-approximation silently deletes the
instances the lever exists for.  Each over-approximation is named in the
emitted JSON under `over_approximations` so a reader can see exactly which
rows are speculative.

Usage
-----
  scripts/lever_eligibility.py \
      --corpus ~/ay-bench/main2026-full/cnf \
      --truth benchmarks/sat/satcomp2026-main-truth.json \
      --reference-sweep ~/ay-bench/proofmode-full400-aug25-corrected.json \
      --timeout 300 --workers 6 --outdir ~/ay-bench/lever-ab
"""
import argparse
import glob
import json
import os
import subprocess
import sys

# ---------------------------------------------------------------------------
# GATE CONSTANTS.  Each is quoted from the source with its file:line so this
# file can be re-verified by reading, not by trusting a summary.
# ---------------------------------------------------------------------------

# FormulaClass::classify -- crates/ay-sat/src/solver/constants.rs:1890-1898
#   Large if num_vars >= PREPROCESS_EXPENSIVE_MAX_VARS
#            or active_clauses >= PREPROCESS_EXPENSIVE_MAX_CLAUSES
#   Small if num_vars < 10_000 and active_clauses < 100_000
FORMULA_CLASS_SMALL_MAX_VARS = 10_000            # constants.rs:1893
FORMULA_CLASS_SMALL_MAX_CLAUSES = 100_000        # constants.rs:1893
PREPROCESS_EXPENSIVE_MAX_VARS = 200_000          # constants.rs:1401
PREPROCESS_EXPENSIVE_MAX_CLAUSES = 3_000_000     # constants.rs:1415

# PreprocessPolicy::skip_dense_formula_elim_raised
#   -- crates/ay-sat/src/solver/config_preprocess_policy.rs:730-737
#   (active_clauses > PREPROCESS_EXPENSIVE_MAX_CLAUSES
#     and density > PREPROCESS_BVE_SKIP_DENSITY) or density > BVE_HIGH_DENSITY_SKIP
PREPROCESS_BVE_SKIP_DENSITY = 20.0               # constants.rs:1078
BVE_HIGH_DENSITY_SKIP = 50.0                     # constants.rs:1089

# Very-large stabilization band -- crates/ay-sat/src/solver/constants.rs:491,
# read at crates/ay-sat/src/solver/solve/mod.rs:920 against
# `self.num_original_clauses`, which solve/mod.rs:484 sets to
# `self.arena.irredundant_count()` -- a POST-preprocessing count, not the header.
VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD = 1_000_000

# Giant raw-BVE band -- crates/ay-sat/src/variant.rs:1093-1122, all read off
# `self.input.num_vars()` / `num_clauses()`, i.e. the PARSED counts.
BVE_SPARSE_MAX_VARS = 150_000                    # variant.rs:517
BVE_GIANT_RAW_MAX_VARS = 2_000_000               # variant.rs:561
BVE_GIANT_RAW_MAX_CLAUSES = 10_000_000           # variant.rs:588
BVE_SPARSE_MAX_DENSITY = 12.0                    # variant.rs:499

# Auto-route bands that STEAL instances away from SolverVariant::Default and
# therefore disarm the giant raw-BVE route at variant.rs:1097.  Both need
# `num_binary`, which a header does not carry -- see --scan-binary.
AUTO_ROUTE_MIN_BINARY_FRACTION = 0.70            # features.rs:104, features.rs:144
PROBE_MAX_CLAUSE_VAR_RATIO = 4.0                 # features.rs:105
PROBE_MIN_VARS = 50_000                          # features.rs:114
PROBE_MAX_VARS = 3_000_000                       # features.rs:115
AGGRESSIVE_MAX_CLAUSE_VAR_RATIO = 6.5            # features.rs:149
AGGRESSIVE_MIN_VARS = 50_000                     # features.rs:155
AGGRESSIVE_MAX_VARS = 250_000                    # features.rs:156

# Header-margin multiplier for gates read against POST-preprocessing counts.
# Preprocessing (units, subsumption, BVE) usually SHRINKS a formula, so an
# instance whose header sits above a "< X" gate can still land under it by the
# time the gate is read.  2x is the shipped default: it is the smallest margin
# that covers ordinary preprocessing shrinkage without dragging the whole
# corpus in.  Raise it with --shrink-margin if a lever's witness sits outside.
DEFAULT_SHRINK_MARGIN = 2.0

# The giant raw-BVE band is the one gate read against PARSED counts
# (variant.rs:1114-1121), which the header equals except when a file's `p cnf`
# line disagrees with its content -- the parser uses the content-driven
# max-variable count (variant.rs:147-152). That is a small, bounded discrepancy,
# not preprocessing shrinkage, so it gets its own much tighter margin. Using
# DEFAULT_SHRINK_MARGIN here would nearly double the population (29 -> 51) to
# insure against an error the gate cannot make.
DEFAULT_BAND_EDGE_MARGIN = 1.10


def read_header(path):
    """Return (vars, clauses) from the DIMACS `p cnf` line. Header-only read."""
    with open(path, "rb") as fh:
        for _ in range(1024):
            line = fh.readline()
            if not line:
                return None, None
            s = line.strip()
            if not s or s[:1] in (b"c", b"%"):
                continue
            if s[:1] == b"p":
                parts = s.split()
                if len(parts) >= 4:
                    try:
                        return int(parts[2]), int(parts[3])
                    except ValueError:
                        return None, None
            return None, None
    return None, None


BINARY_CLAUSE_RE = r"^[[:space:]]*-?[0-9]+[[:space:]]+-?[0-9]+[[:space:]]+0[[:space:]]*$"


def count_binary(path):
    """Count 2-literal clauses. FULL-FILE read -- only for the L3 route band.

    ADVISORY ONLY.  It assumes one clause per line, which this corpus honours
    but DIMACS does not require; a file that wraps clauses across lines would
    undercount.  Because a wrong count could only ever remove an instance from
    the population -- the under-approximating direction this whole script
    exists to avoid -- the result never shrinks `core`. See lever_bve_giant.
    """
    try:
        proc = subprocess.run(["grep", "-cE", BINARY_CLAUSE_RE, path],
                              capture_output=True,
                              env=dict(os.environ, LC_ALL="C"))
        # grep exits 1 on "no match", which is a legitimate zero.
        if proc.returncode in (0, 1):
            return int((proc.stdout or b"0").strip() or 0)
    except (OSError, ValueError):
        pass
    n_bin = 0
    with open(path, "rb") as fh:
        for line in fh:
            s = line.strip()
            if not s or s[:1] in (b"c", b"p", b"%"):
                continue
            if len(s.split()) == 3:
                n_bin += 1
    return n_bin


def density(v, c):
    return (c / v) if v else 0.0


# ---------------------------------------------------------------------------
# LEVER 1 -- --sat-vivify-converge  (05d1b59745)
# ---------------------------------------------------------------------------
def lever_vivify(rows, margin):
    """Preprocessing-vivification convergence.

    REACHABILITY, in the order the binary evaluates it:

      crates/ay-sat/src/solver/config_preprocess.rs:886-892
          !dense_factor_bve_lrat_route
          && !circuit_bve_lrat_preprocess_route_active()
          && formula_class == FormulaClass::Small
          && inproc_ctrl.vivify.enabled
          && (!skip_expensive_preprocessing_passes || vivify_density_exempt)

      config_preprocess.rs:884-885
          vivify_density_exempt = skip_expensive_preprocessing_passes
                                  && vivify_converge_enabled()

    The arm changes behaviour along TWO independent paths, and the second is
    wider than the commit message's headline:

      (a) DENSITY EXEMPTION.  When the shared density gate
          (config_preprocess_policy.rs:568-570, whose dense arm is
          skip_dense_formula_elim_raised at :730-737) is tripped, base skips
          preprocessing vivification entirely and the arm runs it.  This is the
          `stable-400` witness (400 vars / 30,623 clauses, density 76.6).

      (b) BUDGET.  vivify/mod.rs:389-404 -- base gets
          (VIVIFY_MIN_EFFORT * PREPROCESS_VIVIFY_MAX_ROUNDS) = 4M ticks,
          4 rounds and NO dedicated deadline (it inherits the shared ~2 s
          preprocessing budget); the arm gets
          irredundant_literals * VIVIFY_CONVERGE_TICKS_PER_LITERAL(64)
          clamped to [4M, VIVIFY_CONVERGE_MAX_TICKS(200M)],
          VIVIFY_CONVERGE_MAX_ROUNDS(64) rounds and a dedicated
          VIVIFY_CONVERGE_WALL_SECS(30) deadline.
          (constants.rs:676 / :682 / :687 / :693.)
          This fires on EVERY Small formula that reaches vivify_preprocess,
          density-gated or not.

    So eligibility is `FormulaClass::Small`, and the density-tripped set is a
    reported SUB-population, not the whole thing.  Scoping the run to the
    density-tripped 17 would have measured only path (a).
    """
    core, wide, dense_sub = [], [], []
    for h, r in rows.items():
        v, c = r["vars"], r["clauses"]
        small = (v < FORMULA_CLASS_SMALL_MAX_VARS
                 and c < FORMULA_CLASS_SMALL_MAX_CLAUSES)
        near = (v < FORMULA_CLASS_SMALL_MAX_VARS * margin
                and c < FORMULA_CLASS_SMALL_MAX_CLAUSES * margin)
        if small:
            core.append(h)
            # skip_expensive_preprocessing_passes for a Small formula can only
            # be reached through the density arm: its var/clause arms
            # (config_preprocess_policy.rs:568-569) need > 200K vars or > 3M
            # clauses, which Small excludes by construction. So the dense
            # sub-population is exactly `density > BVE_HIGH_DENSITY_SKIP`.
            if density(v, c) > BVE_HIGH_DENSITY_SKIP:
                dense_sub.append(h)
        elif near:
            wide.append(h)
    return {
        "lever": "vivify-converge",
        "flag": "--sat-vivify-converge true",
        "commit": "05d1b59745",
        "gate_citations": [
            "crates/ay-sat/src/solver/config_preprocess.rs:884-892 (class + density exemption)",
            "crates/ay-sat/src/solver/constants.rs:1890-1898 (FormulaClass::classify)",
            "crates/ay-sat/src/solver/constants.rs:1401,1415 (PREPROCESS_EXPENSIVE_MAX_VARS/CLAUSES)",
            "crates/ay-sat/src/solver/config_preprocess_policy.rs:568-570 (skip_expensive_preprocessing_passes)",
            "crates/ay-sat/src/solver/config_preprocess_policy.rs:730-737 (skip_dense_formula_elim_raised)",
            "crates/ay-sat/src/solver/constants.rs:1078,1089 (density thresholds 20.0 / 50.0)",
            "crates/ay-sat/src/solver/inprocessing/vivify/mod.rs:389-404 (preprocess_vivify_budget)",
            "crates/ay-sat/src/solver/constants.rs:676,682,687,693 (converge budget constants)",
            "crates/ay-sat/src/solver/inprocessing/vivify/mod.rs:443-447 (default OFF)",
        ],
        "gate_arithmetic":
            "vars < 10_000 AND clauses < 100_000 (FormulaClass::Small); "
            "the density sub-population additionally has clauses/vars > 50.0",
        "core": core,
        "wide": wide,
        "sub_populations": {"density_gate_tripped": dense_sub},
        "over_approximations": [
            "classify() is fed `num_vars - count_fixed_vars()` and "
            "`arena.active_clause_count()` -- POST-parse, mid-preprocessing "
            "counts. The header is only a proxy. The `wide` tier adds every "
            f"instance within {margin:g}x of both thresholds, which is where a "
            "formula that shrinks into Small during preprocessing lives.",
            "`inproc_ctrl.vivify.enabled` is assumed true: config_preprocess.rs:57 "
            "clears it only under an explicit --sat-no-vivify, which no arm passes.",
            "The two LRAT route predicates in the same condition "
            "(dense_factor_bve_lrat_route, circuit_bve_lrat_preprocess_route_active) "
            "are assumed false because the run is a DRAT surface.",
        ],
    }


# ---------------------------------------------------------------------------
# LEVER 2 -- --sat-mode-equiticks-large  (8776347a35)
# ---------------------------------------------------------------------------
def lever_equiticks(rows, margin):
    """Equal-effort stable/focused tick split, restricted to the very-large band.

    REACHABILITY:

      crates/ay-sat/src/solver/solve/mod.rs:920
          let very_large =
              self.num_original_clauses > VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD;
      crates/ay-sat/src/solver/solve/mod.rs:923-924
          self.cold.mode_equiticks_large_band =
              very_large && switches.mode_equiticks_large.unwrap_or_default();
      crates/ay-sat/src/solver/constants.rs:491
          VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD = 1_000_000

    `num_original_clauses` is NOT the header count: solve/mod.rs:484 assigns
    `self.arena.irredundant_count()`, which is read AFTER preprocessing.  A
    header well above 1M can be under it by the time line 920 runs, and (more
    rarely, via factoring/BVE resolvents) a header under 1M can be over it.
    """
    core, wide = [], []
    for h, r in rows.items():
        c = r["clauses"]
        if c > VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD:
            core.append(h)
        elif c > VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD / margin:
            wide.append(h)
    return {
        "lever": "mode-equiticks-large",
        "flag": "--sat-mode-equiticks-large true",
        "commit": "8776347a35",
        "gate_citations": [
            "crates/ay-sat/src/solver/solve/mod.rs:920 (very_large predicate)",
            "crates/ay-sat/src/solver/solve/mod.rs:923-924 (arm resolution)",
            "crates/ay-sat/src/solver/constants.rs:491 (threshold = 1_000_000)",
            "crates/ay-sat/src/solver/solve/mod.rs:484 (num_original_clauses = arena.irredundant_count())",
        ],
        "gate_arithmetic": "post-preprocessing irredundant clauses > 1_000_000",
        "core": core,
        "wide": wide,
        "sub_populations": {},
        "over_approximations": [
            "The gate reads a POST-preprocessing irredundant count, not the "
            f"header. The `wide` tier adds headers above {int(VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD / margin):,} "
            "so an instance whose clause DB GROWS past 1M during preprocessing "
            "is not silently dropped. Instances whose header is above 1M but "
            "shrink below it stay in `core` and simply cost run time.",
        ],
    }


# ---------------------------------------------------------------------------
# LEVER 3 -- --sat-bve-giant-raw  (3ee1ae5497)
# ---------------------------------------------------------------------------
def lever_bve_giant(rows, margin, binfrac=None):
    """Giant raw-BVE route.

    REACHABILITY -- crates/ay-sat/src/variant.rs:1093-1122, in evaluation order:

      :1097  variant must be SolverVariant::Default
      :1100  input.proof_mode() == VariantProofMode::Lrat  ->  FALSE
             *** THIS IS WHY THE RUN MUST BE A DRAT SURFACE. Under LRAT the
             predicate returns false BEFORE any band check, so an LRAT A/B
             measures base against base and is guaranteed to report a null. ***
      :1104  the switch itself, default BVE_GIANT_RAW_ROUTE_DEFAULT=false (:593)
      :1114  input.num_vars()    <= BVE_SPARSE_MAX_VARS (150_000)      -> FALSE
      :1115  input.num_vars()    >  BVE_GIANT_RAW_MAX_VARS (2_000_000) -> FALSE
      :1116  input.num_clauses() >  BVE_GIANT_RAW_MAX_CLAUSES (10_000_000) -> FALSE
      :1120  density = clauses/vars <= BVE_SPARSE_MAX_DENSITY (12.0)

    These read the PARSED counts (variant.rs:147-152: "num_vars must be the
    content-driven max-variable count"), which the header normally equals, so
    this is the one lever whose band is decidable from headers.

    Two gates are NOT decidable from a header:
      * the route steal at :1097 -- an instance auto-routed Default->Probe
        (features.rs:99-125) or Default->Aggressive (features.rs:139-165) is
        no longer Default and the route is inert. Both bands need
        `num_binary`, so --scan-binary computes it; without it every in-band
        instance is kept.
      * `Solver::try_qualify_bve_giant_raw` completes qualification at
        preprocess time and requires the collapse to have substituted NOTHING
        plus a live dense-skip re-check. That is a runtime property with no
        static proxy at all -- always over-approximated.
    """
    core, wide, route_stolen = [], [], []
    for h, r in rows.items():
        v, c = r["vars"], r["clauses"]
        d = density(v, c)
        in_band = (v > BVE_SPARSE_MAX_VARS and v <= BVE_GIANT_RAW_MAX_VARS
                   and c <= BVE_GIANT_RAW_MAX_CLAUSES and d <= BVE_SPARSE_MAX_DENSITY)
        near = (v > BVE_SPARSE_MAX_VARS / margin
                and v <= BVE_GIANT_RAW_MAX_VARS * margin
                and c <= BVE_GIANT_RAW_MAX_CLAUSES * margin
                and d <= BVE_SPARSE_MAX_DENSITY * margin)
        if not (in_band or near):
            continue
        # ADVISORY dilution estimate: an instance the auto-router steals from
        # Default can never arm the route, so its two arms are identical. It is
        # REPORTED, never REMOVED -- count_binary's one-clause-per-line
        # assumption is not guaranteed, and acting on it would be the
        # under-approximation this script refuses to make.
        if binfrac is not None and h in binfrac:
            fb = binfrac[h]
            probe = (fb >= AUTO_ROUTE_MIN_BINARY_FRACTION
                     and d <= PROBE_MAX_CLAUSE_VAR_RATIO
                     and PROBE_MIN_VARS <= v <= PROBE_MAX_VARS)
            aggressive = (fb >= AUTO_ROUTE_MIN_BINARY_FRACTION
                          and d > PROBE_MAX_CLAUSE_VAR_RATIO
                          and d <= AGGRESSIVE_MAX_CLAUSE_VAR_RATIO
                          and AGGRESSIVE_MIN_VARS <= v <= AGGRESSIVE_MAX_VARS)
            if probe or aggressive:
                route_stolen.append(h)
        if in_band:
            core.append(h)
        else:
            wide.append(h)
    return {
        "lever": "bve-giant-raw",
        "flag": "--sat-bve-giant-raw true",
        "commit": "3ee1ae5497",
        "requires_drat": True,
        "gate_citations": [
            "crates/ay-sat/src/variant.rs:1093-1122 (bve_giant_raw_route_active)",
            "crates/ay-sat/src/variant.rs:1097 (SolverVariant::Default only)",
            "crates/ay-sat/src/variant.rs:1100-1102 (LRAT -> false, before any band check)",
            "crates/ay-sat/src/variant.rs:593 (BVE_GIANT_RAW_ROUTE_DEFAULT = false)",
            "crates/ay-sat/src/variant.rs:517,561,588,499 (150K / 2M / 10M / 12.0)",
            "crates/ay-sat/src/features.rs:99-125,139-165 (Probe/Aggressive auto-route bands)",
        ],
        "gate_arithmetic":
            "150_000 < vars <= 2_000_000 AND clauses <= 10_000_000 "
            "AND clauses/vars <= 12.0, on a NON-LRAT proof surface",
        "core": core,
        "wide": wide,
        "sub_populations": {"auto_route_stolen_from_default": route_stolen},
        "over_approximations": [
            "`try_qualify_bve_giant_raw` (zero collapse substitution + a live "
            "dense-skip re-check) is a runtime property with no header proxy. "
            "Every in-band instance is kept; some will qualify at neither arm "
            "and produce an identical pair.",
            "The Default-variant requirement at variant.rs:1097 needs "
            "`num_binary`. Without --scan-binary no instance is excluded on "
            "that ground.",
            f"The `wide` tier relaxes each band edge by {margin:g}x to absorb "
            "header/parse disagreement (variant.rs:147-152 uses the "
            "content-driven max-variable count, so a `p cnf` line that "
            "overstates its var count could push a genuinely in-band instance "
            "out). This margin is deliberately much tighter than the one the "
            "other two levers use: this gate reads PARSED counts, not "
            "post-preprocessing ones, so there is no shrinkage to insure against.",
        ],
    }


def estimate_wall(hashes, ref_times, timeout, workers, arms=2, overhead=1.15):
    """Wall-clock estimate in seconds for a paired sweep over `hashes`."""
    total = 0.0
    unknown = 0
    for h in hashes:
        t = ref_times.get(h)
        if t is None:
            unknown += 1
            t = timeout
        total += min(t, timeout)
    return total * arms / max(1, workers) * overhead, unknown


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", default=os.path.expanduser("~/ay-bench/main2026-full/cnf"))
    ap.add_argument("--truth", default="benchmarks/sat/satcomp2026-main-truth.json")
    ap.add_argument("--reference-sweep",
                    default=os.path.expanduser("~/ay-bench/proofmode-full400-aug25-corrected.json"),
                    help="a prior sweep JSON, used ONLY to price the run")
    ap.add_argument("--timeout", type=float, default=300.0, help="SECONDS")
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--shrink-margin", type=float, default=DEFAULT_SHRINK_MARGIN,
                    help="over-approximation multiplier for the two gates read "
                         "against POST-preprocessing counts (levers 1 and 2)")
    ap.add_argument("--band-edge-margin", type=float, default=DEFAULT_BAND_EDGE_MARGIN,
                    help="over-approximation multiplier for the giant raw-BVE "
                         "band, which is read against PARSED counts (lever 3)")
    ap.add_argument("--tier", choices=("core", "core+wide"), default="core+wide",
                    help="which population the emitted .list files carry")
    ap.add_argument("--scan-binary", action="store_true",
                    help="FULL-FILE read of the giant-raw candidates to compute "
                         "the binary-clause fraction, which decides whether the "
                         "auto-router steals the instance from Default")
    ap.add_argument("--outdir", default=os.path.expanduser("~/ay-bench/lever-ab"))
    ap.add_argument("--json-out", help="also write the populations here (repo evidence)")
    args = ap.parse_args()

    cnfs = sorted(glob.glob(os.path.join(args.corpus, "*.cnf")))
    if not cnfs:
        print(f"no CNFs under {args.corpus}", file=sys.stderr)
        return 1
    rows = {}
    for p in cnfs:
        h = os.path.basename(p)[:-4]
        v, c = read_header(p)
        if v is None:
            print(f"WARNING: no `p cnf` header in {p}", file=sys.stderr)
            continue
        rows[h] = {"vars": v, "clauses": c, "path": p}

    truth = {}
    if os.path.exists(args.truth):
        truth = json.load(open(args.truth)).get("instances_by_hash", {})

    ref_times = {}
    if args.reference_sweep and os.path.exists(args.reference_sweep):
        ref = json.load(open(args.reference_sweep))
        ref_to = float(ref.get("timeout_s") or args.timeout)
        for r in ref["results"]:
            h = r["cnf"][:-4] if r["cnf"].endswith(".cnf") else r["cnf"]
            ref_times[h] = (r["time"] if r["verdict"] in ("sat", "unsat")
                            else max(ref_to, args.timeout))

    binfrac = None
    if args.scan_binary:
        cand = [h for h, r in rows.items()
                if r["vars"] > BVE_SPARSE_MAX_VARS / 2
                and r["vars"] <= BVE_GIANT_RAW_MAX_VARS * 2
                and density(r["vars"], r["clauses"]) <= AGGRESSIVE_MAX_CLAUSE_VAR_RATIO]
        binfrac = {}
        for h in sorted(cand):
            nb = count_binary(rows[h]["path"])
            binfrac[h] = nb / max(1, rows[h]["clauses"])
        print(f"scanned {len(binfrac)} candidate(s) for binary fraction", flush=True)

    margin = args.shrink_margin
    levers = [lever_vivify(rows, margin),
              lever_equiticks(rows, margin),
              lever_bve_giant(rows, args.band_edge_margin, binfrac)]

    os.makedirs(args.outdir, exist_ok=True)
    report = {"corpus": args.corpus, "n_corpus": len(rows),
              "timeout_s": args.timeout, "workers": args.workers,
              "shrink_margin": margin,
              "band_edge_margin": args.band_edge_margin, "tier": args.tier,
              "binary_fraction_scanned": binfrac is not None,
              "levers": []}

    total_wall = 0.0
    for L in levers:
        sel = L["core"] + (L["wide"] if args.tier == "core+wide" else [])
        sel = sorted(sel, key=lambda h: (rows[h]["vars"], h))
        listp = os.path.join(args.outdir, f"lever-{L['lever']}.list")
        with open(listp, "w") as fh:
            for h in sel:
                fh.write(rows[h]["path"] + "\n")
        wall, unknown = estimate_wall(sel, ref_times, args.timeout, args.workers)
        total_wall += wall
        L["list_path"] = listp
        L["n_core"] = len(L["core"])
        L["n_wide"] = len(L["wide"])
        L["n_selected"] = len(sel)
        L["estimated_wall_s"] = round(wall, 1)
        L["estimated_wall_h"] = round(wall / 3600.0, 2)
        L["priced_at_timeout_rows"] = unknown
        L["instances"] = [
            {"hash": h, "name": truth.get(h, {}).get("name", "?"),
             "truth": truth.get(h, {}).get("truth", "?"),
             "field_solved": truth.get(h, {}).get("n_solved"),
             "vars": rows[h]["vars"], "clauses": rows[h]["clauses"],
             "density": round(density(rows[h]["vars"], rows[h]["clauses"]), 3),
             "tier": "core" if h in set(L["core"]) else "wide",
             "ref_time_s": ref_times.get(h)}
            for h in sel]
        # Detail the sub-populations by name so a reader can see the witness.
        L["sub_population_names"] = {
            k: [truth.get(h, {}).get("name", h) for h in v]
            for k, v in L["sub_populations"].items()}
        report["levers"].append(L)

        sat = sum(1 for i in L["instances"] if i["truth"] == "sat")
        uns = sum(1 for i in L["instances"] if i["truth"] == "unsat")
        unk = len(sel) - sat - uns
        print(f"\n=== {L['lever']}  ({L['flag']}) ===")
        print(f"  gate: {L['gate_arithmetic']}")
        print(f"  eligible: core={L['n_core']}  wide(+over-approx)={L['n_wide']}"
              f"  -> selected {L['n_selected']}/{len(rows)}")
        print(f"  ground truth of the selection: sat={sat} unsat={uns} unknown={unk}")
        for k, v in L["sub_populations"].items():
            print(f"  sub-population {k}: {len(v)}")
        print(f"  list: {listp}")
        print(f"  ESTIMATED PAIRED WALL at {args.timeout:g}s x {args.workers} workers:"
              f" {wall/3600.0:.2f} h  ({unknown} row(s) priced at the full timeout)")
        if L["n_selected"] == 0:
            print("  *** EMPTY POPULATION -- this lever cannot fire on ANY corpus "
                  "instance. Do not ship it on a witness alone. ***")
        elif L["n_selected"] < 5:
            print(f"  *** TINY POPULATION ({L['n_selected']}) -- a lever that can "
                  "fire on ~no corpus instance is not worth shipping whatever its "
                  "witness showed. ***")

    report["estimated_total_wall_h"] = round(total_wall / 3600.0, 2)
    print(f"\nTOTAL ESTIMATED WALL for all three paired A/Bs: "
          f"{total_wall/3600.0:.2f} h at {args.timeout:g}s x {args.workers} workers")

    outp = os.path.join(args.outdir, "lever-populations.json")
    with open(outp, "w") as fh:
        json.dump(report, fh, indent=2)
    print(f"wrote {outp}")
    if args.json_out:
        os.makedirs(os.path.dirname(args.json_out) or ".", exist_ok=True)
        with open(args.json_out, "w") as fh:
            json.dump(report, fh, indent=2)
        print(f"wrote {args.json_out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
