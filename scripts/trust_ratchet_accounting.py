#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Tell a PROVED obligation apart from one that merely STOPPED BEING ASKED.

WHY THIS FILE EXISTS. It exists because the ratchet was fooled, once, in a way
that is fully documented and fully reproducible.

On 2026-08-21 three audited std call summaries landed (ay commit 5c7bf3a05d,
against trust 3011097ff). The measured movement was:

    obligations 126 -> 105     unknown 43 -> 22     unsupported 66 -> 44
    proved       35 ->  35     failed  27 -> 27     solver-discharged 12 -> 12

FOUR metrics improved and NOT ONE obligation was proved. Modelling a callee as
total does not DISCHARGE its panic-freedom obligation -- it stops the obligation
being EMITTED. The numerator stood still; the denominator fell out from under
it. To a ratchet that compares scalar counts and treats "unknown went down" as
progress, that is indistinguishable from real work, and it printed as a pass.

THE STRUCTURAL FIX IS NOT A BETTER THRESHOLD, IT IS A DIFFERENT KIND OF
MEASUREMENT. A count cannot separate the two cases; a SET can:

  * an obligation that was PROVED keeps its identity and changes class;
  * an obligation that STOPPED BEING ASKED has an identity that is simply gone.

So the baseline records identities (schema v3 `obligation_ledger`) and this file
differences them. Everything it credits as forward motion is a named obligation
that a solver or the kernel discharged. Everything else is disclosed by name and
credited to nothing.

THE THREE RULES THIS ENCODES

  1. ONLY A PROVER EARNS CREDIT. `proved_solver_discharged` and
     `kernel_certified` are the floors, and they are floors precisely because
     deleting an obligation cannot raise them. `verdicts.proved` is NOT a floor:
     it includes `no_obligations` structural verdicts, and those DO rise when
     obligations stop being emitted -- measured 2026-08-26, `proved` moved
     35 -> 42 on this crate while `proved_solver_discharged` sat at 12, the
     entire +7 being structural. A headline that can move without a prover is a
     headline that can be gamed.

  2. A GAP METRIC FALLING IS NOT EVIDENCE. `failed`, `unknown`,
     `summary.unproved_obligations` and friends fall for two reasons that look
     identical in a count: something got proved, or something stopped being
     asked. They are therefore reported with their cause attached and are never
     credited on their own. A gap metric RISING is still a regression -- that
     asymmetry is deliberate, and rises are excused only to the exact extent
     that newly-emitted obligations account for them.

  3. DENOMINATOR SHRINKAGE IS STATED, NOT INFERRED. `obligations_removed_*` is
     printed on every run, in the headline, next to the proof count. A shrinking
     denominator is a legitimate thing to do -- 21 obligations that could never
     be discharged are better gone than pending -- but it is bought with TRUST,
     not proof, and it must never again be reported in the same breath as a
     proof.

ATTRIBUTION. A removed obligation is charged to `obligations_removed_by_summary`
when it carried an absent-callee assumption for a callee that is no longer
charged anywhere in the crate. That is the exact fingerprint of a callee
acquiring an audited totality summary. Removals we cannot attribute that way are
reported separately as `obligations_removed_unattributed` rather than being
folded in -- an unattributed removal is still denominator shrinkage, and
guessing its cause would be the same species of error as projecting a result.

USAGE
    trust_ratchet_accounting.py BASE.json CUR.json              # compare, exit 1 on regress
    trust_ratchet_accounting.py BASE.json CUR.json --record OUT # write OUT with accounting
"""

from __future__ import annotations

import argparse
import collections
import json
import sys
from pathlib import Path

# Obligation classes, in the ledger's vocabulary. `proved_solver` is the only one
# that means a prover discharged a goal.
PROVED_SOLVER = "proved_solver"
PROVED_STRUCTURAL = "proved_structural"


def _ledger(doc: dict) -> dict[str, dict]:
    return (doc.get("obligation_ledger") or {}).get("entries") or {}


def _v(doc: dict, key: str, default: int = 0) -> int:
    return (doc.get("verdicts") or {}).get(key, default)


def _proved_multiset(doc: dict) -> collections.Counter:
    """Degraded-mode proof identity for a pre-v3 baseline: (function, kind).

    A v2 baseline has no ledger, but it DOES carry `proved_obligations` -- the
    itemized solver-discharged proofs with function/kind/location. That is enough
    to answer the one question that must never be answered by a count: did an
    obligation that WAS proved stop being proved.

    The LOCATION is deliberately dropped. v2 recorded `file:line`, and a line
    number moves whenever code is inserted above it: measured 2026-08-26, five
    untouched obligations in `literal.rs` shifted by 49 lines and a
    location-keyed comparison called all five a lost proof AND called their new
    positions five fresh proofs -- both halves fabricated by the same edit. A
    (function, kind) multiset is coarser, and coarse in the safe direction: it
    cannot invent a loss, and the only loss it can miss is one masked by a
    same-function same-kind gain, which the counts would then contradict.
    """
    return collections.Counter(
        (r.get("function"), r.get("kind")) for r in doc.get("proved_obligations") or []
    )


def accounting(base: dict, cur: dict) -> dict:
    """The whole comparison. Pure function of two baseline documents."""
    base_led, cur_led = _ledger(base), _ledger(cur)
    identity_mode = bool(base_led) and bool(cur_led)

    before, after = _v(base, "obligations"), _v(cur, "obligations")

    proved_gained: list[str] = []
    proof_lost: list[str] = []
    removed_by_class: collections.Counter = collections.Counter()
    added_by_class: collections.Counter = collections.Counter()
    removed_by_summary: list[str] = []
    removed_unattributed: list[str] = []

    if identity_mode:
        # Callees still charged an absent-callee assumption somewhere in the
        # current run. A removed obligation whose callee has left this set is
        # attributable to that callee becoming modeled.
        still_charged = {
            e["absent_callee"] for e in cur_led.values() if e.get("absent_callee")
        }
        for key, entry in sorted(cur_led.items()):
            was = base_led.get(key)
            if was is None:
                added_by_class[entry["class"]] += 1
            elif entry["class"] == PROVED_SOLVER and was["class"] != PROVED_SOLVER:
                proved_gained.append(key)
        for key, entry in sorted(base_led.items()):
            now = cur_led.get(key)
            if now is None:
                removed_by_class[entry["class"]] += 1
                callee = entry.get("absent_callee")
                if callee and callee not in still_charged:
                    removed_by_summary.append("%s  <- %s" % (key, callee))
                else:
                    removed_unattributed.append(key)
                if entry["class"] == PROVED_SOLVER:
                    proof_lost.append(key + "  (REMOVED while proved)")
            elif entry["class"] == PROVED_SOLVER and now["class"] != PROVED_SOLVER:
                proof_lost.append("%s  (%s -> %s)" % (key, entry["class"], now["class"]))
    else:
        # Degraded: enforce no-proof-lost from the v2 `proved_obligations` list,
        # and report the denominator delta WITHOUT attributing it -- a pre-v3
        # baseline recorded no identities for the obligations it did not prove,
        # so there is nothing to difference and guessing would be a projection.
        base_ms = _proved_multiset(base)
        cur_ms = (
            collections.Counter(
                (k.split("|")[0], k.split("|")[1])
                for k, e in cur_led.items()
                if e["class"] == PROVED_SOLVER
            )
            if cur_led
            else _proved_multiset(cur)
        )
        for (fn, kind), n in sorted((base_ms - cur_ms).items()):
            proof_lost.extend(
                ["%s|%s  (was solver-discharged in the baseline)" % (fn, kind)] * n
            )
        for (fn, kind), n in sorted((cur_ms - base_ms).items()):
            proved_gained.extend(["%s|%s" % (fn, kind)] * n)
        if after < before:
            removed_unattributed = [
                "<%d obligations, identities not recorded by the pre-v3 baseline>"
                % (before - after)
            ]

    removed = sum(removed_by_class.values()) if identity_mode else max(0, before - after)
    added = sum(added_by_class.values()) if identity_mode else max(0, after - before)

    one_line = (
        "PROVED %d obligation(s) this run; %d obligation(s) merely STOPPED BEING ASKED "
        "(%d attributed to a callee summary, %d unattributed); denominator %d -> %d."
        % (
            len(proved_gained),
            removed,
            len(removed_by_summary),
            len(removed_unattributed) if identity_mode else removed,
            before,
            after,
        )
    )

    def delta(key: str) -> dict:
        b, c = _v(base, key), _v(cur, key)
        return {"before": b, "after": c, "delta": c - b}

    return {
        "mode": "identity (schema v3 ledger on both sides)"
        if identity_mode
        else "DEGRADED -- the baseline predates the obligation ledger. Removals "
        "cannot be attributed at all, and proof-loss is checked on a (function, "
        "kind) multiset rather than per obligation",
        "one_line": one_line,
        "floors_only_a_prover_can_raise": {
            "proved_solver_discharged": delta("proved_solver_discharged"),
            "kernel_certified": delta("kernel_certified"),
        },
        "disclosed_never_credited": {
            "_why": "each of these can move without a prover: `proved` and "
            "`functions_fully_verified` rise when obligations stop being emitted "
            "(structural `no_obligations` verdicts), and every gap counter falls "
            "for proof and for deletion alike.",
            "obligations": delta("obligations"),
            "proved_including_structural": delta("proved"),
            "proved_structural_no_obligations": delta("proved_structural_no_obligations"),
            "functions_fully_verified": delta("functions_fully_verified"),
            "failed": delta("failed"),
            "unknown": delta("unknown"),
            "runtime_checked": delta("runtime_checked"),
            "timed_out": delta("timed_out"),
        },
        "movement": {
            "obligations_proved": len(proved_gained),
            "obligations_proved_detail": proved_gained,
            "obligations_proof_lost": len(proof_lost),
            "obligations_proof_lost_detail": proof_lost,
            "obligations_removed_total": removed,
            "obligations_removed_by_summary": len(removed_by_summary),
            "obligations_removed_by_summary_detail": removed_by_summary,
            "obligations_removed_unattributed": len(removed_unattributed)
            if identity_mode
            else removed,
            "obligations_removed_unattributed_detail": removed_unattributed,
            "obligations_removed_by_previous_class": dict(sorted(removed_by_class.items())),
            "obligations_newly_asked": added,
            "obligations_newly_asked_by_class": dict(sorted(added_by_class.items())),
        },
    }


def regressions(acct: dict, base: dict, cur: dict) -> list[str]:
    """The fail conditions. Every one is a lost proof or an unexplained new gap."""
    out: list[str] = []
    mv = acct["movement"]
    if mv["obligations_proof_lost"]:
        out.append(
            "%d obligation(s) that a solver had DISCHARGED are no longer proved:\n      %s"
            % (
                mv["obligations_proof_lost"],
                "\n      ".join(mv["obligations_proof_lost_detail"][:10]),
            )
        )
    for name, d in acct["floors_only_a_prover_can_raise"].items():
        if d["delta"] < 0:
            out.append("%s FELL %d -> %d (proof floor)" % (name, d["before"], d["after"]))
    dt = acct["disclosed_never_credited"]["timed_out"]
    if dt["delta"] > 0:
        out.append("timed_out ROSE %d -> %d" % (dt["before"], dt["after"]))
    # A gap RISING is a regression; it is excused only to the extent that newly
    # emitted obligations account for it. (A fall is never credited -- rule 2.)
    newly = mv["obligations_newly_asked_by_class"]
    identity = acct["mode"].startswith("identity")
    for cls in ("failed", "unknown"):
        d = acct["disclosed_never_credited"][cls]
        if d["delta"] <= 0:
            continue
        explained = newly.get(cls, 0) if identity else 0
        # `skipped` is a SUBSET of the rollup's `unknown`, and the two transports
        # disagree about the name. The crate_summary partitions obligations as
        # proved + failed + unknown + runtime_checked = total, and reports
        # `total_skipped` as a separate view of obligations already inside
        # `total_unknown`. The per-obligation ledger instead records the raw
        # outcome string, so the same obligation is classed `skipped` there.
        #
        # MEASURED 2026-08-26, the run that exposed this: the crate went to 63
        # proved / 17 failed / 9 unknown / 21 runtime-checked / 110 total --
        # which sums to exactly 110 -- with `total_skipped: 4`, while the ledger
        # read 5 unknown + 4 skipped. Both transports agree; only the label
        # differs. Without this line, the FIRST contract ever added to a crate is
        # reported as an unexplained `unknown` regression, because every
        # `assumption:requires` obligation lands in a class the excuse lookup
        # cannot see. Those obligations ARE newly emitted, which is precisely the
        # excuse this rule already grants -- so this is a naming fix, not a
        # loosening. Nothing here credits anything: `skipped` earns no proof, and
        # the floors above (`proved_solver_discharged`, `kernel_certified`) are
        # untouched and remain the only things a prover can raise.
        if cls == "unknown" and identity:
            explained += newly.get("skipped", 0)
        if d["delta"] > explained:
            out.append(
                "%s ROSE %d -> %d, and only %d of the +%d is explained by newly-emitted "
                "obligations" % (cls, d["before"], d["after"], explained, d["delta"])
            )
    return out


def report(acct: dict, cur: dict, regs: list[str]) -> None:
    v = cur.get("verdicts") or {}
    print(
        "trust-ratchet: %d of %d obligations SOLVER-DISCHARGED (%d kernel-certified). "
        "The crate also counts %d proved of which %d are structural `no_obligations` "
        "-- a verdict no prover produced."
        % (
            v.get("proved_solver_discharged", 0),
            v.get("obligations", 0),
            v.get("kernel_certified", 0),
            v.get("proved", 0),
            v.get("proved_structural_no_obligations", 0),
        )
    )
    # THE one line the lane asks for: proved versus merely-not-asked, together.
    print("trust-ratchet: " + acct["one_line"])
    if not acct["mode"].startswith("identity"):
        print("  NOTE  accounting mode: %s" % acct["mode"])

    mv = acct["movement"]
    for key in mv["obligations_proved_detail"][:10]:
        print("  PROVED           %s" % key)
    for key in mv["obligations_removed_by_summary_detail"][:10]:
        print("  NO-LONGER-ASKED  %s" % key)
    for key in mv["obligations_removed_unattributed_detail"][:10]:
        print("  NO-LONGER-ASKED  %s  (cause unattributed)" % key)
    if mv["obligations_newly_asked"]:
        by_class = mv["obligations_newly_asked_by_class"]
        print(
            "  NEWLY-ASKED      %d obligation(s)%s"
            % (
                mv["obligations_newly_asked"],
                (": %s" % by_class) if by_class else " (classes not attributable)",
            )
        )

    for name, d in acct["floors_only_a_prover_can_raise"].items():
        if d["delta"]:
            print(
                "  %-9s %-34s %d -> %d"
                % ("PROOF+" if d["delta"] > 0 else "PROOF-", name, d["before"], d["after"])
            )
    for name, d in acct["disclosed_never_credited"].items():
        if name.startswith("_") or not d["delta"]:
            continue
        print(
            "  %-9s %-34s %d -> %d"
            % ("DISCLOSED", name, d["before"], d["after"])
        )
    for r in regs:
        print("  REGRESSED  %s" % r)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("baseline", type=Path)
    ap.add_argument("current", type=Path)
    ap.add_argument(
        "--record",
        type=Path,
        help="write CURRENT (with the accounting embedded) here as the new baseline",
    )
    args = ap.parse_args()

    base = json.loads(args.baseline.read_text()) if args.baseline.exists() else {}
    cur = json.loads(args.current.read_text())

    acct = accounting(base, cur)
    regs = regressions(acct, base, cur)

    if args.record:
        # A baseline carries the movement that produced it. That is what makes a
        # shrinking denominator permanently visible: every re-record states, in
        # the file, how many obligations it proved and how many it stopped
        # asking. Nobody has to reconstruct it from two commits later.
        cur["ratchet_accounting"] = {
            "_purpose": "how THIS baseline moved from the one it replaced. Recorded "
            "so a denominator that shrank is legible forever, not just on the day.",
            "previous_baseline_schema": base.get("schema_version"),
            "previous_toolchain": (base.get("metadata") or {}).get("toolchain"),
            **acct,
            "regressions_at_record_time": regs,
        }
        args.record.write_text(json.dumps(cur, indent=2, sort_keys=False) + "\n")
        report(acct, cur, regs)
        print("\ntrust-ratchet: baseline re-recorded at %s" % args.record)
        if regs:
            # Recording over a regression is allowed (that is what --record is
            # for) but it is never silent, and the new baseline carries the list.
            print(
                "trust-ratchet: WARNING -- this re-record accepted %d regression(s); "
                "they are stored in `ratchet_accounting.regressions_at_record_time`."
                % len(regs)
            )
        return 0

    report(acct, cur, regs)
    if regs:
        print(
            "\ntrust-ratchet: FAIL -- proof coverage went backwards against %s"
            % args.baseline
        )
        return 1
    if acct["movement"]["obligations_proved"] or any(
        d["delta"] > 0 for d in acct["floors_only_a_prover_can_raise"].values()
    ):
        print(
            "\ntrust-ratchet: PASS -- the ratchet moved forward BY PROOF. Re-record so "
            "the gain is permanent:\n"
            "    bash scripts/ci/trust_verification_ratchet_gate.sh --record"
        )
        return 0
    if acct["movement"]["obligations_removed_total"]:
        print(
            "\ntrust-ratchet: PASS -- but NOTHING WAS PROVED. %d obligation(s) stopped "
            "being asked and 0 were discharged. That is a smaller denominator bought "
            "with trust, not a larger proof; re-record it only if the removal is "
            "intended and audited."
            % acct["movement"]["obligations_removed_total"]
        )
        return 0
    print("\ntrust-ratchet: PASS (no change against baseline)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
