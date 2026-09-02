#!/usr/bin/env python3
"""Adversarial mutation battery for the census's own VERIFIED certificates.

A census that reports "N instances VERIFIED" is worth nothing unless a WRONG
proof would have been caught. This script takes certificates the census scored
VERIFIED, damages each one in ways that break the bound it claims, and requires
the PINNED checker to REJECT every damaged copy.

CONTRACT
--------
Every mutation is declared with the verdict it MUST get:

  must-reject   the mutation makes the proof claim something the formula does
                not entail, or breaks the derivation that licenses the claim.
                An ACCEPT here is a checker defect and a stop-the-line event.
  may-accept    the mutation produces a DIFFERENT BUT STILL LEGAL proof, so a
                correct checker accepts it. Recorded, never counted as a
                catch. This class exists because a previous battery in this
                repo filed three `2 d` -> `3 d` mutations as suspicious before
                working out that VeriPB rounds coefficients up as well as the
                degree, so every divisor >= the original yields an identical or
                weaker row. A battery that cannot tell "the checker missed one"
                from "I wrote a bad mutation" is not evidence.

WHAT WENT INTO `may-accept`, AND WHY. All four families below were written as
must-reject first, MEASURED as accepted, and only then re-derived. Each is a bad
mutation, not a checker defect, and the discriminator is the same every time:
THE CHECKER STILL PRINTS THE TRUE OPTIMUM. A wrong-verdict defect prints a bound
that is not the instance's optimum; these print exactly the bound the unmutated
proof does. Every one of them has a must-reject TWIN in the battery that isolates
the property the original mutation was reaching for.

  pol-operand-repointed (to an id that EXISTS)
      `pol` is a CHECKED rule: the checker recomputes the row from the operands
      it is given, so aiming a summand at a different legal row derives a
      different but still SOUND row. Nothing downstream depends on the old one,
      because the lower bound is closed by a `rup` the checker re-derives by
      propagation over the whole database. TWIN: `pol-operand-nonexistent`,
      which names an id that was never derived. Rejected.
  pol-saturation-dropped
      saturation only weakens a row (it lowers coefficients to the degree), so
      removing it leaves a legal row with STRONGER coefficients. Sound.
      TWIN: `pol-degree-raised`, which raises the degree instead. Rejected.
  pol-divisor-halved
      cutting-planes division is sound for EVERY positive divisor, rounding up
      both coefficients and degree; 8192 -> 4096 is another legal division, not
      an unlicensed rounding. (The battery originally expected a smaller divisor
      to be a stronger round-up. It is not.)
      TWIN: `pol-divisor-zeroed`, which is not a division at all. Rejected.
  rup-degree-raised ON AN EMPTY ROW
      `rup >= 1 ;` carries no literals: it is the contradiction `0 >= 1`.
      Raising it to `0 >= 2` is a DIFFERENT contradiction, and every assignment
      falsifies both, so it is RUP-derivable exactly when the original is.
      TWIN: `rup-nonimplied`, which asks for a row that does NOT follow by
      propagation. Rejected.
  conclusion-lb-hint-nonexistent
      an out-of-range hint is IGNORED, not trusted -- the checker falls back to
      establishing the bound from the database itself and still prints the true
      optimum. TWINS, both must-reject and both rejected on every proof in the
      battery: the same bogus hint WITH the last derived row deleted, and the
      same bogus hint WITH the lower bound inflated by 1. Together those two
      show the fallback is a real check, not a bypass.

A FIFTH ENTRY BELONGS HERE AS A WARNING RATHER THAN A CLASS. The
contradiction-deletion mutation was first keyed on `rup` lines. Four of the
corpus proofs close their bound with `pol` alone and carry no `rup` at all, so
on those the mutation silently degenerated into the benign bogus-hint mutation
and was reported as four ACCEPTED must-rejects -- a battery scoring its own
no-op as a checker defect. It now deletes the LAST DERIVED ROW whatever rule
produced it, and is not emitted at all when there is no derived row to remove.
A mutation that does not fire is not a catch, and must not be able to look like
one in either direction.

Usage:
  pb_cert_census_mutate.py <veripb> <out.json> <opb> <pbp> [<opb> <pbp> ...]
"""

import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import OrderedDict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

_BOUND = re.compile(r'BOUNDS\s+(-?\d+)\s*<=\s*obj\s*<=\s*(-?\d+)')
_LIT = re.compile(r'(~?)x(\d+)')


def _bound_from_verdict(verdict):
    """The single optimum a `s VERIFIED BOUNDS v <= obj <= v` line asserts."""
    m = _BOUND.search(verdict or "")
    if not m or m.group(1) != m.group(2):
        return None
    return int(m.group(1))


def _check_witness(opb, pbp):
    """(feasible, objective) for the model on the proof's `conclusion` line.

    Uses the census's own independent OPB parser -- deliberately NOT the
    crate's -- so this adjudication cannot inherit a misreading of the formula
    from the thing it is adjudicating.
    """
    try:
        from construct_below_floor import parse_opb
        objective, constraints, _ = parse_opb(opb)
        tail = ""
        with open(pbp, errors="replace") as fh:
            for line in fh:
                if line.startswith("conclusion BOUNDS"):
                    tail = line.rpartition(":")[2]
                    break
        if not tail:
            return (False, None)
        assign = {int(v): (neg != '~') for neg, v in _LIT.findall(tail)}

        def lhs(terms):
            return sum(c * ((0 if assign.get(v, False) else 1) if neg
                            else (1 if assign.get(v, False) else 0))
                       for c, v, neg in terms)

        for terms, op, rhs in constraints:
            got = lhs(terms)
            if (op == '>=' and got < rhs) or (op == '=' and got != rhs):
                return (False, lhs(objective))
        return (True, lhs(objective))
    except Exception:                                        # noqa: BLE001
        return (False, None)


def run_checker(veripb, opb, pbp):
    """(exit_code, verdict_line). Verdict is taken from STDOUT alone."""
    try:
        p = subprocess.run([veripb, "--opb", opb, pbp],
                           capture_output=True, text=True, timeout=900)
    except subprocess.TimeoutExpired:
        return (-1, "<checker timed out>")
    verdict = ""
    for line in p.stdout.splitlines():
        if line.startswith("s "):
            verdict = line.rstrip()
            break
    return (p.returncode, verdict)


def accepted(code, verdict):
    """The shell library's contract, in Python: exit 0 AND a real conclusion.

    `s VERIFIED NO CONCLUSION` is NOT an acceptance, and neither is a bare
    `s VERIFIED`; `s UNDER WEAKENED GUARANTEES <x>` IS an acceptance for the
    purpose of scoring a mutation (a checker that accepts a broken proof under
    weakened guarantees has still accepted it).
    """
    if code != 0:
        return False
    for prefix in ("s VERIFIED", "s UNDER WEAKENED GUARANTEES"):
        if verdict == prefix or verdict == prefix + " NO CONCLUSION":
            return False
        if verdict.startswith(prefix + " "):
            return True
    return False


def flip_first_literal(text):
    m = re.search(r"(~?)(x\d+)", text)
    if not m:
        return None
    tilde, var = m.group(1), m.group(2)
    return text[:m.start()] + ("" if tilde else "~") + var + text[m.end():]


def mutants(lines):
    """Yield (name, expectation, mutated_lines). expectation in {reject, may}."""
    idx = {}
    for i, l in enumerate(lines):
        head = l.split()[0] if l.split() else ""
        idx.setdefault(head, []).append(i)

    def cp(mod):
        out = list(lines)
        mod(out)
        return out

    # --- the conclusion: the sentence the whole proof exists to license.
    for i in idx.get("conclusion", []):
        line = lines[i]
        m = re.match(r"conclusion BOUNDS (-?\d+) : (\S+) (-?\d+) :(.*)", line)
        if m:
            lb, hint, ub, wit = m.group(1), m.group(2), m.group(3), m.group(4)
            yield ("conclusion-lb+1", "reject", cp(lambda o, i=i, lb=lb, hint=hint, ub=ub, wit=wit:
                   o.__setitem__(i, f"conclusion BOUNDS {int(lb)+1} : {hint} {ub} :{wit}")))
            yield ("conclusion-lb+7", "reject", cp(lambda o, i=i, lb=lb, hint=hint, ub=ub, wit=wit:
                   o.__setitem__(i, f"conclusion BOUNDS {int(lb)+7} : {hint} {ub} :{wit}")))
            yield ("conclusion-ub-1", "reject", cp(lambda o, i=i, lb=lb, hint=hint, ub=ub, wit=wit:
                   o.__setitem__(i, f"conclusion BOUNDS {lb} : {hint} {int(ub)-1} :{wit}")))
            yield ("conclusion-both-shift+1", "reject", cp(lambda o, i=i, lb=lb, hint=hint, ub=ub, wit=wit:
                   o.__setitem__(i, f"conclusion BOUNDS {int(lb)+1} : {hint} {int(ub)+1} :{wit}")))
            flipped = flip_first_literal(wit)
            if flipped:
                yield ("conclusion-witness-literal-flipped", "reject",
                       cp(lambda o, i=i, lb=lb, hint=hint, ub=ub, f=flipped:
                          o.__setitem__(i, f"conclusion BOUNDS {lb} : {hint} {ub} :{f}")))
            # Repointing the lower-bound HINT at another legal row is not a
            # false claim: the hint is an optimisation, and the checker
            # re-establishes the bound itself. Measured accepted; recorded as a
            # weakening. The must-reject twin is the NONEXISTENT hint below.
            yield ("conclusion-lb-hint-repointed", "may",
                   cp(lambda o, i=i, lb=lb, hint=hint, ub=ub, wit=wit:
                      o.__setitem__(i, f"conclusion BOUNDS {lb} : "
                                       f"{int(hint)-1 if hint.isdigit() and int(hint) > 1 else 1}"
                                       f" {ub} :{wit}")))
            # An out-of-range hint is IGNORED, not trusted: the checker falls
            # back to establishing the bound from the database itself, and
            # still prints the true optimum. Measured accepted; the two
            # conjunction mutations below prove the fallback is a real check
            # rather than a bypass -- with the hint bogus AND the contradiction
            # row deleted it rejects, and with the hint bogus AND the bound
            # inflated by 1 it rejects.
            yield ("conclusion-lb-hint-nonexistent", "may",
                   cp(lambda o, i=i, lb=lb, ub=ub, wit=wit:
                      o.__setitem__(i, f"conclusion BOUNDS {lb} : 999999 {ub} :{wit}")))

            # Delete the LAST DERIVED ROW, whatever rule produced it -- not
            # specifically a `rup`. Four of these proofs have no `rup` line at
            # all (they close the bound with `pol` alone), and a mutation keyed
            # on `rup` degenerated on them into the benign bogus-hint mutation
            # and was scored as an ACCEPTED must-reject. A mutation that does
            # not fire is not a catch and must not look like one, so this one
            # is only emitted when there IS a derived row to remove.
            derived = [j for j, l in enumerate(lines)
                       if l.split() and l.split()[0] in ("pol", "rup", "red")]
            if derived:
                last = derived[-1]

                def _bogus_hint_and_no_contradiction(o, i=i, lb=lb, ub=ub,
                                                     wit=wit, last=last):
                    o[i] = f"conclusion BOUNDS {lb} : 999999 {ub} :{wit}"
                    o.pop(last)
                yield ("conclusion-hint-nonexistent-AND-last-derived-row-deleted",
                       "reject", cp(_bogus_hint_and_no_contradiction))
            yield ("conclusion-hint-nonexistent-AND-lb+1", "reject",
                   cp(lambda o, i=i, lb=lb, ub=ub, wit=wit:
                      o.__setitem__(i, f"conclusion BOUNDS {int(lb)+1} : 999999 {ub} :{wit}")))
        m2 = re.match(r"conclusion UNSAT : (\d+)", line)
        if m2:
            cid = int(m2.group(1))
            yield ("conclusion-unsat-hint-repointed", "reject",
                   cp(lambda o, i=i, c=cid: o.__setitem__(i, f"conclusion UNSAT : {max(1, c - 1)};")))
            yield ("conclusion-unsat->sat", "reject",
                   cp(lambda o, i=i: o.__setitem__(i, "conclusion SAT : x1;")))
        yield ("conclusion-deleted", "reject", cp(lambda o, i=i: o.pop(i)))

    # --- the upper-bound half: the logged incumbent.
    for i in idx.get("soli", [])[:1]:
        line = lines[i]
        flipped = flip_first_literal(line)
        if flipped:
            yield ("soli-witness-literal-flipped", "reject",
                   cp(lambda o, i=i, f=flipped: o.__setitem__(i, f)))
        yield ("soli-deleted", "reject", cp(lambda o, i=i: o.pop(i)))

    # --- the lower-bound half: the derivation chain.
    pols = idx.get("pol", [])
    for k, i in enumerate(pols[:4]):
        yield (f"pol-line-{k}-deleted", "reject", cp(lambda o, i=i: o.pop(i)))
        toks = lines[i].split()
        for j, t in enumerate(toks):
            if j >= 1 and t.isdigit():
                # A different EXISTING id derives a different but legal row.
                alt = list(toks)
                alt[j] = str(max(1, int(t) - 1))
                yield (f"pol-line-{k}-operand-repointed", "may",
                       cp(lambda o, i=i, a=" ".join(alt): o.__setitem__(i, a)))
                # An id that was NEVER derived is not a legal operand.
                alt2 = list(toks)
                alt2[j] = "999999"
                yield (f"pol-line-{k}-operand-nonexistent", "reject",
                       cp(lambda o, i=i, a=" ".join(alt2): o.__setitem__(i, a)))
                break
        m = re.search(r"\b(\d+) d\b", lines[i])
        if m:
            d = int(m.group(1))
            # Division is sound for every positive divisor, so BOTH directions
            # only produce another legal row.
            if d > 1:
                yield (f"pol-line-{k}-divisor-halved", "may",
                       cp(lambda o, i=i, d=d, m=m:
                          o.__setitem__(i, lines[i][:m.start(1)] + str(max(2, d // 2))
                                        + lines[i][m.end(1):])))
            yield (f"pol-line-{k}-divisor-doubled", "may",
                   cp(lambda o, i=i, d=d, m=m:
                      o.__setitem__(i, lines[i][:m.start(1)] + str(d * 2)
                                    + lines[i][m.end(1):])))
            # Zero is not a divisor at all.
            yield (f"pol-line-{k}-divisor-zeroed", "reject",
                   cp(lambda o, i=i, m=m:
                      o.__setitem__(i, lines[i][:m.start(1)] + "0" + lines[i][m.end(1):])))
        if re.search(r"\bs\b", lines[i]):
            # Saturation only lowers coefficients to the degree, so dropping it
            # leaves a legal, stronger-coefficient row.
            yield (f"pol-line-{k}-saturation-dropped", "may",
                   cp(lambda o, i=i: o.__setitem__(i, re.sub(r"\bs\b", "", lines[i]))))

    for k, i in enumerate(idx.get("rup", [])[:3]):
        yield (f"rup-line-{k}-deleted", "reject", cp(lambda o, i=i: o.pop(i)))
        m = re.search(r">= (-?\d+)", lines[i])
        has_lits = bool(re.search(r"~?x\d+", lines[i]))
        if m:
            # On a row WITH literals, raising the degree strengthens a claimed
            # consequence and must not be licensed. On the EMPTY row `>= 1`
            # (the contradiction 0 >= 1) it merely names a different
            # contradiction, which is RUP-derivable exactly when the original
            # is -- a bad mutation, recorded as such.
            yield (f"rup-line-{k}-degree-raised",
                   "reject" if has_lits else "may",
                   cp(lambda o, i=i, m=m: o.__setitem__(
                       i, lines[i][:m.start(1)] + str(int(m.group(1)) + 1) + lines[i][m.end(1):])))
        # The twin that isolates what the degree mutation was reaching for: ask
        # the checker for a row that does NOT follow by propagation.
        yield (f"rup-line-{k}-nonimplied", "reject",
               cp(lambda o, i=i: o.__setitem__(i, "rup +1 x1 >= 1 ;")))

    for k, i in enumerate(idx.get("red", [])[:2]):
        yield (f"red-line-{k}-deleted", "reject", cp(lambda o, i=i: o.pop(i)))

    # --- the header: the number of input rows the proof imports.
    for i in idx.get("f", [])[:1]:
        m = re.match(r"f (\d+)", lines[i])
        if m:
            n = int(m.group(1))
            yield ("f-header-count-raised", "reject",
                   cp(lambda o, i=i, n=n: o.__setitem__(i, f"f {n + 1} ;")))
            if n > 1:
                yield ("f-header-count-lowered", "reject",
                       cp(lambda o, i=i, n=n: o.__setitem__(i, f"f {n - 1} ;")))

    # --- whole-file: does the checker read to the END?
    mid = max(1, len(lines) // 2)
    yield ("tripwire-at-file-midpoint", "reject",
           cp(lambda o, mid=mid: o.insert(mid, "this is not a proof line")))
    yield ("truncated-at-midpoint", "reject", list(lines[:mid]))
    yield ("truncated-before-conclusion", "reject",
           [l for l in lines if not l.startswith("conclusion")])


def main():
    if len(sys.argv) < 5 or (len(sys.argv) - 3) % 2:
        raise SystemExit("usage: pb_cert_census_mutate.py <veripb> <out.json> "
                         "<opb> <pbp> [<opb> <pbp> ...]")
    veripb, out_path = sys.argv[1], sys.argv[2]
    pairs = list(zip(sys.argv[3::2], sys.argv[4::2]))

    results = []
    stats = OrderedDict(must_reject=0, must_reject_accepted=0,
                        may_accept=0, may_accept_accepted=0,
                        baseline_verified=0, cross_instance=0,
                        cross_instance_accepted=0)
    tmp = tempfile.mkdtemp(prefix="ay-cert-mutate-")

    for opb, pbp in pairs:
        with open(pbp) as fh:
            lines = fh.read().splitlines()
        code, verdict = run_checker(veripb, opb, pbp)
        base_ok = accepted(code, verdict)
        if base_ok:
            stats["baseline_verified"] += 1
        results.append(OrderedDict(
            instance=os.path.basename(opb), proof=os.path.basename(pbp),
            mutation="<none: baseline>", expectation="accept",
            checker_exit=code, verdict=verdict,
            outcome="ACCEPTED" if base_ok else "REJECTED",
            ok=base_ok))
        if not base_ok:
            # Mutating a proof the checker already refuses proves nothing.
            continue

        # DEDUPE BY CONTENT, NOT BY NAME. Two mutation rules with different
        # names routinely produce the SAME bytes on a given proof (e.g. a proof
        # whose only `pol` line is also its last derived row), and a name-keyed
        # `seen` counts those as two independent must-reject catches. That is
        # how a battery count in this repo came out 36% high. The key is the
        # sha256 of the mutant text, so byte-identical mutants are scored once
        # however many rules generated them.
        #
        # A mutant byte-identical to the ORIGINAL is worse than a duplicate: it
        # is not a mutation at all, the checker rightly ACCEPTS it, and under
        # `must-reject` it would fire a false stop-the-line. Those are excluded
        # and counted, never scored.
        original_digest = hashlib.sha256(
            ("\n".join(lines) + "\n").encode()).hexdigest()
        seen = set()
        for name, expectation, mlines in mutants(lines):
            text = "\n".join(mlines) + "\n"
            digest = hashlib.sha256(text.encode()).hexdigest()
            if digest == original_digest:
                stats["noop_mutants_excluded"] = (
                    stats.get("noop_mutants_excluded", 0) + 1)
                continue
            if digest in seen:
                stats["duplicate_mutants_excluded"] = (
                    stats.get("duplicate_mutants_excluded", 0) + 1)
                continue
            seen.add(digest)
            mpath = os.path.join(tmp, "m.pbp")
            with open(mpath, "w") as fh:
                fh.write(text)
            c, v = run_checker(veripb, opb, mpath)
            acc = accepted(c, v)
            adjudication = None
            # ADJUDICATE THE WITNESS FLIPS RATHER THAN ASSUMING THEM.
            #
            # `*-witness-literal-flipped` flips one literal of the logged
            # optimal assignment, on the assumption that this must break the
            # witness. That assumption is INSTANCE-DEPENDENT and it is false
            # whenever the flipped variable is free at the optimum: the flip
            # then yields a DIFFERENT optimal model, the proof stays correct,
            # and a correct checker accepts it. Measured on
            # mult_diagcomm_opt_less_teq_nbits_19 (optimum 0), where the
            # flipped witness is feasible -- 0 of 3325 constraints violated --
            # at objective 0.
            #
            # So when such a mutation is accepted, the expectation is decided
            # by INDEPENDENTLY evaluating the flipped assignment against the
            # formula rather than by the mutation's name. Feasible and still at
            # the claimed bound means the battery wrote a bad mutation and the
            # checker was right; anything else stays a must-reject failure and
            # a genuine alarm.
            if acc and expectation == "reject" and "witness-literal-flipped" in name:
                verdict_bound = _bound_from_verdict(v)
                feasible, obj = _check_witness(opb, mpath)
                if feasible and verdict_bound is not None and obj == verdict_bound:
                    expectation = "may"
                    adjudication = (
                        f"BAD MUTATION, not a checker defect: the flipped "
                        f"witness is independently feasible at objective {obj}, "
                        f"which is the bound the checker printed. A different "
                        f"optimal model is still an optimal model.")
                else:
                    adjudication = (
                        f"GENUINE: flipped witness feasible={feasible} "
                        f"objective={obj} vs printed bound {verdict_bound}")
            if expectation == "reject":
                stats["must_reject"] += 1
                if acc:
                    stats["must_reject_accepted"] += 1
                ok = not acc
            else:
                stats["may_accept"] += 1
                if acc:
                    stats["may_accept_accepted"] += 1
                ok = True
            rec = OrderedDict(
                instance=os.path.basename(opb), proof=os.path.basename(pbp),
                mutation=name, expectation=expectation,
                mutant_sha256=digest,
                checker_exit=c, verdict=v or "<no verdict line>",
                outcome="ACCEPTED" if acc else "REJECTED", ok=ok)
            if adjudication:
                rec["adjudication"] = adjudication
                stats["witness_flips_adjudicated"] = (
                    stats.get("witness_flips_adjudicated", 0) + 1)
            results.append(rec)

    # --- a proof must be bound to ITS OWN instance.
    for i, (opb_a, pbp_a) in enumerate(pairs):
        for j, (opb_b, _) in enumerate(pairs):
            if i == j:
                continue
            c, v = run_checker(veripb, opb_b, pbp_a)
            acc = accepted(c, v)
            stats["cross_instance"] += 1
            if acc:
                stats["cross_instance_accepted"] += 1
            results.append(OrderedDict(
                instance=os.path.basename(opb_b), proof=os.path.basename(pbp_a),
                mutation="cross-instance (proof of a DIFFERENT formula)",
                expectation="reject", checker_exit=c,
                verdict=v or "<no verdict line>",
                outcome="ACCEPTED" if acc else "REJECTED", ok=not acc))

    stats["must_reject_total"] = stats["must_reject"] + stats["cross_instance"]
    stats["must_reject_total_accepted"] = (
        stats["must_reject_accepted"] + stats["cross_instance_accepted"])
    with open(out_path, "w") as fh:
        json.dump(OrderedDict(checker=veripb, stats=stats, results=results),
                  fh, indent=1)
        fh.write("\n")
    print(json.dumps(stats, indent=2))
    bad = stats["must_reject_total_accepted"]
    if bad:
        print(f"\n*** {bad} MUTATION(S) ACCEPTED — stop the line ***", file=sys.stderr)
        return 2
    print(f"\n{stats['must_reject_total']} must-reject mutations, 0 accepted; "
          f"{stats['may_accept']} weakening mutations recorded separately "
          f"({stats['may_accept_accepted']} accepted, correctly).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
