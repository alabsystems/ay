#!/usr/bin/env python3
"""A DETERMINISTIC stand-in for the `ay` binary, used only by the harness self-test.

WHY A FAKE SOLVER
-----------------
The proof harness has silently "measured nothing" three times (dangling symlinks,
a [WARN] masking the real [ERROR], a stderr-only signal scanned on stdout). Each
time the harness printed PASS. To make that impossible we need fixtures whose
correct classification is KNOWN IN ADVANCE -- including classifications real AY
cannot produce on demand, e.g. "emits a proof carcara cannot parse" or "answers
sat on an unsat instance".

So the self-test runs the REAL scripts (scripts/check_proofs.sh,
scripts/soundness_sweep.py) unmodified, with `--ay`/`AY_BIN` pointed at this stub.
Every code path under test -- work-cell symlinking, answer parsing, carcara
invocation, reason extraction, counters, exit codes -- is the production path.
Only the solver is swapped for one whose behaviour is spelled out in the fixture.

FIXTURE PROTOCOL
----------------
Each fixture is ONE self-contained .smt2 file. It is a legal SMT-LIB problem
(so carcara, z3 and cvc5 can all read it) that additionally carries `;` comment
directives telling this stub how to behave:

    ; AY-ANSWER: unsat            what to print on stdout   (omit => print nothing)
    ; AY-STDERR: (:reason-unknown "incomplete")   extra line on stderr
    ; AY-RC: 124                  process exit code         (default 0)
    ; AY-PROOF-BEGIN              start of the canned Alethe proof
    ;| (assume h1 p)              proof body, one line per `;|`
    ; AY-PROOF-END

The proof is embedded rather than kept in a sibling file on purpose: the harness
hands the solver a SYMLINK inside a scratch work cell, so anything resolved
relative to the argument would have to chase the link -- exactly the class of bug
(see check_proofs.sh's absolutize note) these fixtures exist to catch. A
self-contained file cannot be defeated by a broken link: if the link dangles this
stub reads nothing, emits nothing, and the run is classified `no-answer`, which
is precisely what we want the guard to notice.

The `; EXPECT-...` directives in the same file are read by
scripts/selftest_proof_harness.py, never by this stub.

INVOCATION MODES (both real harness paths)
    ay -T:20 /path/to/case.smt2        (check_proofs.sh)   -> reads the file,
                                        writes /path/to/case.smt2.alethe
    ay --z3-mode -T:10 < case.smt2     (soundness_sweep.py) -> reads stdin,
                                        writes no proof (nothing to write it next to)
"""
import os
import sys

VERSION = "ay 0.0.0-FAKE (benchmarks/proof-fixtures/fake_ay.py harness self-test stub)"


def parse(text):
    """Pull the behaviour directives out of a fixture's comment lines."""
    answer, stderr_lines, rc = None, [], 0
    proof, in_proof = [], False
    for raw in text.splitlines():
        s = raw.strip()
        if not s.startswith(";"):
            continue
        body = s.lstrip(";").strip()
        if body.startswith("AY-PROOF-BEGIN"):
            in_proof = True
        elif body.startswith("AY-PROOF-END"):
            in_proof = False
        elif s.startswith(";|"):
            if in_proof:
                # everything after ';|' verbatim, minus one leading space
                line = s[2:]
                proof.append(line[1:] if line.startswith(" ") else line)
        elif body.startswith("AY-ANSWER:"):
            answer = body.split(":", 1)[1].strip()
        elif body.startswith("AY-STDERR:"):
            stderr_lines.append(body.split(":", 1)[1].strip())
        elif body.startswith("AY-RC:"):
            rc = int(body.split(":", 1)[1].strip())
    return answer, stderr_lines, rc, proof


def main(argv):
    if "--version" in argv:
        print(VERSION)
        return 0

    # The real `ay` takes the problem as a positional path, or on stdin under
    # --z3-mode. Mirror that: last existing-file argument wins, else stdin.
    path = None
    for a in argv[1:]:
        if not a.startswith("-") and os.path.isfile(a):
            path = a

    if path is not None:
        with open(path, errors="ignore") as fh:
            text = fh.read()
    else:
        text = sys.stdin.read() if not sys.stdin.isatty() else ""

    answer, stderr_lines, rc, proof = parse(text)

    # A proof is only written when we were given a path to write it next to --
    # exactly like real AY, which writes <input>.alethe and writes nothing in
    # --z3-mode/stdin.
    if path is not None and proof:
        with open(path + ".alethe", "w") as fh:
            fh.write("\n".join(proof) + "\n")

    for line in stderr_lines:
        print(line, file=sys.stderr)
    if answer:
        print(answer)
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv))
