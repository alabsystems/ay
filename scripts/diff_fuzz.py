#!/usr/bin/env python3
# ay-script: smt-diff-fuzz
# Copyright 2026 Andrew Yates
# Differential SMT fuzzer: generate random well-typed formulas in a declared
# logic, run AY against an oracle (z3), and flag soundness conflicts
# (sat-vs-unsat). Targets AY's historically bug-prone patterns — ite-over-Int
# defining a UF application (the P1 false-SAT class), UFs over Boolean-valued
# args (the bool-arg EUF class), and multi-arg `distinct` chains.
#
# This is the DURABLE replacement for the ephemeral /tmp fuzzers prior sessions
# kept rebuilding and losing. Adversarial fuzzing finds the wrong answers that
# corpus sweeps miss (see memory: "sweeps necessary but not sufficient").
#
# Usage:
#   python3 scripts/diff_fuzz.py --logic QF_UFLIA --n 3000 --seed 1 \
#       --ay target/release/examples/smt_run --out-dir /tmp/fuzz_witnesses
#
# AY runner: either an `smt_run`-style binary taking a file arg, or the `ay`
# CLI via `--ay-stdin "<bin> --z3-mode -in"` reading from stdin.
import argparse, os, random, re, signal, subprocess, sys, tempfile

INT_BINOPS = ["+", "-"]
CMP = ["<=", "<", ">=", ">", "="]


ARITH_VARS = ["x", "y", "z", "n", "m"]


class Gen:
    def __init__(self, rng, logic):
        self.rng = rng
        self.logic = logic
        if logic in ("QF_UFLIA", "QF_AUFLIA", "QF_LIA", "QF_ALIA", "QF_NIA"):
            self.arith = "Int"
        elif logic in ("QF_LRA", "QF_UFLRA", "QF_AUFLRA", "LRA"):
            self.arith = "Real"
        else:
            self.arith = None
        self.has_uf = logic.startswith("QF_U") or logic.startswith("QF_AU")
        # Array logics over an arithmetic element/index sort (QF_ALIA, QF_AUFLIA,
        # QF_AUFLRA). Arrays are historically bug-prone in combined theories.
        self.has_array = self.arith is not None and logic.startswith("QF_A")
        # Nonlinear integer arithmetic (QF_NIA): variable*variable products —
        # pure (x*y), squared (x*x), scaled ((* c x y), the #nia-const-factor
        # class), and degree-3 — stressing the NIA relaxation, bounded
        # enumeration / factor split, and model validation paths.
        self.nonlinear = logic == "QF_NIA"

    def num_literal(self):
        r = self.rng
        if self.arith == "Real" and r.random() < 0.4:
            d = r.choice([2, 3, 4, 5])
            return f"(/ {r.randint(-5, 5)} {d})"  # rational stresses the simplex
        return str(r.randint(-3, 3))

    def header(self):
        lines = [f"(set-logic {self.logic})"]
        if self.has_uf:
            lines.append("(declare-sort U 0)")
        if self.arith:
            for v in ARITH_VARS:
                lines.append(f"(declare-const {v} {self.arith})")
            if self.has_uf:  # arith-sorted UFs (P1 ite-defined-UF-app class)
                lines.append(f"(declare-fun fa ({self.arith}) {self.arith})")
                lines.append(f"(declare-fun ga ({self.arith}) {self.arith})")
                lines.append(f"(declare-fun pa ({self.arith}) Bool)")
        for v in ("p", "q", "r", "s"):
            lines.append(f"(declare-const {v} Bool)")
        if self.has_array:
            lines.append(f"(declare-const arr1 (Array {self.arith} {self.arith}))")
            lines.append(f"(declare-const arr2 (Array {self.arith} {self.arith}))")
        if self.has_uf:
            for v in ("a", "b", "c"):
                lines.append(f"(declare-const {v} U)")
            lines.append("(declare-fun fu (U) U)")
            lines.append("(declare-fun mem (U Bool) U)")  # UF over a Bool arg
            lines.append("(declare-fun ub (U) Bool)")
        return lines

    def nl_product(self):
        # Variable-only nonlinear products (QF_NIA): the shapes NIA's monomial
        # registration, scaled-product handling, and factor split each treat
        # differently.
        r = self.rng
        k = r.random()
        v1, v2, v3 = (r.choice(ARITH_VARS) for _ in range(3))
        if k < 0.35:
            return f"(* {v1} {v2})"
        if k < 0.55:
            return f"(* {v1} {v1})"  # square
        if k < 0.80:
            return f"(* {r.randint(-3, 3)} {v1} {v2})"  # scaled (#nia-const-factor)
        return f"(* {v1} {v2} {v3})"  # degree 3

    def num_term(self, d):
        r = self.rng
        if d <= 0:
            return r.choice(ARITH_VARS + [self.num_literal()])
        k = r.random()
        if self.nonlinear:
            # QF_NIA mix: sums over products, raw products, ite-over-arith,
            # and leaves. Products stay variable-only (see nl_product).
            if k < 0.30:
                return f"({r.choice(INT_BINOPS)} {self.num_term(d-1)} {self.num_term(d-1)})"
            if k < 0.65:
                return self.nl_product()
            if k < 0.80:
                return f"(ite {self.bool_term(d-1)} {self.num_term(d-1)} {self.num_term(d-1)})"
            return r.choice(ARITH_VARS + [self.num_literal()])
        if k < 0.25:
            return f"({r.choice(INT_BINOPS)} {self.num_term(d-1)} {self.num_term(d-1)})"
        if k < 0.40:
            return f"(* {self.num_literal()} {self.num_term(d-1)})"
        if k < 0.62:  # ite-over-arith (P1 class): often defines a UF app via =
            return f"(ite {self.bool_term(d-1)} {self.num_term(d-1)} {self.num_term(d-1)})"
        if self.has_uf and k < 0.78:  # UF application over arith
            return f"({r.choice(['fa','ga'])} {self.num_term(d-1)})"
        if self.has_array and k < 0.90:  # (select arr idx) -> element
            return f"(select {self.arr_term(d-1)} {self.num_term(d-1)})"
        return r.choice(ARITH_VARS + [self.num_literal()])

    def arr_term(self, d):
        r = self.rng
        if d <= 0 or r.random() < 0.5:
            return r.choice(["arr1", "arr2"])
        # (store arr idx elem) -> array; nests select-over-store extensionality.
        return f"(store {self.arr_term(d-1)} {self.num_term(d-1)} {self.num_term(d-1)})"

    def u_term(self, d):
        r = self.rng
        if d <= 0 or r.random() < 0.4:
            return r.choice(["a", "b", "c"])
        if r.random() < 0.5:
            return f"(fu {self.u_term(d-1)})"
        return f"(mem {self.u_term(d-1)} {self.bool_term(d-1)})"  # UF over Bool arg

    def bool_term(self, d):
        r = self.rng
        if d <= 0:
            return r.choice(["p", "q", "r", "s", "true", "false"])
        k = r.random()
        if k < 0.18:
            return f"(not {self.bool_term(d-1)})"
        if k < 0.34:
            op = r.choice(["and", "or"])
            return f"({op} {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if k < 0.44:
            return f"(=> {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if k < 0.52:
            return f"(ite {self.bool_term(d-1)} {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if self.arith and k < 0.70:
            op = r.choice(CMP)  # `=`/`<` over (UF-)arith vs ite = the P1/LRA shapes
            return f"({op} {self.num_term(d-1)} {self.num_term(d-1)})"
        if self.arith and k < 0.80:  # multi-arg distinct over arith (LRA bug class)
            nn = r.randint(2, 4)
            return f"(distinct {' '.join(self.num_term(d-1) for _ in range(nn))})"
        if self.arith and self.has_uf and k < 0.84:
            return f"(pa {self.num_term(d-1)})"
        if self.has_array and k < 0.90:  # array (dis)equality / extensionality
            if r.random() < 0.5:
                return f"(= {self.arr_term(d-1)} {self.arr_term(d-1)})"
            return f"(not (= {self.arr_term(d-1)} {self.arr_term(d-1)}))"
        if self.has_uf and k < 0.93:
            nn = r.randint(2, 4)
            args = " ".join(self.u_term(d-1) for _ in range(nn))
            return f"(distinct {args})" if r.random() < 0.5 else f"(= {self.u_term(d-1)} {self.u_term(d-1)})"
        if self.has_uf:
            return f"(ub {self.u_term(d-1)})"
        return r.choice(["p", "q", "r", "s"])

    def formula(self):
        r = self.rng
        lines = self.header()
        # A definitional equality that pins a UF app to an ite (P1 false-SAT shape)
        if self.arith and self.has_uf and r.random() < 0.7:
            lines.append(f"(assert (= ({r.choice(['fa','ga'])} {self.num_term(1)}) {self.num_term(3)}))")
        # QF_NIA: give a random subset of variables SMALL asserted boxes so the
        # bounded deciders (enumeration, capped/repair search, factor split)
        # actually fire; leave the rest unbounded to stress the relaxation.
        if self.nonlinear:
            for v in ARITH_VARS:
                if r.random() < 0.55:
                    lo = r.randint(-2, 0)
                    hi = lo + r.randint(0, 3)
                    lines.append(f"(assert (and (<= {lo} {v}) (<= {v} {hi})))")
        for _ in range(r.randint(2, 6)):
            lines.append(f"(assert {self.bool_term(r.randint(2, 4))})")
        lines.append("(check-sat)")
        return "\n".join(lines) + "\n"


def run(cmd, text, timeout):
    # Launch the child as its own process-group leader (start_new_session) so a
    # timeout can kill the ENTIRE tree — otherwise a solver that forks workers
    # leaves orphaned processes at PID 1 that pile up and saturate the machine.
    p = subprocess.Popen(
        cmd,
        stdin=(subprocess.PIPE if text is not None else subprocess.DEVNULL),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )

    def _kill_tree():
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass

    try:
        out, _ = p.communicate(input=text, timeout=timeout)
    except subprocess.TimeoutExpired:
        _kill_tree()
        try:
            p.communicate(timeout=5)  # reap the killed group
        except Exception:
            pass
        return "timeout"
    except Exception as e:
        _kill_tree()
        return f"error:{e}"
    for line in out.splitlines():
        t = line.strip()
        if t in ("sat", "unsat", "unknown"):
            return t
    return "noanswer"


_MODEL_INT_RE = re.compile(
    r"\(define-fun\s+(\S+)\s+\(\)\s+Int\s+(\(-\s*\d+\)|-?\d+)\s*\)"
)


def run_capture(cmd, timeout):
    """Run `cmd`, return full stdout (or None on timeout/error). Same
    process-group kill discipline as run()."""
    p = subprocess.Popen(
        cmd,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        out, _ = p.communicate(timeout=timeout)
        return out
    except Exception:
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            p.communicate(timeout=5)
        except Exception:
            pass
        return None


def parse_int_model(out):
    """Extract {name: int} from `(define-fun name () Int val)` lines."""
    vals = {}
    for m in _MODEL_INT_RE.finditer(out or ""):
        raw = m.group(2).replace("(-", "-").replace(")", "").replace(" ", "")
        vals[m.group(1)] = int(raw)
    return vals


def z3_pin_check(z3_bin, smt, model, timeout):
    """Pin AY's model values into the formula and ask z3: must be sat.
    Returns 'sat'/'unsat'/'unknown'/'timeout'/'nomodel'."""
    if not model:
        return "nomodel"
    body = smt.replace("(check-sat)", "")
    pins = "\n".join(f"(assert (= {name} {value}))" for name, value in sorted(model.items()))
    pinned = body + pins + "\n(check-sat)\n"
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as fh:
        fh.write(pinned)
        path = fh.name
    try:
        return run([z3_bin, path], None, timeout)
    finally:
        os.unlink(path)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--logic", default="QF_UFLIA")
    ap.add_argument("--n", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--ay", default="target/release/examples/smt_run",
                    help="AY binary taking a file arg")
    ap.add_argument("--ay-stdin", default="", help="AY cmd reading SMT2 from stdin (overrides --ay), e.g. 'target/debug/ay --z3-mode -in'")
    ap.add_argument("--z3", default="z3")
    ap.add_argument("--timeout", type=float, default=5.0)
    ap.add_argument("--out-dir", default="/tmp/diff_fuzz_witnesses")
    ap.add_argument("--pin-models", action="store_true",
                    help="When AY answers sat, re-run AY with (get-model), pin "
                         "every Int value into the formula, and require z3 to "
                         "accept the pinned formula (model cross-validation). "
                         "Needs --ay to be the `ay` CLI (file arg, get-model).")
    args = ap.parse_args()

    os.makedirs(args.out_dir, exist_ok=True)
    rng = random.Random(args.seed)
    conflicts = 0
    both_def = 0
    pins_checked = 0
    pin_failures = 0
    for i in range(args.n):
        gen = Gen(rng, args.logic)
        smt = gen.formula()
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as fh:
            fh.write(smt)
            path = fh.name
        try:
            if args.ay_stdin:
                ay = run(args.ay_stdin.split(), smt, args.timeout)
            else:
                ay = run([args.ay, path], None, args.timeout)
            z3 = run([args.z3, path], None, args.timeout)
            if ay in ("sat", "unsat") and z3 in ("sat", "unsat"):
                both_def += 1
                if ay != z3:
                    conflicts += 1
                    wpath = os.path.join(args.out_dir, f"conflict_{args.logic}_{args.seed}_{i}_{ay}_vs_{z3}.smt2")
                    with open(wpath, "w") as wf:
                        wf.write(f"; AY={ay} z3={z3} (SOUNDNESS CONFLICT)\n" + smt)
                    print(f"[CONFLICT #{conflicts}] AY={ay} z3={z3} -> {wpath}", file=sys.stderr)
            # Model cross-validation (z3-pinning): AY's sat model, asserted
            # value-by-value, must remain sat under z3.
            if args.pin_models and ay == "sat" and not args.ay_stdin:
                mpath = path + ".model.smt2"
                with open(mpath, "w") as mf:
                    mf.write(smt + "(get-model)\n")
                try:
                    mout = run_capture([args.ay, mpath], args.timeout * 2)
                finally:
                    os.unlink(mpath)
                model = parse_int_model(mout)
                if model:
                    pins_checked += 1
                    pin_verdict = z3_pin_check(args.z3, smt, model, args.timeout)
                    if pin_verdict == "unsat":
                        pin_failures += 1
                        conflicts += 1
                        wpath = os.path.join(
                            args.out_dir,
                            f"pinfail_{args.logic}_{args.seed}_{i}.smt2")
                        with open(wpath, "w") as wf:
                            wf.write(f"; AY model rejected by z3 pin-check: {model}\n" + smt)
                        print(f"[PIN-FAIL #{pin_failures}] AY model {model} rejected -> {wpath}",
                              file=sys.stderr)
        finally:
            os.unlink(path)
        if (i + 1) % 500 == 0:
            print(f"  {i+1}/{args.n} | both-definite={both_def} | conflicts={conflicts} "
                  f"| pins={pins_checked} pin-failures={pin_failures}", file=sys.stderr)
    print(f"\n=== {args.logic} seed={args.seed}: {args.n} cases, both-definite={both_def}, "
          f"SOUNDNESS CONFLICTS={conflicts}, pins={pins_checked}, pin-failures={pin_failures} ===")
    sys.exit(1 if conflicts else 0)


if __name__ == "__main__":
    main()
