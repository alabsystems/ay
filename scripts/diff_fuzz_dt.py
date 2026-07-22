#!/usr/bin/env python3
# ay-script: smt-diff-fuzz-dt
# Differential SMT fuzzer for DATATYPES (QF_DT, QF_UFDT, QF_UFDTLIA, AUFDTLIA).
# Generates well-typed random formulas mixing algebraic datatypes (enums,
# recursive lists/trees, Pair/record), constructors, selectors, testers
# ((_ is C)), datatype equality/distinct, and (in the *LIA logics) Int and
# (in AUFDTLIA) arrays. Runs AY vs z3, flags sat-vs-unsat conflicts, minimizes.
#
# CRITICAL logic-semantics note (verified against z3 4.16):
#   In pure QF_DT / QF_UFDT, z3 does NOT interpret Int (treats it as a free
#   sort): (= (v a) 1) and (= (v a) 2) is SAT for z3. So we use Int FIELDS and
#   Int arithmetic ONLY in the *LIA logics. In QF_DT/QF_UFDT we use enums,
#   uninterpreted sorts (E), Bool, and nested datatypes -- all interpreted
#   consistently by both solvers.
import argparse, json, os, random, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

RESOURCE_PLAN = None


def run(cmd, timeout):
    try:
        p = run_captured(
            cmd, RESOURCE_PLAN.memlimit_mb, timeout,
            label="diff_fuzz_dt.py",
            env=dict(os.environ, MEMLIMIT=str(RESOURCE_PLAN.memlimit_mb),
                     NBCORE=str(RESOURCE_PLAN.nbcore)),
        )
    except OSError as error:
        return f"error:{error}"
    if p.memout:
        return "memout"
    if p.timed_out:
        return "timeout"
    if p.output_truncated:
        return "error:output-truncated"
    for line in p.stdout.splitlines():
        t = line.strip()
        if t in ("sat", "unsat", "unknown"):
            return t
    # surface errors as a distinct bucket so they don't masquerade as answers
    if "error" in (p.stdout + p.stderr).lower():
        return "error"
    return "noanswer"


class Gen:
    """A fresh datatype universe + term generator per formula."""

    def __init__(self, rng, logic):
        self.rng = rng
        self.logic = logic
        self.has_uf = "UF" in logic
        self.has_int = logic in ("QF_UFDTLIA", "AUFDTLIA")
        self.has_array = logic == "AUFDTLIA"
        # leaf-field sorts available besides datatypes
        self.scalar_sorts = ["Bool", "E"]  # E = uninterpreted sort
        if self.has_int:
            self.scalar_sorts.append("Int")
        # registry: sort_name -> list of (ctor_name, [(sel_name, field_sort), ...])
        self.dts = {}
        self.dt_order = []  # declaration order for mutually-rec block
        self.consts = {}    # var_name -> sort
        self.var_ctr = 0
        self._build_datatypes()
        self._declare_consts()

    # ---- datatype universe construction ----
    def _fresh_dt_name(self):
        n = f"D{len(self.dt_order)}"
        return n

    def _build_datatypes(self):
        r = self.rng
        # Always include an enum (pigeonhole bug class).
        enum = "Enum"
        ncolors = r.randint(2, 4)
        self.dts[enum] = [(f"c{i}", []) for i in range(ncolors)]
        self.dt_order.append(enum)
        # A record/Pair with mixed scalar fields.
        rec = "Rec"
        nf = r.randint(1, 3)
        fields = []
        for j in range(nf):
            fs = r.choice(self.scalar_sorts)
            fields.append((f"rs{j}", fs))
        self.dts[rec] = [(f"mk{rec}", fields)]  # single constructor
        self.dt_order.append(rec)
        # An Option-like over a scalar (single sel; wrong-ctor selector traps).
        opt = "Opt"
        oscalar = r.choice(self.scalar_sorts)
        self.dts[opt] = [("none", []), ("some", [("val", oscalar)])]
        self.dt_order.append(opt)
        # A recursive list over a scalar element (acyclicity bug class).
        lst = "Lst"
        lelem = r.choice([s for s in self.scalar_sorts])
        self.dts[lst] = [("cons", [("hd", lelem), ("tl", lst)]), ("nil", [])]
        self.dt_order.append(lst)
        # Sometimes a recursive binary tree carrying an Enum + Rec (nested DT).
        if r.random() < 0.7:
            tree = "Tree"
            self.dts[tree] = [
                ("leaf", [("lv", "Enum")]),
                ("node", [("left", tree), ("nv", "Rec"), ("right", tree)]),
            ]
            self.dt_order.append(tree)

    def _decl_lines(self):
        # Single combined (declare-datatypes ...) for all (handles mutual rec
        # ordering trivially since we only forward-reference declared names).
        sort_decls = " ".join(f"({n} 0)" for n in self.dt_order)
        bodies = []
        for n in self.dt_order:
            ctors = []
            for cname, fields in self.dts[n]:
                if fields:
                    fs = " ".join(f"({sn} {st})" for sn, st in fields)
                    ctors.append(f"({cname} {fs})")
                else:
                    ctors.append(f"({cname})")
            bodies.append("(" + " ".join(ctors) + ")")
        lines = [f"(set-logic {self.logic})", "(declare-sort E 0)"]
        lines.append(f"(declare-datatypes ({sort_decls}) ({' '.join(bodies)}))")
        return lines

    # ---- constant declarations ----
    def _new_var(self, sort):
        self.var_ctr += 1
        name = f"v{self.var_ctr}"
        self.consts[name] = sort
        return name

    def _declare_consts(self):
        r = self.rng
        # a handful of vars per datatype + scalars
        for n in self.dt_order:
            for _ in range(r.randint(2, 3)):
                self._new_var(n)
        for s in ["E", "Bool"]:
            for _ in range(2):
                self._new_var(s)
        if self.has_int:
            for _ in range(3):
                self._new_var("Int")
        if self.has_array:
            # arrays Int -> datatype (the datatype-over-array bias)
            for n in self.dt_order:
                self._new_var(("Array", "Int", n))

    def const_decl_lines(self):
        lines = []
        for name, sort in self.consts.items():
            if isinstance(sort, tuple):
                lines.append(f"(declare-const {name} (Array {sort[1]} {sort[2]}))")
            else:
                lines.append(f"(declare-const {name} {sort})")
        if self.has_uf:
            # UF over datatypes / scalars (QF_UFDT class).
            lines.append("(declare-fun fEnum (Enum) Enum)")
            lines.append("(declare-fun fLst (Lst) Lst)")
            lines.append("(declare-fun pRec (Rec) Bool)")
            lines.append("(declare-fun gE (E) E)")
            if self.has_int:
                lines.append("(declare-fun fInt (Int) Int)")
        return lines

    # ---- helpers ----
    def vars_of(self, sort):
        return [n for n, s in self.consts.items() if s == sort]

    def arrays_to(self, sort):
        return [n for n, s in self.consts.items()
                if isinstance(s, tuple) and s[2] == sort]

    # ---- term generators by sort ----
    def int_term(self, d):
        r = self.rng
        if d <= 0 or r.random() < 0.45:
            ch = self.vars_of("Int")
            opts = [str(r.randint(-3, 3))]
            if ch:
                opts.append(r.choice(ch))
            return r.choice(opts)
        k = r.random()
        if k < 0.35:
            return f"({r.choice(['+', '-'])} {self.int_term(d-1)} {self.int_term(d-1)})"
        if k < 0.5:
            return f"(* {r.randint(-2, 2)} {self.int_term(d-1)})"
        if k < 0.7:
            # selector that yields Int (if any datatype has an Int field)
            t = self.int_selector(d-1)
            if t is not None:
                return t
        if self.has_uf and k < 0.85:
            return f"(fInt {self.int_term(d-1)})"
        return self.int_term(0)

    def int_selector(self, d):
        # find a (sort, ctor, selname) producing Int
        opts = []
        for n in self.dt_order:
            for cname, fields in self.dts[n]:
                for sn, st in fields:
                    if st == "Int":
                        opts.append((n, sn))
        if not opts:
            return None
        n, sn = self.rng.choice(opts)
        return f"({sn} {self.dt_term(n, max(d, 0))})"

    def bool_term(self, d):
        r = self.rng
        if d <= 0:
            ch = self.vars_of("Bool") + ["true", "false"]
            return r.choice(ch)
        k = r.random()
        if k < 0.14:
            return f"(not {self.bool_term(d-1)})"
        if k < 0.30:
            return f"({r.choice(['and', 'or'])} {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if k < 0.38:
            return f"(=> {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if k < 0.46:
            return f"(ite {self.bool_term(d-1)} {self.bool_term(d-1)} {self.bool_term(d-1)})"
        # tester (_ is C) over a datatype term -- core DT predicate
        if k < 0.66:
            n = r.choice(self.dt_order)
            cname = r.choice(self.dts[n])[0]
            return f"((_ is {cname}) {self.dt_term(n, d-1)})"
        # datatype equality / distinct
        if k < 0.80:
            n = r.choice(self.dt_order)
            if r.random() < 0.5:
                nn = r.randint(2, 4)
                args = " ".join(self.dt_term(n, d-1) for _ in range(nn))
                return f"(distinct {args})"
            return f"(= {self.dt_term(n, d-1)} {self.dt_term(n, d-1)})"
        # Int comparison (only meaningful in *LIA)
        if self.has_int and k < 0.90:
            op = r.choice(["<=", "<", ">=", ">", "="])
            return f"({op} {self.int_term(d-1)} {self.int_term(d-1)})"
        # Bool-field selector / Bool selector
        bsel = self.bool_selector(d-1)
        if bsel is not None and r.random() < 0.6:
            return bsel
        if self.has_uf:
            return f"(pRec {self.dt_term('Rec', d-1)})"
        # scalar equality on E
        return f"(= {self.e_term(d-1)} {self.e_term(d-1)})"

    def bool_selector(self, d):
        opts = []
        for n in self.dt_order:
            for cname, fields in self.dts[n]:
                for sn, st in fields:
                    if st == "Bool":
                        opts.append((n, sn))
        if not opts:
            return None
        n, sn = self.rng.choice(opts)
        return f"({sn} {self.dt_term(n, max(d, 0))})"

    def e_term(self, d):
        r = self.rng
        ch = self.vars_of("E")
        if d <= 0 or not ch or r.random() < 0.4:
            base = ch if ch else ["err"]
            if self.has_uf and r.random() < 0.4:
                return f"(gE {r.choice(base)})"
            return r.choice(base)
        # selector producing E
        opts = []
        for n in self.dt_order:
            for cname, fields in self.dts[n]:
                for sn, st in fields:
                    if st == "E":
                        opts.append((n, sn))
        if opts and r.random() < 0.5:
            n, sn = r.choice(opts)
            return f"({sn} {self.dt_term(n, d-1)})"
        if self.has_uf:
            return f"(gE {self.e_term(d-1)})"
        return r.choice(ch)

    def scalar_term(self, sort, d):
        if sort == "Bool":
            return self.bool_term(d)
        if sort == "Int":
            return self.int_term(d)
        if sort == "E":
            return self.e_term(d)
        # else it's a datatype sort
        return self.dt_term(sort, d)

    def dt_term(self, sort, d):
        """Generate a term of datatype `sort`."""
        r = self.rng
        ch = self.vars_of(sort)
        # base: variable, or array select (AUFDTLIA), or constructor
        if d <= 0:
            if ch and r.random() < 0.7:
                return r.choice(ch)
            return self._construct(sort, 0)
        k = r.random()
        if ch and k < 0.32:
            return r.choice(ch)
        if k < 0.50:
            return self._construct(sort, d - 1)
        # selector chain producing this datatype sort
        if k < 0.68:
            t = self._dt_selector(sort, d - 1)
            if t is not None:
                return t
        # array select producing this datatype (datatype-over-array)
        if self.has_array and k < 0.82:
            arrs = self.arrays_to(sort)
            if arrs:
                arr = r.choice(arrs)
                idx = self.int_term(d - 1)
                if r.random() < 0.4:
                    # store then select -> stresses select-over-store
                    val = self.dt_term(sort, d - 1)
                    arr = f"(store {arr} {self.int_term(d-1)} {val})"
                return f"(select {arr} {idx})"
        # UF producing a datatype (Enum/Lst)
        if self.has_uf and sort == "Enum" and k < 0.9:
            return f"(fEnum {self.dt_term('Enum', d-1)})"
        if self.has_uf and sort == "Lst" and k < 0.9:
            return f"(fLst {self.dt_term('Lst', d-1)})"
        # ite over two datatype terms
        if k < 0.95:
            return f"(ite {self.bool_term(d-1)} {self.dt_term(sort, d-1)} {self.dt_term(sort, d-1)})"
        return self._construct(sort, d - 1)

    def _dt_selector(self, sort, d):
        # find selector returning this datatype sort
        opts = []
        for n in self.dt_order:
            for cname, fields in self.dts[n]:
                for sn, st in fields:
                    if st == sort:
                        opts.append((n, sn))
        if not opts:
            return None
        n, sn = self.rng.choice(opts)
        return f"({sn} {self.dt_term(n, d)})"

    def _construct(self, sort, d):
        r = self.rng
        cname, fields = r.choice(self.dts[sort])
        if not fields:
            return cname
        args = []
        for sn, st in fields:
            args.append(self.scalar_term(st, max(d, 0)))
        return f"({cname} {' '.join(args)})"

    # ---- top-level formula ----
    def formula(self):
        r = self.rng
        lines = self._decl_lines() + self.const_decl_lines()
        asserts = []
        # Bias: occasionally inject an acyclicity trap (x = cons(.., x)).
        if r.random() < 0.5:
            xs = self.vars_of("Lst")
            if xs:
                x = r.choice(xs)
                lelem = self.dts["Lst"][0][1][0][1]  # hd field sort
                asserts.append(f"(= {x} (cons {self.scalar_term(lelem,1)} {x}))")
        # Bias: a definitional equality pinning a selector via a constructor.
        if r.random() < 0.5:
            n = r.choice(self.dt_order)
            xs = self.vars_of(n)
            if xs:
                asserts.append(f"(= {r.choice(xs)} {self._construct(n, 2)})")
        for _ in range(r.randint(3, 7)):
            asserts.append(self.bool_term(r.randint(2, 4)))
        for a in asserts:
            lines.append(f"(assert {a})")
        lines.append("(check-sat)")
        return "\n".join(lines) + "\n", asserts, lines

    def render(self, header_lines, asserts):
        out = list(header_lines)
        for a in asserts:
            out.append(f"(assert {a})")
        out.append("(check-sat)")
        return "\n".join(out) + "\n"


def both_definite(a, b):
    return a in ("sat", "unsat") and b in ("sat", "unsat")


def minimize(header_lines, asserts, ay_bin, z3_bin, timeout, target_ay, target_z3):
    """Greedy: drop asserts while the disagreement persists."""
    def disagrees(asrts):
        smt = "\n".join(header_lines) + "\n" + "".join(f"(assert {a})\n" for a in asrts) + "(check-sat)\n"
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as fh:
            fh.write(smt); p = fh.name
        try:
            ay = run([ay_bin, p], timeout)
            z3 = run([z3_bin, p], timeout)
        finally:
            os.unlink(p)
        return both_definite(ay, z3) and ay != z3 and ay == target_ay and z3 == target_z3

    cur = list(asserts)
    changed = True
    while changed:
        changed = False
        for i in range(len(cur)):
            trial = cur[:i] + cur[i + 1:]
            if trial and disagrees(trial):
                cur = trial
                changed = True
                break
    return cur


def main():
    global RESOURCE_PLAN
    ap = argparse.ArgumentParser()
    ap.add_argument("--logics", default="QF_DT,QF_UFDT,QF_UFDTLIA,AUFDTLIA")
    ap.add_argument("--n", type=int, default=2500)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--ay", default="target/release/examples/smt_run")
    ap.add_argument("--z3", default="z3")
    ap.add_argument("--timeout", type=float, default=5.0)
    ap.add_argument("--out-dir", default="/tmp/fuzz_dt_witnesses")
    args = ap.parse_args()
    if args.n <= 0 or args.timeout <= 0:
        ap.error("--n and --timeout must be positive")

    warn_concurrent_build()
    RESOURCE_PLAN = plan_solver_resources(1, label="diff_fuzz_dt.py")
    envelope = {
        "requested_jobs": 1, "jobs": RESOURCE_PLAN.jobs,
        "memlimit_mb_per_child": RESOURCE_PLAN.memlimit_mb,
        "nbcore_per_child": RESOURCE_PLAN.nbcore,
        "headroom_mb": RESOURCE_PLAN.headroom_mb,
        "enforcement": "process-group rss_watchdog; MEMLIMIT/NBCORE environment",
    }

    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "resource-envelope.json"), "w") as fh:
        json.dump(envelope, fh, indent=2)
        fh.write("\n")
    rng = random.Random(args.seed)
    logics = args.logics.split(",")
    conflicts = 0
    both_def = 0
    per_logic = {L: [0, 0] for L in logics}  # [cases, both_def]
    seen = set()
    for i in range(args.n):
        L = logics[i % len(logics)]
        gen = Gen(rng, L)
        smt, asserts, header_lines = gen.formula()
        # header is everything except the trailing (assert ...) lines + check-sat
        hdr = [ln for ln in header_lines if not ln.startswith("(assert ") and ln != "(check-sat)"]
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as fh:
            fh.write(smt); path = fh.name
        try:
            ay = run([args.ay, path], args.timeout)
            z3 = run([args.z3, path], args.timeout)
        finally:
            os.unlink(path)
        per_logic[L][0] += 1
        if both_definite(ay, z3):
            both_def += 1
            per_logic[L][1] += 1
            if ay != z3:
                conflicts += 1
                mini = minimize(hdr, asserts, args.ay, args.z3, args.timeout, ay, z3)
                msmt = "\n".join(hdr) + "\n" + "".join(f"(assert {a})\n" for a in mini) + "(check-sat)\n"
                key = msmt
                tag = "DUP" if key in seen else "NEW"
                seen.add(key)
                wpath = os.path.join(args.out_dir, f"conflict_{L}_{args.seed}_{i}_{ay}_vs_{z3}.smt2")
                with open(wpath, "w") as wf:
                    wf.write(f"; AY={ay} z3={z3} (SOUNDNESS CONFLICT) logic={L}\n" + msmt)
                print(f"[CONFLICT #{conflicts} {tag}] {L} AY={ay} z3={z3} ({len(asserts)}->{len(mini)} asserts) -> {wpath}", file=sys.stderr)
                if tag == "NEW":
                    print("----MINIMIZED----\n" + msmt + "----------------", file=sys.stderr)
        if (i + 1) % 250 == 0:
            print(f"  {i+1}/{args.n} | both-def={both_def} | conflicts={conflicts}", file=sys.stderr)
    print(f"\n=== seeds={args.seed} logics={args.logics}: {args.n} cases, both-definite={both_def} "
          f"({100*both_def/max(1,args.n):.0f}%), CONFLICTS={conflicts} ===")
    for L in logics:
        c, bd = per_logic[L]
        print(f"   {L}: {c} cases, both-def={bd} ({100*bd/max(1,c):.0f}%)")
    with open(os.path.join(args.out_dir, "summary.json"), "w") as fh:
        json.dump({
            "logics": logics,
            "seed": args.seed,
            "cases": args.n,
            "both_definite": both_def,
            "conflicts": conflicts,
            "per_logic": per_logic,
            "resource_plan": envelope,
        }, fh, indent=2)
        fh.write("\n")
    sys.exit(1 if conflicts else 0)


if __name__ == "__main__":
    main()
