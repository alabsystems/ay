#!/usr/bin/env python3
"""Extract every SMT block from the Fix A test file and write it out so the
three reference solvers can adjudicate the expected verdicts independently."""
import re, pathlib, sys

src = pathlib.Path(sys.argv[1]).read_text()
out = pathlib.Path(sys.argv[2]); out.mkdir(parents=True, exist_ok=True)

# each check(...) call: name string then r#"..."# block then SolverOutcome::X
pat = re.compile(r'check\(\s*"([^"]+)",\s*r#"(.*?)"#,\s*SolverOutcome::(\w+)', re.S)
n = 0
for name, body, expect in pat.findall(src):
    (out / f"{name}.smt2").write_text(body.strip() + "\n")
    (out / f"{name}.expect").write_text(expect.lower() + "\n")
    n += 1
print(f"{n} obligations -> {out}")
