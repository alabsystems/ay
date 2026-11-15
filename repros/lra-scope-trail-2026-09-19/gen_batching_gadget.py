import sys
N = int(sys.argv[1]); m = int(sys.argv[2])
out = ["(set-logic QF_LRA)"]
for i in range(N):
    out.append(f"(declare-fun f{i} () Real)")
    out.append(f"(declare-fun g{i} () Real)")
    out.append(f"(assert (or (>= f{i} 0) (<= g{i} 0)))")
    out.append(f"(assert (or (not (>= f{i} 0)) (not (<= g{i} 0))))")
out.append("(declare-fun x () Real)")
out.append("(declare-fun k () Real)")
out.append("(assert (or (>= x 0) (>= k 0)))")
out.append("(assert (or (>= x 0) (not (>= k 0))))")
out.append(f"(assert (or (not (>= f{m} 0)) (<= x (- 1))))")
out.append(f"(assert (or (>= f{m} 0) (< x 0)))")
out.append("(check-sat)")
print("\n".join(out))
