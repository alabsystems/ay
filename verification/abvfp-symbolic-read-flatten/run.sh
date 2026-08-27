#!/bin/bash
# Copyright 2026 Andrew Yates
# Discharge every obligation with z3, cvc5 and bitwuzla. Expected answers are in
# the sibling .expect files; a mismatch from ANY solver is a hard failure.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
CASES="${1:-$HERE/cases}"
Z3="${Z3:-z3}"
CVC5="${CVC5:-$(command -v cvc5 || echo cvc5)}"
BWZ="${BWZ:-bitwuzla}"
fail=0
for f in "$CASES"/*.smt2; do
  n=$(basename "$f" .smt2)
  exp=$(cat "$CASES/$n.expect")
  z=$(timeout 600 "$Z3" "$f" 2>&1 | head -1)
  c=$(timeout 600 "$CVC5" "$f" 2>&1 | head -1)
  b=$(timeout 600 "$BWZ" "$f" 2>&1 | head -1)
  ok="OK"
  for got in "$z" "$c" "$b"; do [ "$got" = "$exp" ] || ok="MISMATCH"; done
  [ "$ok" = "OK" ] || fail=1
  printf "%-12s exp=%-6s z3=%-8s cvc5=%-8s bitwuzla=%-8s %s\n" "$n" "$exp" "$z" "$c" "$b" "$ok"
done
echo "FAIL=$fail"
exit $fail
