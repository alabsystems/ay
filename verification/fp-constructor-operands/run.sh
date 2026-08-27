#!/bin/bash
O="${1:-$(cd "$(dirname "$0")" && pwd)/cases}"
Z3=/opt/homebrew/bin/z3
CVC5="${CVC5:-$(command -v cvc5 || echo cvc5)}"
BWZ=/opt/homebrew/bin/bitwuzla
fail=0
for f in "$O"/*.smt2; do
  n=$(basename "$f" .smt2)
  exp=$(cat "$O/$n.expect")
  z=$(timeout 300 "$Z3" "$f" 2>&1 | head -1)
  c=$(timeout 300 "$CVC5" "$f" 2>&1 | head -1)
  b=$(timeout 300 "$BWZ" "$f" 2>&1 | head -1)
  ok="OK"
  for got in "$z" "$c" "$b"; do
    [ "$got" = "$exp" ] || ok="MISMATCH"
  done
  [ "$ok" = "OK" ] || fail=1
  printf "%-46s exp=%-6s z3=%-8s cvc5=%-8s bwz=%-8s %s\n" "$n" "$exp" "$z" "$c" "$b" "$ok"
done
echo "ORACLE_FAIL=$fail"
