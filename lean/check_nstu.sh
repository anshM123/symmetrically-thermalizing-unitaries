#!/usr/bin/env bash
# Check the formalisation of Theorem 2 (N identical systems): every NSTUProof file in dependency order, then the
# axioms of 41 declarations and a keyword scan. Run from this directory (the Lake project root) with the Lean
# toolchain on PATH, after the two-system development has been built:
#   export PATH="$HOME/.elan/bin:$PATH"; lake exe cache get; bash check.sh && bash check_genh.sh && bash check_nstu.sh
# The NSTUProof files import STUProof modules (including STUProof.GeneralH) from the build directory.
set -euo pipefail
stu=.lake/build/lib/lean/STUProof
if [ ! -f "$stu/KirwanFreeFinal.olean" ] || [ ! -f "$stu/GeneralH.olean" ]; then
  echo "STUProof is not built yet: run 'bash check.sh && bash check_genh.sh' first." >&2
  exit 1
fi
out=.lake/build/lib/lean/NSTUProof
mkdir -p "$out"
for f in NSTUBasic NSTUEven NSTULCS NSTUVertex NSTUKirwan NSTUChain NSTUSmallD NSTUSanity; do
  echo "== NSTUProof/$f.lean"
  lake env lean -o "$out/$f.olean" -i "$out/$f.ilean" "NSTUProof/$f.lean"
done
echo "== NSTUProof/Axioms.lean"
lake env lean NSTUProof/Axioms.lean
echo "== forbidden keywords (sorry/admit/axiom/native_decide):"
grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' NSTUProof/*.lean || echo "none"
