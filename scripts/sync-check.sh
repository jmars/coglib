#!/bin/sh
# Sync-check: every backtick-quoted identifier in the paper that looks
# like a Lean declaration name matches a real declaration in the
# development. FAIL on any dead anchor.
set -e
cd "$(dirname "$0")/.."

# Candidate anchors: backtick-quoted lowercase snake_case identifiers
# (the paper's theorem/definition name convention), filtering out
# known non-declaration words (syntax, core axioms, single letters)
CANDIDATES=$(rg -o '`[a-z_][a-z0-9_]*`' paper/paper.md |
  tr -d '`' |
  sort -u |
  rg -v '^(cons|content|dcare|fix|fst|feed|gen|knower|let|lete|nil|red|obj|terminate|var|unit|trace|stream|later|tensor|arrow|propext|self|snd|sorry|Quot|Classical|body|arg|fn|hd|tl|t|u|w|x|y|a|b|c|d|e|f|g|h|i|j|k|l|m|n|p|q|r|s|v|z)$')

if [ -z "$CANDIDATES" ]; then
  echo "PASS sync-check: no anchors found"
  exit 0
fi

FAIL=0
TOTAL=0
for name in $CANDIDATES; do
  TOTAL=$((TOTAL + 1))
  if rg -q "theorem $name\b|def $name\b|inductive $name\b|structure $name\b|abbrev $name\b|class $name\b" lean/Dcare/*.lean 2>/dev/null; then
    :
  else
    # Check if it's a constructor name (inductive constructor patterns)
    if rg -q "\| $name\b" lean/Dcare/*.lean 2>/dev/null; then
      :
    else
      echo "FAIL: \`$name\` cited in paper but not found as a declaration in lean/Dcare/"
      FAIL=1
    fi
  fi
done

if [ "$FAIL" -eq 0 ]; then
  echo "PASS sync-check: $TOTAL anchors all match declarations"
else
  echo "FAIL sync-check: dead anchors found"
  exit 1
fi
