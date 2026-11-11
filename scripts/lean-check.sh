#!/bin/sh
# Dcare gate: build the library, run the axiom audit, check the
# restricted companion compiles WITHOUT being part of the public build.
# FAIL: any build error, T2_postulate reintroduced, sorryAx outside the
# allowlist, a public file importing restricted, or the restricted
# companion failing to compile on its own.
set -e
cd "$(dirname "$0")/../lean"
export PATH="$HOME/.elan/bin:$PATH"
lake build
echo '--- axiom audit ---'
lake env lean Audit.lean > /tmp/dcare-audit.txt 2>&1 || {
  cat /tmp/dcare-audit.txt
  echo 'FAIL: axiom audit errored' >&2
  exit 1
}
cat /tmp/dcare-audit.txt
if rg -n "T2_postulate" /tmp/dcare-audit.txt; then
  echo 'FAIL: T2_postulate leaked into a public theorem' >&2
  exit 1
fi
if rg -n "sorryAx" /tmp/dcare-audit.txt \
    | rg -v "no_contraction_content|no_vanishing"; then
  echo 'FAIL: unexpected sorryAx in a public theorem' >&2
  exit 1
fi
echo '--- restricted companion (compiled separately, not in the public build) ---'
if [ -f ../restricted/Private.lean ]; then
  lake env lean ../restricted/Private.lean > /tmp/dcare-restricted.txt 2>&1 || {
    cat /tmp/dcare-restricted.txt
    echo 'FAIL: restricted companion does not compile' >&2
    exit 1
  }
  echo 'compiles against these interfaces'
else
  echo 'NOT PRESENT in this checkout — the confidential companion (paper §16)'
  echo 'is withheld from the public artifact; this check is skipped, not passed.'
fi
if rg -n "import.*[Rr]estricted|Dcare.Restricted" Dcare/ Dcare.lean Audit.lean; then
  echo 'FAIL: a public file references restricted/' >&2
  exit 1
fi
echo '--- remaining scheduled sorries (allowlist) ---'
rg -c "sorry" Dcare/ || true
echo 'PASS'
