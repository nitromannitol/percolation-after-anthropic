#!/bin/bash
# Elaborate one file standalone with the project's exact lean options (the
# same options lakefile.toml sets for the build), reporting the compiler's
# output verbatim.  For a Challenge file the expected outcome is rc=0 with
# exactly one `declaration uses 'sorry'` warning (the intentional target);
# for every other file, rc=0 with empty output.
#
# Usage (from the repository root or from PercolationAudit/):
#   bash PercolationAudit/check_standalone.sh PercolationAudit/SiteCriticality/Challenge.lean
#   bash PercolationAudit/check_standalone.sh --vocabulary
# The second form checks that the vocabulary block between VOCABULARY-BEGIN and
# VOCABULARY-END is byte-identical in every PercolationAudit/*/Challenge.lean and in
# PercolationAudit/*/SolutionBasic.lean.
set -u
cd "$(dirname "$0")/.."
if [ "${1:-}" = "--vocabulary" ]; then
  block() { sed -n '/^-- VOCABULARY-BEGIN$/,/^-- VOCABULARY-END$/p' "$1"; }
  RC=0
  for c in PercolationAudit/*/Challenge.lean; do
    d="$(dirname "$c")/SolutionBasic.lean"
    H1=$(block "$c" | sha256sum | cut -d' ' -f1)
    H2=$(block "$d" | sha256sum | cut -d' ' -f1)
    if [ "$H1" = "$H2" ]; then echo "identical  $c  $d"; else echo "DIFFERENT  $c  $d"; RC=1; fi
  done
  exit $RC
fi
SRC="$1"
OUTPUT=$(lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false "$SRC" 2>&1)
RC=$?
printf '%s\n' "$OUTPUT"
echo "rc=$RC output-bytes=$(printf '%s' "$OUTPUT" | wc -c) file=$SRC"
exit $RC
