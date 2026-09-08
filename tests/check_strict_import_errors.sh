#!/usr/bin/env bash
# Run after compiling strict_import_errors.v; Redirect appends .out.
set -Eeuo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
grep -Fxq 'Stopped!' strict-stop.out
grep -Fxq 'Done!' strict-done.out
grep -Fq 'StrictBad' strict-stop.out
grep -Fq 'StrictBad' strict-fail.out
for log in strict-stop.out strict-fail.out strict-eof.out; do
  test -r "$log"
  if grep -Fxq 'Done!' "$log"; then
    printf 'Unexpected success summary in %s\n' "$log" >&2
    exit 1
  fi
done
printf 'Stop, Fail and past-EOF summaries passed.\n'
