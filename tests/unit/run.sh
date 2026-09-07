#!/usr/bin/env bash
set -Eeuo pipefail
test_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
source_dir=$(cd -- "$test_dir/../../src" && pwd -P)
scratch=$(mktemp -d -t lean-parser-tests.XXXXXXXX)
trap 'rm -r -- "$scratch"' EXIT
compiler=(ocamlfind ocamlc -rectypes -thread -package rocq-runtime.vernac -I "$scratch")
for module in leanName leanExpr leanParse; do
  "${compiler[@]}" -c "$source_dir/$module.mli" -o "$scratch/$module.cmi"
  if [[ -f $source_dir/$module.ml ]]; then
    "${compiler[@]}" -c "$source_dir/$module.ml" -o "$scratch/$module.cmo"
  fi
done
for test in chunked_parse checkpoint; do
  "${compiler[@]}" -c "$test_dir/$test.ml" -o "$scratch/$test.cmo"
  "${compiler[@]}" -linkpkg "$scratch/leanName.cmo" "$scratch/leanParse.cmo" \
    "$scratch/$test.cmo" -o "$scratch/$test.exe"
  "$scratch/$test.exe"
done
