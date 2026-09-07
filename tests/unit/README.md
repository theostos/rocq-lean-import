# Parser-only regressions

Run in a Rocq development environment with `ocamlfind` and `rocq-runtime.vernac`:

```sh
bash tests/unit/run.sh
```

This compiles only the parser and runs small OCaml fixtures. It does not start
a Rocq worker, import cslib or test kernel conversion.
