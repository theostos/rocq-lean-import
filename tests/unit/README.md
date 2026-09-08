# Parser-only regressions

Run in a Rocq development environment with `ocamlfind` and `rocq-runtime.vernac`:

```sh
bash tests/unit/run.sh
```

This compiles only the parser and runs small OCaml fixtures. It does not start
a Rocq worker, import cslib or test kernel conversion.

The fixtures check:

- Definition metadata: legacy tags, abbreviations, regular heights, and the
  distinction between an opaque hint and a genuinely opaque declaration.
- Persistent parser indices, snapshot isolation and legacy-state migration.
- Indexed checkpoint round trips, expression sharing and malformed data.
