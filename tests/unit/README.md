# Definition metadata regression

Run with `ocamlfind` and the matching Rocq `rocq-runtime.vernac` package:

```sh
bash tests/unit/run.sh
```

This parser-only test checks legacy records, abbreviations, regular heights and
opaque hints versus genuine opacity. It checks body sharing and universe order,
not kernel opacity, conversion or strategy replay. No Rocq worker is started.
