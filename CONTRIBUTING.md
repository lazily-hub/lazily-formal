# Contributing to lazily-formal

## Verify a change

```bash
make check   # lake build + conformance-bridge drift check + axiom audit
```

`make check` expects a sibling `lazily-spec` checkout (`LAZILY_SPEC_DIR`
overrides the path). After a bridged fixture changes in `lazily-spec`, run
`make bridge-sync` and commit the regenerated `LazilyFormal/Conformance/`
modules; never edit them by hand.

The project is pinned to Lean 4.30.0 via `lean-toolchain` and has no external
dependencies beyond the Lean standard library (the bridge and hygiene scripts
use only the Python 3 standard library).
