.RECIPEPREFIX := >

LAKE ?= lake
PYTHON ?= python3
# The canonical conformance corpus. A sibling checkout by default, exactly as in
# the bindings' formal gates (`LEAN_FORMAL_DIR` sits beside `lazily-spec`).
LAZILY_SPEC_DIR ?= ../lazily-spec

.PHONY: \
	check \
	build \
	bridge-check \
	bridge-sync \
	proof-hygiene

check: build bridge-check proof-hygiene

build:
>$(LAKE) build

# Conformance bridge: LazilyFormal/Conformance/*.lean replay the canonical
# corpus inside the kernel (`lake build` fails if the model disagrees with the
# snapshot); this fails if the snapshot disagrees with lazily-spec.
bridge-check:
>$(PYTHON) scripts/gen-conformance-bridge.py --spec-dir "$(LAZILY_SPEC_DIR)" --check

bridge-sync:
>$(PYTHON) scripts/gen-conformance-bridge.py --spec-dir "$(LAZILY_SPEC_DIR)"

# Every module is reachable from the root (so `lake build` checks it) and no
# proof is open, axiomatized, or compiler-trusted.
proof-hygiene: build
>$(PYTHON) scripts/check-proof-hygiene.py
>$(LAKE) env lean scripts/AxiomAudit.lean
