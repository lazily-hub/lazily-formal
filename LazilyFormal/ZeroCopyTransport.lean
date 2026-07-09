/-
! Cross-process zero-copy transport — pluggable blob backends (#lzzcpy).

The formal counterpart of `lazily-spec/docs/zero-copy-transport.md` and the
descriptor-resolution contract behind `ShmBlobRef` / `IpcValueSharedBlob`.

A large payload is not copied through the wire codec. The producer spills it to a
**blob backend** (POSIX `shm`, Apache Arrow IPC/Flight, or an in-process arena)
and ships a `Descriptor`; the receiver resolves the descriptor against the same
backend and reads the bytes in place — zero copy. The descriptor carries a
`backend` discriminator so a receiver routes resolution to the right backend.

The model is **backend-agnostic**: it is parameterised only by the table of blobs
a backend has issued plus the `resolve` lookup. Any concrete backend
(shm / Arrow / in-process) that maintains its issued-table semantics instantiates
the laws, so the transport theorems hold uniformly — the universal guarantee no
single-adapter fixture can establish.
-/

namespace LazilyFormal.ZeroCopyTransport

/-- Wire discriminator: which backend holds the blob. -/
inductive BackendKind
  | shm        -- POSIX shared memory (default cross-process backend)
  | arrow      -- Apache Arrow IPC / Flight (columnar zero-copy)
  | inProcess  -- an in-process arena (single address space; e.g. the FFI host)
  deriving DecidableEq, Repr

/-- The payload bytes (a byte sequence). -/
abbrev Bytes := List Nat

/-- A descriptor into a blob backend: backend kind + a backend-local id +
generation (ABA guard) + checksum (integrity). Mirrors `ShmBlobRef` extended with
a `kind`. -/
structure Descriptor where
  kind : BackendKind
  id : Nat
  generation : Nat
  checksum : Nat
  deriving Repr

/-- A backend's issued-blob table: each descriptor the backend has minted (via
`write`) paired with the exact bytes it holds for it. -/
abbrev Issued := List (Descriptor × Bytes)

/-- Descriptor equivalence on the integrity-relevant fields (kind + id +
generation + checksum). Two descriptors are equivalent iff they name the same
backend slot at the same generation with the same checksum. -/
def sameDesc (d e : Descriptor) : Prop :=
  d.kind = e.kind ∧ d.id = e.id ∧ d.generation = e.generation ∧ d.checksum = e.checksum

instance (d e : Descriptor) : Decidable (sameDesc d e) := by
  unfold sameDesc; infer_instance

/-- A descriptor is equivalent to itself. -/
theorem sameDesc_self (d : Descriptor) : sameDesc d d :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Zero-copy resolution: look up `d` in the backend's issued table. Returns the
stored bytes iff some issued descriptor is `sameDesc d`; `none` otherwise (unknown
/ stale-generation / corrupt-checksum / wrong-backend). Returns the backend's
*own* bytes object — no copy, no transformation. -/
def resolve (d : Descriptor) : Issued → Option Bytes
  | [] => none
  | (e, b) :: rest => if sameDesc d e then some b else resolve d rest

/-- `write` registers bytes with a backend, minting a fresh descriptor (new id,
current generation, the bytes' checksum) and prepending the entry to the issued
table. -/
def write (kind : BackendKind) (gen : Nat) (b : Bytes) (issued : Issued) :
    Descriptor × Issued :=
  let id := issued.length
  let csum := b.foldl (fun h x => h + x + 1) 0
  let d := { kind := kind, id := id, generation := gen, checksum := csum }
  (d, (d, b) :: issued)

/-! ### Resolution laws (backend-agnostic) -/

/-- An empty backend resolves nothing. -/
theorem resolve_empty (d : Descriptor) : resolve d [] = none := rfl

/-- A literal cons whose head descriptor is the resolver itself: the core law. -/
theorem resolve_cons_self (d : Descriptor) (b : Bytes) (rest : Issued) :
    resolve d ((d, b) :: rest) = some b := by
  simp only [resolve, if_pos (sameDesc_self d)]

/-- **Spill-then-resolve identity / zero-copy correctness.** Resolving the
descriptor a backend minted via `write` returns exactly the bytes written — the
consumer reads the backend's own bytes, not a copy. -/
theorem resolve_write (kind : BackendKind) (gen : Nat) (b : Bytes) (issued : Issued) :
    resolve (write kind gen b issued).1 (write kind gen b issued).2 = some b :=
  resolve_cons_self (write kind gen b issued).1 b issued

/-- **Backend isolation / routing.** A descriptor of one backend kind never
resolves against an entry of a different kind — a `shm` descriptor does not
resolve in an Arrow table (and vice versa), so a receiver must route resolution
by the descriptor's `kind`. -/
theorem resolve_wrong_backend (d e : Descriptor) (b : Bytes) (rest : Issued)
    (h : d.kind ≠ e.kind) : resolve d ((e, b) :: rest) = resolve d rest := by
  have hne : ¬ sameDesc d e := fun hs => h hs.1
  simp only [resolve, if_neg hne]

/-- **Generation / ABA safety.** A descriptor whose generation differs from the
entry's never matches, so a slot reused at a later generation (or a stale ref to
a freed slot) does not resolve against the new occupant. -/
theorem resolve_stale_generation (d e : Descriptor) (b : Bytes) (rest : Issued)
    (h : d.generation ≠ e.generation) : resolve d ((e, b) :: rest) = resolve d rest := by
  have hne : ¬ sameDesc d e := fun hs => h hs.2.2.1
  simp only [resolve, if_neg hne]

/-- **Checksum integrity.** A descriptor whose checksum differs never matches, so
a corrupted-in-transit descriptor is rejected rather than resolving to the wrong
bytes. -/
theorem resolve_corrupt_checksum (d e : Descriptor) (b : Bytes) (rest : Issued)
    (h : d.checksum ≠ e.checksum) : resolve d ((e, b) :: rest) = resolve d rest := by
  have hne : ¬ sameDesc d e := fun hs => h hs.2.2.2
  simp only [resolve, if_neg hne]

/-! ### End-to-end transport round-trip -/

/-- A message payload is either inline bytes (copied through the codec) or a
spilled descriptor (resolved zero-copy at the receiver). -/
inductive Payload
  | inline : Bytes → Payload
  | spilled : Descriptor → Payload

/-- Spill inline bytes to the backend: mint a descriptor and return the spilled
payload plus the extended issued table. -/
def spill (kind : BackendKind) (gen : Nat) (b : Bytes) (issued : Issued) :
    Payload × Issued :=
  let (d, issued') := write kind gen b issued
  (Payload.spilled d, issued')

/-- Receive a payload: return its bytes. Inline bytes come back directly;
spilled descriptors resolve against the backend (zero copy). -/
def receive (p : Payload) (issued : Issued) : Option Bytes :=
  match p with
  | Payload.inline b => some b
  | Payload.spilled d => resolve d issued

/-- **Transport round-trip (end-to-end zero-copy).** Spilling bytes to a backend
and then receiving the spilled payload against the resulting table yields the
original bytes — the consumer sees exactly what the producer spilled, via a
descriptor, with no copy through the wire. This is `resolve_write` lifted to the
payload layer, and it holds for every backend (shm / Arrow / in-process) since
`write`/`resolve` are backend-agnostic. -/
theorem transport_roundtrip (kind : BackendKind) (gen : Nat) (b : Bytes)
    (issued : Issued) :
    receive (spill kind gen b issued).1 (spill kind gen b issued).2 = some b := by
  show resolve (write kind gen b issued).1 (write kind gen b issued).2 = some b
  exact resolve_write kind gen b issued

end LazilyFormal.ZeroCopyTransport
