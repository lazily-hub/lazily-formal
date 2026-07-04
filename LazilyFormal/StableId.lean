/-
! Manufactured identity for text — anchored / content / similarity key layers.

The formal counterpart of `lazily-{rs,kt,js}` stable-id alignment and
`lazily-spec/cell-model.md` § "Manufactured identity for text", behind
`lazily-spec/conformance/collections/stableid_alignment.json`.

Markdown has no inherent node ids, so reconciliation keys are *manufactured* from text in
three layers, and the fixture pins one property of each:

1. **In-band anchors** — exact, survive a full body rewrite. Modelled as `Key.anchored`,
   whose payload ignores the block text (`anchored_survives_rewrite`).
2. **Content-derived keys** of whitespace-normalized text — survive reflow/reorder, change
   on edit. Modelled as `Key.content` carrying the normalized word list, so two blocks
   share a content key iff their normalized text is identical (`content_key_eq_iff`); the
   reflow case is `content_key_reflow`.
3. **Similarity alignment** — a word-LCS ratio `≥ 0.5` reads as an *edit* (key inherited
   from the matched predecessor → an `update`), below as a genuine *insert*
   (`classify_self`, `classify_small_edit`, `classify_genuine_insert`).

The `a:` / `c:` keyspaces never collide — they are distinct constructors of `Key`, so
`Key.anchored ≠ Key.content` holds by construction (`keyspaces_disjoint`).
-/

namespace LazilyFormal.StableId

/-- A normalized text token (whitespace already collapsed away pre-tokenization). -/
abbrev Word := Nat

/-- A manufactured reconciliation key. The two constructors are the `a:` (anchored) and
`c:` (content) keyspaces; being distinct constructors they can never be equal. -/
inductive Key where
  | anchored (a : Nat)
  | content (words : List Word)
deriving DecidableEq

/-- A text block: an optional in-band anchor and its whitespace-normalized words. -/
structure Block where
  anchor : Option Nat
  words : List Word

/-- The manufactured key: an anchored block keys off its anchor (text-independent); an
anchorless block keys off its normalized content. -/
def key : Block → Key
  | ⟨some a, _⟩ => .anchored a
  | ⟨none, w⟩ => .content w

/-! ### Keyspaces never collide -/

/-- `a:` and `c:` keyspaces are disjoint by construction. -/
theorem keyspaces_disjoint (a : Nat) (w : List Word) :
    (Key.anchored a) ≠ (Key.content w) := by
  intro h; cases h

/-- An anchored block and an anchorless block can never share a key. -/
theorem anchored_content_never_collide (a : Nat) (w : List Word) (t : List Word) :
    key ⟨some a, t⟩ ≠ key ⟨none, w⟩ := by
  simp only [key]; exact keyspaces_disjoint a w

/-! ### Anchored keys survive a full body rewrite -/

/-- An anchored key is a pure function of the anchor: rewriting the entire body leaves the
key identical. -/
theorem anchored_survives_rewrite (a : Nat) (t1 t2 : List Word) :
    key ⟨some a, t1⟩ = key ⟨some a, t2⟩ := rfl

/-! ### Content keys survive reflow but change on edit -/

/-- Two anchorless blocks share a content key iff their normalized text is identical — so
whitespace-only reflow (same tokens) preserves the key, and any word-level edit changes
it. -/
theorem content_key_eq_iff (t1 t2 : List Word) :
    key ⟨none, t1⟩ = key ⟨none, t2⟩ ↔ t1 = t2 := by
  simp only [key, Key.content.injEq]

/-- Reflow (same normalized tokens, different whitespace) preserves the content key. -/
theorem content_key_reflow (t : List Word) :
    key ⟨none, t⟩ = key ⟨none, t⟩ := rfl

/-- A word-level edit changes the content key. -/
theorem content_key_changes_on_edit (t1 t2 : List Word) (h : t1 ≠ t2) :
    key ⟨none, t1⟩ ≠ key ⟨none, t2⟩ := by
  intro heq; exact h ((content_key_eq_iff t1 t2).mp heq)

/-! ### Similarity alignment: word-LCS ratio distinguishes edit from insert -/

/-- Length of the longest common subsequence of two word lists. -/
def lcs : List Word → List Word → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs =>
    if a == b then 1 + lcs as bs
    else max (lcs (a :: as) bs) (lcs as (b :: bs))
termination_by a b => a.length + b.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals omega

/-- The LCS of a list with itself is its full length. -/
theorem lcs_self : (a : List Word) → lcs a a = a.length
  | [] => by simp [lcs]
  | x :: xs => by
    unfold lcs
    simp only [beq_self_eq_true, if_true, lcs_self xs, List.length_cons]
    omega

/-- An alignment verdict: an `edited` block inherits its predecessor's key (an `update`);
an `inserted` block mints a fresh one. -/
inductive Match where
  | edited
  | inserted
deriving DecidableEq

/-- Word-LCS ratio `≥ 0.5`, encoded over `Nat` as `2·|LCS| ≥ max |old| |new|`. -/
def similar (a b : List Word) : Bool := decide (2 * lcs a b ≥ max a.length b.length)

/-- The alignment decision: similar enough ⇒ `edited` (key inherited), else `inserted`. -/
def classify (old new : List Word) : Match :=
  if similar old new then .edited else .inserted

/-- **Identical text is an edit, not insert+remove** — the reflexive base of alignment. -/
theorem classify_self (a : List Word) : classify a a = .edited := by
  have h : similar a a = true := by
    simp only [similar, lcs_self, Nat.max_self, decide_eq_true_eq]
    omega
  simp only [classify, h, if_true]

/-! ### Grounding in the fixture

A one-word edit in a nine-word block reads as `Edited` (LCS 8 of 9 ≥ 0.5); a genuine
replacement reads as `Inserted` (LCS 0). -/

/-- "small edit is Edited": `... jumps over the lazy dog` → `... jumps over the sleepy dog`
(one word differs of nine). -/
example : classify [1,2,3,4,5,6,7,8,9] [1,2,3,4,5,6,7,10,9] = .edited := by native_decide

/-- "genuine insert": unrelated replacement text has LCS 0 ⇒ `Inserted`. -/
example : classify [1,2] [3,4,5,6,7] = .inserted := by native_decide

end LazilyFormal.StableId
