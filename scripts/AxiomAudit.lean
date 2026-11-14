/-
Axiom audit for lazily-formal (`make proof-hygiene`).

Every declaration in a `LazilyFormal` module may depend only on Lean's three
standard axioms. This rejects an open proof (`sorryAx`, from `sorry`/`admit`),
a compiler-trusted proof (`Lean.ofReduceBool`, from `native_decide`), and any
locally declared axiom — independently of whether the build was cached.
-/
import Lean
import LazilyFormal

open Lean Elab Command

elab "#audit_lazily_formal_axioms" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut bad : Array MessageData := #[]
  for (name, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some modName := env.header.moduleNames[idx.toNat]? | continue
    unless (`LazilyFormal).isPrefixOf modName do continue
    checked := checked + 1
    let axioms ← liftCoreM <| collectAxioms name
    let extra := axioms.filter (fun a => !allowed.contains a)
    unless extra.isEmpty do
      bad := bad.push m!"{name} ({modName}) depends on {extra.toList}"
  if checked == 0 then
    throwError "axiom audit checked no LazilyFormal declarations; the audit is vacuous"
  unless bad.isEmpty do
    throwError m!"forbidden axioms:\n{MessageData.joinSep bad.toList "\n"}"
  logInfo m!"axiom audit ok: {checked} LazilyFormal declarations use only propext, Classical.choice, Quot.sound"

#audit_lazily_formal_axioms
