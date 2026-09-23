/-
Prints every `axiom` declared in a `KappaMonoid` module, one fully qualified name per line.

CI compares the output with the expected list, so an axiom is caught however it is written —
namespaced, `private`, indented, or produced by a macro — unlike a textual grep of the sources.
Run it after the build: `lake env lean scripts/list_axioms.lean`.
-/
import KappaMonoid

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut names : Array String := #[]
  for (n, ci) in env.constants.toList do
    if let .axiomInfo _ := ci then
      if let some idx := env.getModuleIdxFor? n then
        if (`KappaMonoid).isPrefixOf env.header.moduleNames[idx.toNat]! then
          names := names.push n.toString
  for s in names.qsort (· < ·) do
    IO.println s
