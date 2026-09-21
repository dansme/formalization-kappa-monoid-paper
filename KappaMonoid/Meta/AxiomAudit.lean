/-
`#assert_axioms`: the axiom provenance of a result, as a checked claim rather than a comment.

CI already refuses a change to the *set* of `axiom` declarations under `KappaMonoid/`.  It says
nothing about who depends on them, so a proof that quietly starts using Bergman–Dicks passes.
`README.md` carries that information as prose, which is exactly the kind of claim that goes stale.

    #assert_axioms KappaMonoid.theorem_3_12 []
    #assert_axioms KappaMonoid.prop_2_16 [bergmanDicksData]

`propext`, `Classical.choice` and `Quot.sound` are always permitted and never listed; everything
else must be declared, and a mismatch in either direction is an error.  The point of failing on a
*missing* axiom too is that the claim stays honest when a proof changes: if a result stops needing
an axiom, the assertion says so and the table gets fixed.
-/
import Lean

namespace KappaMonoid.Meta

open Lean Elab Command

/-- The three axioms of Lean's own foundation, permitted everywhere and never listed. -/
private def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_axioms foo [a, b]` fails unless the axioms `foo` depends on, other than `propext`,
`Classical.choice` and `Quot.sound`, are exactly `a` and `b`. -/
syntax (name := assertAxiomsCmd) "#assert_axioms " ident " [" ident,* "] " : command

@[command_elab assertAxiomsCmd]
def elabAssertAxioms : CommandElab := fun stx => do
  match stx with
  | `(command| #assert_axioms $c:ident [$as:ident,*]) => do
    let cname ← liftCoreM <| realizeGlobalConstNoOverload c
    let expected ← as.getElems.mapM fun a => liftCoreM <| realizeGlobalConstNoOverload a
    let found ← liftCoreM <| collectAxioms cname
    let actual := found.filter fun a => !standardAxioms.contains a
    let missing := expected.filter fun a => !actual.contains a
    let unexpected := actual.filter fun a => !expected.contains a
    unless unexpected.isEmpty do
      throwError "{cname} depends on {unexpected.toList}, which is not in its declared list.\n\
        Either the proof changed or the claim is wrong; fix the proof, or update this assertion \
        and the provenance table in README.md together."
    unless missing.isEmpty do
      throwError "{cname} no longer depends on {missing.toList}.\n\
        Good news, presumably — drop it from this assertion and from the provenance table in \
        README.md."
  | _ => throwUnsupportedSyntax

end KappaMonoid.Meta
