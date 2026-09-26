/-
**The shape of the Bergman–Dicks realisation theorem.**

`BergmanDicksData k M u` packages a hereditary `k`-algebra whose monoid of finitely generated
projective (left) modules is `M`, with `[R] ↦ u`.  It used to be the conclusion of the one axiom
of the development; it is now produced by `Bergman.realization` (`Bergman/Realization.lean`).
-/
import Mathlib.RingTheory.Finiteness.Defs
import KappaMonoid.ForMathlib.Hereditary

universe u

namespace KappaMonoid

/-- A hereditary `k`-algebra realising a given reduced commutative monoid `M` as its monoid of
finitely generated projective modules.

`P a` is the module realising `a ∈ M`; the four conditions `iso_zero`, `iso_add`, `inj` and
`surj` say exactly that `a ↦ [P a]` is a monoid isomorphism `M ≅ V(R)`, and `iso_unit` says that
it carries the given order-unit `u` to the class of `R` itself. -/
structure BergmanDicksData (k : Type u) [Field k] (M : Type u) [AddCommMonoid M] (u : M) where
  /-- The realising algebra. -/
  R : Type u
  [ring : Ring R]
  [algebra : Algebra k R]
  /-- `R` is hereditary: every left ideal and every right ideal is projective. -/
  hereditary : IsHereditary R
  /-- The finitely generated projective module realising `a ∈ M`. -/
  P : M → Type u
  [addCommGroup : ∀ a, AddCommGroup (P a)]
  [module : ∀ a, Module R (P a)]
  proj : ∀ a, Module.Projective R (P a)
  fin : ∀ a, Module.Finite R (P a)
  /-- `P 0 = 0`. -/
  iso_zero : Subsingleton (P 0)
  /-- `P (a + b) ≅ P a ⊕ P b`. -/
  iso_add : ∀ a b, Nonempty (P (a + b) ≃ₗ[R] P a × P b)
  /-- `a ↦ [P a]` is injective. -/
  inj : ∀ a b, Nonempty (P a ≃ₗ[R] P b) → a = b
  /-- `a ↦ [P a]` is onto the finitely generated projectives. -/
  surj : ∀ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q), Module.Projective R Q →
    Module.Finite R Q → ∃ a, Nonempty (Q ≃ₗ[R] P a)
  /-- The order-unit is the class of the ring itself: `[R] = u`. -/
  iso_unit : Nonempty (P u ≃ₗ[R] R)

attribute [instance] BergmanDicksData.ring BergmanDicksData.algebra
  BergmanDicksData.addCommGroup BergmanDicksData.module

end KappaMonoid
