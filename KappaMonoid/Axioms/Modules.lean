/-
**A5** the Bergman-Dicks realisation theorem and **A6** Kaplansky's theorem.

A3 — uniqueness of the multiplicities of simple modules — was here until it was proved, in
`ForMathlib/SimpleMultiplicity.lean`.
-/
import Mathlib

universe u

open Cardinal DirectSum

namespace KappaMonoid


/-! ## A5: the Bergman–Dicks realisation theorem -/

/-- A hereditary `k`-algebra realising a given reduced commutative monoid `M` as its monoid of
finitely generated projective modules.

`P a` is the module realising `a ∈ M`; the four conditions `iso_zero`, `iso_add`, `inj` and
`surj` say exactly that `a ↦ [P a]` is a monoid isomorphism `M ≅ V(R)`. -/
structure BergmanDicksData (k : Type u) [Field k] (M : Type u) [AddCommMonoid M] where
  /-- The realising algebra. -/
  R : Type u
  [ring : Ring R]
  [algebra : Algebra k R]
  /-- `R` is hereditary: every left ideal is projective. -/
  hereditary : ∀ I : Ideal R, Module.Projective R I
  /-- Every projective `R`-module is a direct sum of finitely generated ones.
  This is Corollary 4.6 for hereditary rings, and is bundled here because it too is a quoted
  result (Albrecht 1961; Bergman 1972) with no counterpart in Mathlib.  Its shape matches the
  hypothesis of `corollary_4_5_three` verbatim, so it plugs straight in. -/
  sumOfFG : ∀ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q), Module.Projective R Q →
    ∃ (ι : Type u) (S : ι → Type u) (_ : ∀ i, AddCommGroup (S i)) (_ : ∀ i, Module R (S i)),
      (∀ i, Module.Projective R (S i)) ∧ (∀ i, Module.Finite R (S i)) ∧
        Nonempty (Q ≃ₗ[R] ⨁ i, S i)
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

attribute [instance] BergmanDicksData.ring BergmanDicksData.algebra
  BergmanDicksData.addCommGroup BergmanDicksData.module

/-- **Assumed** (Bergman 1974; Bergman–Dicks 1978).  For every field `k`, every reduced
commutative monoid with an order-unit is `V(R)` for a hereditary `k`-algebra `R`.

*Reduced* is the paper's term for conical: `a + b = 0` forces `a = 0`.  An *order-unit* is a `u`
such that every element divides some multiple of `u`.

The proof is a construction by universal localisation and is far out of reach here; Mathlib has
neither hereditary rings nor universal localisation.  The statement bundles the realisation
theorem with the hereditary case of Corollary 4.6 — see `BergmanDicksData.sumOfFG` — because both
are quoted results and Corollary 4.7(1) uses them together. -/
axiom bergmanDicksData (k : Type u) [Field k] (M : Type u) [AddCommMonoid M]
    (_hred : ∀ a b : M, a + b = 0 → a = 0)
    (_hunit : ∃ u : M, ∀ y : M, ∃ (z : M) (n : ℕ), y + z = n • u) :
    BergmanDicksData.{u} k M

/-! ## A6: Kaplansky's theorem -/

/-- **Assumed** (Kaplansky's theorem, [Kaplansky58]): every projective module is a direct sum of
countably generated projective modules.

Standard proof, not formalised here: `P ⊕ Q` is free on a basis `B`, and one builds a
transfinite filtration of `B` by subsets whose spans are compatible with the decomposition —
starting from any element, alternately close up under the supports of the `P`- and `Q`-components
until the process stabilises after countably many steps.  Each step adds a countably generated
summand, and `P` is the direct sum of the `P`-parts of the successive quotients.

Used by `kaplansky`, the `κ`-monoid form: `V^κ(R)` is generated as a `κ`-monoid by the countably
generated projectives. -/
axiom kaplansky_classical {R : Type u} [Ring R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Projective R P] :
    ∃ (ι : Type u) (Q : ι → Type u) (_ : ∀ i, AddCommGroup (Q i)) (_ : ∀ i, Module R (Q i)),
      (∀ i, Module.Projective R (Q i)) ∧
        (∀ i, ∃ s : Set (Q i), #s ≤ ℵ₀ ∧ Submodule.span R s = ⊤) ∧
          Nonempty (P ≃ₗ[R] ⨁ i, Q i)

end KappaMonoid
