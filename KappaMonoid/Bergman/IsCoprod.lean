/-
**Coproducts of `k^ι`-rings, as a universal property.**

`IsCoprod σ σC inc` says that `C` is the coproduct (pushout) of the `k^ι`-rings `R l`
(`σ l : k^ι → R l`) in the category of `k`-algebras under `k^ι`.  No construction is needed: in
the applications `C` is a matrix ring over a presented algebra, shown to have the universal
property directly (`Bergman/Morita.lean`).
-/
import Mathlib

universe u

namespace Bergman

variable (k : Type u) [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]

/-- `C`, with `inc l : R l → C` and `σC : k^ι → C`, is the coproduct of the `k^ι`-rings
`σ l : k^ι → R l`. -/
structure IsCoprod (σ : ∀ l, (ι → k) →ₐ[k] R l) (C : Type u) [Ring C] [Algebra k C]
    (σC : (ι → k) →ₐ[k] C) (inc : ∀ l, R l →ₐ[k] C) : Prop where
  comm : ∀ l, (inc l).comp (σ l) = σC
  lift : ∀ (T : Type u) [Ring T] [Algebra k T] (f₀ : (ι → k) →ₐ[k] T) (f : ∀ l, R l →ₐ[k] T),
    (∀ l, (f l).comp (σ l) = f₀) → ∃ g : C →ₐ[k] T, g.comp σC = f₀ ∧ ∀ l, g.comp (inc l) = f l
  ext : ∀ (T : Type u) [Ring T] [Algebra k T] (g g' : C →ₐ[k] T), g.comp σC = g'.comp σC →
    (∀ l, g.comp (inc l) = g'.comp (inc l)) → g = g'

end Bergman
