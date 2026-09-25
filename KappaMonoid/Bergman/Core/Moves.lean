/-
**Basic transfers and transvections, as changes of standard presentation** (Bergman §1, §6).

The `C`-module `M` stays fixed; each move replaces its standard presentation by another one,
related by one `StdPres.Step`, and records how the images of the components change.

* `StdPres.transfer_some`: `A l = ker φ ⊕ R_l a` with `φ : A l → R_l e_j`, `φ a = e_j`; the summand
  `R_l a` is moved to `A none` as `k^ι a` (Bergman's case `(a_λ)` of §6).
* `StdPres.transfer_none`: the same from `A none` to `A l` (case `(a_0)`).
* `StdPres.transvection`: `θ = id - (m ↦ ε(m) x)` for a functional `ε` supported on `A μ₁` with
  `ε x = 0` (case `(b)`); the new presentation is `θ ∘ j` on `μ₁`.
-/
import KappaMonoid.Bergman.Core.Pres

universe u

set_option linter.unusedSectionVars false

namespace Bergman.Core

open Module

variable {k : Type u} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  {σ : ∀ l, (ι → k) →ₐ[k] R l} [Fact (∀ l, Function.Injective (σ l))]
  {C : Type u} [Ring C] [Algebra k C] {σC : (ι → k) →ₐ[k] C} {inc : ∀ l, R l →ₐ[k] C}
  [Fact (IsCoprod k σ C σC inc)]
  {M : Type u} [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]

/-- The functional `ε : M → C` extending `incμ ∘ e` on `A μ₁` and `0` on the other components. -/
theorem StdPres.exists_functional (p : StdPres σ σC inc M) (μ₁ : Option Λ)
    (e : p.A μ₁ →ₗ[Rμ k ι R μ₁] Rμ k ι R μ₁) :
    ∃ ε : M →ₗ[C] C, (∀ b, ε (p.j μ₁ b) = incμ σC inc μ₁ (e b)) ∧
      ∀ μ ≠ μ₁, ∀ b, ε (p.j μ b) = 0 := sorry

/-- **Basic transfer from `A l` to `A none`.** -/
theorem StdPres.transfer_some (p : StdPres σ σC inc M) (l : Λ) (j : ι)
    (φ : p.A (some l) →ₗ[Rμ k ι R (some l)] lid σ (some l) j) (a : p.A (some l))
    (ha : (φ a : Rμ k ι R (some l)) = eμ σ (some l) j) (hja : eμ σ (some l) j • a = a) :
    ∃ p' : StdPres σ σC inc M, p.Step p' ∧ (p.FG → p'.FG) ∧
      (∀ μ, μ ≠ none → μ ≠ some l → Set.range (p'.j μ) = Set.range (p.j μ)) ∧
      Set.range (p'.j (some l)) = p.j (some l) '' {x | φ x = 0} ∧
      Set.range (p'.j none) =
        {m | ∃ (x : p.A none) (c : ι → k), m = p.j none x + σC c • p.j (some l) a} := sorry

/-- **Basic transfer from `A none` to `A l`.** -/
theorem StdPres.transfer_none (p : StdPres σ σC inc M) (l : Λ) (j : ι)
    (ψ : p.A none →ₗ[Rμ k ι R none] lid σ none j) (a : p.A none)
    (ha : (ψ a : Rμ k ι R none) = eμ σ none j) (hja : eμ σ none j • a = a) :
    ∃ p' : StdPres σ σC inc M, p.Step p' ∧ (p.FG → p'.FG) ∧
      (∀ μ, μ ≠ none → μ ≠ some l → Set.range (p'.j μ) = Set.range (p.j μ)) ∧
      Set.range (p'.j none) = p.j none '' {x | ψ x = 0} ∧
      Set.range (p'.j (some l)) =
        {m | ∃ (x : p.A (some l)) (r : R l), m = p.j (some l) x + inc l r • p.j none a} := sorry

/-- **Transvection.** -/
theorem StdPres.transvection (p : StdPres σ σC inc M) (μ₁ : Option Λ) (ε : M →ₗ[C] C)
    (hε : ∀ μ ≠ μ₁, ∀ b, ε (p.j μ b) = 0) (x : M) (hx : ε x = 0) :
    ∃ p' : StdPres σ σC inc M, p.Step p' ∧ (p.FG → p'.FG) ∧
      (∀ μ ≠ μ₁, Set.range (p'.j μ) = Set.range (p.j μ)) ∧
      Set.range (p'.j μ₁) = {m | ∃ b, m = p.j μ₁ b - ε (p.j μ₁ b) • x} := sorry

end Bergman.Core
