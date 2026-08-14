/-
The paper's parenthetical in Lemma 5.1, as monoid theory: both generators of a two-generated
non-cyclic `ℵ₀`-monoid lie in any divisor-closed generating subset.
-/
import KappaMonoid.TwoGen.Forms

universe u v

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

variable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]

/-! ## Lemma 5.1

If `H ≅ V^{ℵ₀}(R)` for a ring whose projectives are direct sums of finitely generated modules,
then `x₁` and `x₂` are classes of finitely generated modules, `H` is braided over `add (x₁ + x₂)`,
and `V(R) ≅ add (x₁ + x₂) = ⟨x₁, x₂⟩`. -/

/-- **The paper's parenthetical, isolated.**

If a *divisor-closed* subset `S` generates `H` as an `ℵ₀`-monoid and `H` is not cyclic, then both
generators lie in `S`.  Otherwise, say `x₁ ∉ S`: every `y ∈ S` has a form (`exists_form`) whose
`X₁`-coefficient must vanish — else `x₁ ≼ y` would put `x₁` in `S` — so `S ⊆ ⟨x₂⟩` and
`H = ⟨S⟩ = ⟨x₂⟩` is cyclic.

Lemma 5.1 uses it with `S = e⁻¹(V(R))`, and the hereditary half of Proposition 5.4 with
`S = V(R)` itself, to see that the two generators are finitely generated. -/
theorem mem_of_divisorClosed_of_generates (x₁ x₂ : H) {S : Set H}
    (hSsat : ∀ a ∈ S, ∀ b c : H, a = b + c → b ∈ S)
    (hSgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) S)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x} : Set H)) :
    x₁ ∈ S ∧ x₂ ∈ S := by
  have key : ∀ a b : H, KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({a, b} : Set H) → a ∈ S := by
    intro a b hab
    by_contra haS
    -- otherwise every element of `S` is a multiple of `b` alone
    have hsub : S ⊆ KMonoid.kclosure (ℵ₀ : Cardinal.{u}) ({b} : Set H) := by
      intro y hy
      obtain ⟨F, hF⟩ := exists_form a b hab y
      have hα : F.1 = 0 := by
        by_contra hne
        obtain ⟨c, hc⟩ := self_addLe_ecmul hne a
        exact haS (hSsat y hy a (c + ecmul F.2 b)
          (by rw [← hF, eval, ← hc, add_assoc]))
      rw [← hF, eval, hα, ecmul_zero, zero_add]
      exact IsKSubmonoid.ecmul_mem
        (S := KMonoid.kclosure (ℵ₀ : Cardinal.{u}) ({b} : Set H))
        (KMonoid.isKSubmonoid_kclosure _ _) (KMonoid.subset_kclosure rfl) F.2
    refine hnoncyclic b (Set.eq_univ_of_univ_subset ?_)
    rw [← hSgen]
    exact KMonoid.kclosure_le hsub (KMonoid.isKSubmonoid_kclosure _ _)
  exact ⟨key x₁ x₂ hgen, key x₂ x₁ (by rwa [Set.pair_comm])⟩

end TwoGen

end KappaMonoid
