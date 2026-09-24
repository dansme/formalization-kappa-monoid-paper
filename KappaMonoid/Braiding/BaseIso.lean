/-
**Isomorphic bases have isomorphic universal `κ`-extensions**, across universes.

The mechanism behind every "`V^{ℵ₀}(R)` determines `V^κ(R)`" and "`V(R)` determines `V^κ(R)`"
statement of §4 (the remarks after Corollary 4.5, and Examples 4.8(3)): if `X₁ ≅ X₂` as
`λ⁻`-monoids, then their universal `κ`-extensions are isomorphic as `κ`-monoids, compatibly with
the two structure maps.  Transport one extension to the other base (`of_base_iso`) and compare
the two extensions of the same base (`isUniversalKExtension_unique'`).

Everything is universe-polymorphic in both bases and both extensions, because the applications
compare a module-theoretic extension in `Type u` with a concrete one in `Type 0` (`ℕ₀ ∪ {∞}`,
`ℝ≥0 ∪ ℝ̃>0 ∪ {∞}`) or in `Type (u+1)` (`H + ℵ₀H ⊆ F_{ℵ₀}^n`).
-/
import KappaMonoid.Braiding.Prop310

universe u v w z t

open Cardinal

namespace KappaMonoid

open KMonoid LMonoid

variable {lam κ : Cardinal.{u}}

/-- **Isomorphic bases have isomorphic universal `κ`-extensions.**  If `H₁` is the universal
`κ`-extension of `X₁`, `H₂` that of `X₂`, and `φ : X₁ → X₂` is an isomorphism of `λ⁻`-monoids,
then there is a `κ`-isomorphism `e : H₁ → H₂` with `e ∘ f₁ = f₂ ∘ φ`.

Each universal property is asked for at both test universes, `w` and `t`, which is what
`isUniversalKExtension_unique'` needs to compare extensions living in different universes; a
braiding supplies both (`IsBraidedOver.exists_kIso_of_base_iso`). -/
theorem IsUniversalKExtension.exists_kIso_of_base_iso {X₁ : Type v} {X₂ : Type z} {H₁ : Type w}
    {H₂ : Type t} [LMonoid lam X₁] [LMonoid lam X₂] [KMonoid κ H₁] [KMonoid κ H₂]
    (hlk : lam ≤ Order.succ κ) {f₁ : X₁ → H₁} {f₂ : X₂ → H₂}
    (h₁ : IsUniversalKExtension.{u, v, w, t} lam κ X₁ H₁ hlk f₁)
    (h₁' : IsUniversalKExtension.{u, v, w, w} lam κ X₁ H₁ hlk f₁)
    (h₂ : IsUniversalKExtension.{u, z, t, w} lam κ X₂ H₂ hlk f₂)
    (h₂' : IsUniversalKExtension.{u, z, t, t} lam κ X₂ H₂ hlk f₂)
    (φ : X₁ → X₂) (hφ : IsLMonoidHom lam φ) (hbij : Function.Bijective φ) :
    ∃ e : H₁ → H₂, IsKHom κ e ∧ (∀ x, e (f₁ x) = f₂ (φ x)) ∧ Function.Bijective e := by
  set Φ := Equiv.ofBijective φ hbij with hΦ
  have hψ : IsLMonoidHom lam Φ.symm :=
    hφ.inv (fun a => Φ.symm_apply_apply a) (fun b => Φ.apply_symm_apply b)
  -- move `H₂` to the base `X₁`
  have k₂ : IsUniversalKExtension.{u, v, t, w} lam κ X₁ H₂ hlk (fun x => f₂ (φ x)) :=
    h₂.of_base_iso hlk φ Φ.symm hφ hψ (fun a => Φ.symm_apply_apply a)
      (fun b => Φ.apply_symm_apply b)
  have k₂' : IsUniversalKExtension.{u, v, t, t} lam κ X₁ H₂ hlk (fun x => f₂ (φ x)) :=
    h₂'.of_base_iso hlk φ Φ.symm hφ hψ (fun a => Φ.symm_apply_apply a)
      (fun b => Φ.apply_symm_apply b)
  obtain ⟨e, ⟨he, hcomm, hebij⟩, -⟩ := isUniversalKExtension_unique' hlk h₁ h₁' k₂ k₂'
  exact ⟨e, he, hcomm, hebij⟩

/-- **Isomorphic bases have isomorphic braided extensions**: two `κ`-monoids `λ⁻`-braided over
isomorphic `λ⁻`-monoids are `κ`-isomorphic, compatibly with the structure maps.  A braiding makes
an extension universal at every test universe (Theorem 3.12(2)), so this is
`IsUniversalKExtension.exists_kIso_of_base_iso`. -/
theorem IsBraidedOver.exists_kIso_of_base_iso {X₁ : Type v} {X₂ : Type z} {H₁ : Type w}
    {H₂ : Type t} [LMonoid lam X₁] [LMonoid lam X₂] [KMonoid κ H₁] [KMonoid κ H₂]
    (hlk : lam ≤ Order.succ κ) {f₁ : X₁ → H₁} {f₂ : X₂ → H₂}
    (hbr₁ : IsBraidedOver lam κ X₁ H₁ hlk f₁) (hbr₂ : IsBraidedOver lam κ X₂ H₂ hlk f₂)
    (φ : X₁ → X₂) (hφ : IsLMonoidHom lam φ) (hbij : Function.Bijective φ) :
    ∃ e : H₁ → H₂, IsKHom κ e ∧ (∀ x, e (f₁ x) = f₂ (φ x)) ∧ Function.Bijective e :=
  IsUniversalKExtension.exists_kIso_of_base_iso hlk (hbr₁.isUniversalKExtension hlk)
    (hbr₁.isUniversalKExtension hlk) (hbr₂.isUniversalKExtension hlk)
    (hbr₂.isUniversalKExtension hlk) φ hφ hbij

end KappaMonoid
