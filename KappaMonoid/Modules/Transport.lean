/-
§4 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*,

the remarks around Corollaries 4.5 and 4.6 that turn "universal extension of" into "determines".

* **Example 4.2**, the countable case: countably generated modules are `ℵ₁⁻`-small, equivalently
  `ℵ₀`-small (`isLambdaSmall_succ_aleph0_of_countable`, `isLambdaSmall_succ_iff`).
* **`V^{ℵ₀}(R)` determines `V^κ(R)`** (after Corollary 4.5): an isomorphism of the `ℵ₁⁻`-monoids
  of countably generated projectives of two rings gives a `κ`-isomorphism `V^κ(R) ≅ V^κ(S)`
  (`exists_kIso_of_aleph1Iso`).
* **`V(R)` determines `V^κ(R)`** (before Corollary 4.6) when every projective is a direct sum of
  finitely generated ones: `exists_kIso_of_fgIso`, and its one-sided form
  `exists_kIso_of_fgIso_univ` against any universal `κ`-extension of a monoid isomorphic to
  `V(R)` — the form Examples 4.8(3) uses.
* **Corollary 4.6**, the hereditary case, which the development proves rather than quotes:
  over a left hereditary ring `V^κ(R)` is the universal `κ`-extension of `V(R)`
  (`corollary_4_6_hereditary`).

All of it is Corollary 4.5 plus the monoid-theoretic `exists_kIso_of_base_iso` of
`Braiding/BaseIso.lean`; no axiom is involved.
-/
import KappaMonoid.Modules.Corollary47
import KappaMonoid.Braiding.BaseIso

universe u v w t

open Cardinal Order

namespace KappaMonoid

/-! ## Example 4.2: countably generated modules -/

section Countable

variable (R : Type u) [Ring R] {M : Type u} [AddCommGroup M] [Module R M]

/-- **Example 4.2(1)**, the converse of `IsLambdaSmallLe.isLambdaSmall_succ`: a
`(λ⁺)⁻`-small module is `λ`-small, since `#s < λ⁺ ↔ #s ≤ λ`. -/
theorem IsLambdaSmall.isLambdaSmallLe_of_succ {lam : Cardinal.{u}}
    (h : IsLambdaSmall R (Order.succ lam) M) : IsLambdaSmallLe R lam M := by
  intro ι N _ _ f
  obtain ⟨s, hs, hzero⟩ := h N ‹_› ‹_› f
  exact ⟨s, Order.lt_succ_iff.mp hs, hzero⟩

/-- **Example 4.2(1)**: `λ`-small and `(λ⁺)⁻`-small are the same condition, for every `λ`. -/
theorem isLambdaSmall_succ_iff {lam : Cardinal.{u}} :
    IsLambdaSmall R (Order.succ lam) M ↔ IsLambdaSmallLe R lam M :=
  ⟨IsLambdaSmall.isLambdaSmallLe_of_succ R, IsLambdaSmallLe.isLambdaSmall_succ R⟩

/-- A module is `<ℵ₁`-generated exactly when it is countably generated. -/
theorem isLambdaGenerated_aleph1_iff :
    IsLambdaGenerated R ℵ₁ M ↔ ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤ := by
  simp only [IsLambdaGenerated, ← Cardinal.succ_aleph0, Order.lt_succ_iff,
    Cardinal.le_aleph0_iff_set_countable]

/-- **Example 4.2**: *"Countably generated modules are `ℵ₁⁻`-small (equivalently,
`ℵ₀`-small)."*  The `ℵ₁⁻` half, with `ℵ₁` written `ℵ₀⁺`; this is Example 4.2(2) at `λ = ℵ₀⁺`. -/
theorem isLambdaSmall_succ_aleph0_of_countable (s : Set M) (hs : s.Countable)
    (hspan : Submodule.span R s = ⊤) : IsLambdaSmall R (Order.succ ℵ₀) M :=
  isLambdaSmall_of_span R (Order.le_succ ℵ₀) M s
    (Order.lt_succ_iff.mpr (Cardinal.le_aleph0_iff_set_countable.mpr hs)) hspan

/-- **Example 4.2**, with `ℵ₁` written as such. -/
theorem isLambdaSmall_aleph1_of_countable (s : Set M) (hs : s.Countable)
    (hspan : Submodule.span R s = ⊤) : IsLambdaSmall R ℵ₁ M :=
  Cardinal.succ_aleph0 ▸ isLambdaSmall_succ_aleph0_of_countable R s hs hspan

/-- **Example 4.2**, the parenthetical: countably generated modules are `ℵ₀`-small. -/
theorem isLambdaSmallLe_aleph0_of_countable (s : Set M) (hs : s.Countable)
    (hspan : Submodule.span R s = ⊤) : IsLambdaSmallLe R ℵ₀ M :=
  IsLambdaSmall.isLambdaSmallLe_of_succ R (isLambdaSmall_succ_aleph0_of_countable R s hs hspan)

end Countable

/-! ## `V^{ℵ₀}(R)` and `V(R)` determine `V^κ(R)` -/

section Determines

variable {κ : Cardinal.{u}}

/-- **`V^{ℵ₀}(R)` determines `V^κ(R)`** (the remark after Corollary 4.5): for rings `R` and `S`,
an isomorphism of the `ℵ₁⁻`-monoids of countably generated projective modules extends to a
`κ`-isomorphism `V^κ(R) ≅ V^κ(S)`, for every infinite `κ`.

`V^{ℵ₀}(R)` is `(projClass R κ hκ).lambdaGenPart ℵ₁`, as in `corollary_4_7_two_iff`, and an
isomorphism of `ℵ₀`-monoids is one of `ℵ₁⁻`-monoids since `ℵ₁ = ℵ₀⁺`.  Both `V^κ(R)` and `V^κ(S)`
are `ℵ₁⁻`-braided over them (Corollary 4.5(2)), and isomorphic bases have isomorphic braided
extensions. -/
theorem exists_kIso_of_aleph1Iso (hκ : ℵ₀ ≤ κ) (R S : Type u) [Ring R] [Ring S]
    (φ : ↥((projClass R κ hκ).lambdaGenPart ℵ₁) → ↥((projClass S κ hκ).lambdaGenPart ℵ₁))
    (hφ : IsLMonoidHom ℵ₁ φ)
    (hbij : Function.Bijective φ) :
    ∃ e : (projClass R κ hκ).carrier → (projClass S κ hκ).carrier, KMonoid.IsKHom κ e ∧
      (∀ a : ↥((projClass R κ hκ).lambdaGenPart ℵ₁),
        e (a : (projClass R κ hκ).carrier) = (φ a : (projClass S κ hκ).carrier)) ∧
        Function.Bijective e := by
  exact IsBraidedOver.exists_kIso_of_base_iso (aleph_one_le_succ κ hκ)
    (corollary_4_5_two.{u, u} R κ hκ).1 (corollary_4_5_two.{u, u} S κ hκ).1 φ hφ hbij

/-- **`V(R)` determines `V^κ(R)`**, one-sided (the remark before Corollary 4.6): if every
projective `R`-module is a direct sum of finitely generated ones, and `H` is the universal
`κ`-extension of a monoid `X ≅ V(R)`, then `V^κ(R) ≅ H` as `κ`-monoids, compatibly with the
isomorphism of bases.

This is the form Examples 4.8(3) uses, with `H` one of the universal extensions computed in §3.
`H` and `X` may live in any universe — `ℕ₀ ∪ {∞}` is in `Type 0`, `H + ℵ₀H ⊆ F_{ℵ₀}^n` in
`Type (u+1)` — which is why the universal property of `H` is asked for at two test universes; a
braiding supplies both. -/
theorem exists_kIso_of_fgIso_univ (hκ : ℵ₀ ≤ κ) (R : Type u) [Ring R]
    (hfg : EveryProjectiveIsSumOfFG R) {X : Type v} {H : Type w} [LMonoid ℵ₀ X] [KMonoid κ H]
    {f : X → H}
    (hH : IsUniversalKExtension.{u, v, w, u} ℵ₀ κ X H (le_succ_of_le hκ) f)
    (hH' : IsUniversalKExtension.{u, v, w, w} ℵ₀ κ X H (le_succ_of_le hκ) f)
    (φ : ↥((projClass R κ hκ).lambdaGenPart ℵ₀) → X)
    (hφ : IsLMonoidHom ℵ₀ φ)
    (hbij : Function.Bijective φ) :
    ∃ e : (projClass R κ hκ).carrier → H,
      KMonoid.IsKHom κ e ∧ (∀ a : ↥((projClass R κ hκ).lambdaGenPart ℵ₀),
        e (a : (projClass R κ hκ).carrier) = f (φ a)) ∧
        Function.Bijective e := by
  have hbr := (corollary_4_5_three.{u, u} R κ hκ hfg).1
  exact IsUniversalKExtension.exists_kIso_of_base_iso (le_succ_of_le hκ)
    (hbr.isUniversalKExtension (le_succ_of_le hκ)) (hbr.isUniversalKExtension (le_succ_of_le hκ))
    hH hH' φ hφ hbij

/-- **`V(R)` determines `V^κ(R)`** (the remark before Corollary 4.6): for rings `R` and `S` over
which every projective module is a direct sum of finitely generated ones, an isomorphism
`V(R) ≅ V(S)` of monoids of finitely generated projectives extends to a `κ`-isomorphism
`V^κ(R) ≅ V^κ(S)`, for every infinite `κ`.

`V(R)` is `(projClass R κ hκ).lambdaGenPart ℵ₀` with its `ℵ₀⁻`-monoid structure, which is its
monoid structure (`isLMonoidHom_aleph0_of_add`); both sides are braided over it by Corollary
4.5(3). -/
theorem exists_kIso_of_fgIso (hκ : ℵ₀ ≤ κ) (R S : Type u) [Ring R] [Ring S]
    (hfgR : EveryProjectiveIsSumOfFG R) (hfgS : EveryProjectiveIsSumOfFG S)
    (φ : ↥((projClass R κ hκ).lambdaGenPart ℵ₀) → ↥((projClass S κ hκ).lambdaGenPart ℵ₀))
    (hφ : IsLMonoidHom ℵ₀ φ)
    (hbij : Function.Bijective φ) :
    ∃ e : (projClass R κ hκ).carrier → (projClass S κ hκ).carrier, KMonoid.IsKHom κ e ∧
      (∀ a : ↥((projClass R κ hκ).lambdaGenPart ℵ₀),
        e (a : (projClass R κ hκ).carrier) = (φ a : (projClass S κ hκ).carrier)) ∧
        Function.Bijective e := by
  exact IsBraidedOver.exists_kIso_of_base_iso (le_succ_of_le hκ)
    (corollary_4_5_three.{u, u} R κ hκ hfgR).1 (corollary_4_5_three.{u, u} S κ hκ hfgS).1
    φ hφ hbij

/-- **Corollary 4.6(2)**, the hereditary special case: over a left hereditary ring `V^κ(R)` is
`ℵ₀⁻`-braided over, and the universal `κ`-extension of, the monoid `V(R)` of finitely generated
projective modules.

The paper's Corollary 4.6 quotes six classes of rings from the literature, and the development
records it among the omissions; the hereditary case — Albrecht's theorem, the paper's source for
(2) at its origin — is the one proved here (`Albrecht.exists_directSum_fg`), which is all
Corollary 4.7(1) needs.  The modules are left modules, so the paper's right hereditary is
`IsLeftHereditary`. -/
theorem corollary_4_6_hereditary (R : Type u) [Ring R] [IsLeftHereditary R] (hκ : ℵ₀ ≤ κ) :
    IsBraidedOver ℵ₀ κ ((projClass R κ hκ).lambdaGenPart ℵ₀)
        (projClass R κ hκ).carrier (le_succ_of_le hκ) (fun a => (a : (projClass R κ hκ).carrier)) ∧
      IsUniversalKExtension.{u, u, u, t} ℵ₀ κ ((projClass R κ hκ).lambdaGenPart ℵ₀)
        (projClass R κ hκ).carrier (le_succ_of_le hκ)
        (fun a => (a : (projClass R κ hκ).carrier)) :=
  corollary_4_5_three R κ hκ Albrecht.exists_directSum_fg

end Determines

end KappaMonoid
