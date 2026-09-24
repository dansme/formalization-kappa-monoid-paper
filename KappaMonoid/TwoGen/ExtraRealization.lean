/-
**Section 5, unnumbered claims — the realisation statements.**

* **The remark before Corollary 5.5** (`kappa_monoids.tex:2237–2240`): if `H ≅ V^{ℵ₀}(R)` for a
  ring over which every projective module is a direct sum of finitely generated ones, then for
  every field `k` also `H ≅ V^{ℵ₀}(S)` for a hereditary `k`-algebra `S` (`remark_before_5_5`).
  This rests on the Bergman–Dicks realisation theorem, through Corollary 4.7(1).

* **The §5 preamble** (`kappa_monoids.tex:1989–1992`): a cyclic `ℵ₀`-monoid `⟨x⟩` is
  `V^{ℵ₀}(R)` for a nonzero hereditary ring `R` iff `ℵ₀ x ≠ n x` for every `n ∈ ℕ₀`
  (`cyclic_realizable_iff`), equivalently iff it is `C ∪ {∞}` for a nonzero cyclic monoid `C`
  (`cyclic_realizable_iff_withTop`).  The monoid theory behind it is in `TwoGen/Extra.lean`.
-/
import KappaMonoid.TwoGen.Extra
import KappaMonoid.TwoGen.Corollary55

universe u

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

open KMonoid

/-! ## The remark before Corollary 5.5 -/

/-- **The remark before Corollary 5.5** (`kappa_monoids.tex:2237–2240`): *"if
`H ≅ V^{ℵ₀}(R)` for a ring whose projective modules are direct sums of finitely generated
modules, then … `H ≅ V^{ℵ₀}(S)` for a hereditary `k`-algebra `S`, for an arbitrary field `k`."*

Stated, as the paper's argument allows, for an arbitrary `κ`-monoid `H` rather than a
two-generated `ℵ₀`-monoid.

Paper proof: Corollary 4.5(3) makes `V^κ(R)` braided over `V(R) = add [R]`, so `H` is braided
over `add x` for `x` the image of `[R]` (`corollary_4_7_one_backward_iso`), and Corollary 4.7(1)
(`corollary_4_7_one_forward`, the direction resting on Bergman–Dicks) realises such an `H` over a
hereditary `k`-algebra. -/
theorem remark_before_5_5 {κ : Cardinal.{u}} {H : Type u} [KMonoid κ H] (hκ : ℵ₀ ≤ κ)
    (R : Type u) [Ring R] (hfg : EveryProjectiveIsSumOfFG R)
    (e : letI := (projClass R κ hκ).instKMonoid hκ; (projClass R κ hκ).carrier → H)
    (he : letI := (projClass R κ hκ).instKMonoid hκ; KMonoid.IsKHom κ e)
    (hbij : Function.Bijective e) (k : Type u) [Field k] :
    ∃ (S : Type u) (_ : Ring S) (_ : Algebra k S) (_ : IsHereditary S),
      letI := (projClass S κ hκ).instKMonoid hκ
      ∃ e' : (projClass S κ hκ).carrier → H, KMonoid.IsKHom κ e' ∧ Function.Bijective e' := by
  obtain ⟨x, hbr⟩ := corollary_4_7_one_backward_iso R hκ hfg e he hbij
  exact corollary_4_7_one_forward hκ k x hbr

/-- **The remark before Corollary 5.5**, in the terms of §5: a realizable `ℵ₀`-monoid
(`IsRealizableAsV`) is `V^{ℵ₀}(S)` for a hereditary `k`-algebra `S`, for every field `k`. -/
theorem remark_before_5_5_realizable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]
    (h : IsRealizableAsV H) (k : Type u) [Field k] :
    ∃ (S : Type u) (_ : Ring S) (_ : Algebra k S) (_ : IsHereditary S),
      ∃ e : V(S).carrier → H, IsKHom ℵ₀ e ∧ Function.Bijective e := by
  obtain ⟨R, _, hfg, e, he, hbij⟩ := h
  exact remark_before_5_5 le_rfl R hfg e he hbij k

/-! ## The §5 preamble: cyclic `ℵ₀`-monoids -/

section Cyclic

variable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]

/-- **A ring realising a nonzero `ℵ₀`-monoid is nonzero**: over the zero ring every module is
zero, so `V^{ℵ₀}(0) = 0`. -/
theorem nontrivial_of_realization (R : Type u) [Ring R] (e : V(R).carrier → H)
    (he : IsKHom ℵ₀ e) (hbij : Function.Bijective e) {x : H} (hx : x ≠ 0) : Nontrivial R := by
  by_contra hR
  rw [not_nontrivial_iff_subsingleton] at hR
  obtain ⟨p, rfl⟩ := hbij.2 x
  have : Subsingleton (V(R).rep p) := Module.subsingleton R _
  exact hx ((congrArg e (V(R).eq_zero_of_subsingleton this)).trans he.1)

/-- **The §5 preamble, forward half** (`kappa_monoids.tex:1989`), for *any* nonzero ring: if a
cyclic `ℵ₀`-monoid `⟨x⟩` is `V^{ℵ₀}(R)` with `R ≠ 0`, then `ℵ₀ x ≠ n x` for every `n ∈ ℕ₀`.
Hereditariness is not needed.

Paper proof (unwritten): `[R]` is a faithful order-unit of `V^{ℵ₀}(R)` (Example 2.13, which uses
invariance of infinite rank), so its image in `H` is one, and `ne_nsmul_of_isFaithful`
applies. -/
theorem ne_nsmul_of_realization {x : H} (hgen : KGenerates (ℵ₀ : Cardinal.{u}) ({x} : Set H))
    (R : Type u) [Ring R] [Nontrivial R] (e : V(R).carrier → H) (he : IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) (n : ℕ) : ℵ₀∙x ≠ n • x := by
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  have hfaith : IsFaithful (κ := (ℵ₀ : Cardinal.{u})) (Projective.unitClass R ℵ₀ le_rfl k) :=
    Projective.isFaithful_unitClass R ℵ₀ le_rfl k
  exact ne_nsmul_of_isFaithful hgen (isFaithful_map_of_bijective he hbij hfaith) n

/-- **The §5 preamble, backward half** (`kappa_monoids.tex:1989`): if `ℵ₀ x ≠ n x` for every
`n ∈ ℕ₀`, then for every field `k` the cyclic `ℵ₀`-monoid `⟨x⟩` is `V^{ℵ₀}(R)` for a nonzero
hereditary `k`-algebra `R`.

Paper proof (unwritten): `H` is braided over `add x` (`isBraidedOver_addOf_of_ne`), so
Corollary 4.7(1) realises it over a hereditary `k`-algebra; that algebra is nonzero because
`x ≠ 0`. -/
theorem realization_of_ne {x : H} (hgen : KGenerates (ℵ₀ : Cardinal.{u}) ({x} : Set H))
    (hx : ∀ n : ℕ, ℵ₀∙x ≠ n • x) (k : Type u) [Field k] :
    ∃ (R : Type u) (_ : Ring R) (_ : Algebra k R) (_ : IsHereditary R), Nontrivial R ∧
      ∃ e : V(R).carrier → H, IsKHom ℵ₀ e ∧ Function.Bijective e := by
  obtain ⟨R, hR, halg, hher, e, he, hbij⟩ :=
    corollary_4_7_one_forward le_rfl k x (isBraidedOver_addOf_of_ne hgen hx)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx 0 (by rw [cmul_zero, zero_nsmul])
  exact ⟨R, hR, halg, hher, nontrivial_of_realization R e he hbij hx0, e, he, hbij⟩

/-- **The §5 preamble** (`kappa_monoids.tex:1989–1991`): *"a cyclic `ℵ₀`-monoid with generator
`x` can be realized as `V^{ℵ₀}(R)` of a nonzero hereditary ring if and only if `ℵ₀x ≠ nx` for all
`n ∈ ℕ₀`."*

"Nonzero" is `Nontrivial R`; "hereditary" is `IsHereditary` (left and right).  The forward
direction holds for any nonzero ring (`ne_nsmul_of_realization`), the backward one produces a
hereditary algebra over any prescribed field (`realization_of_ne`). -/
theorem cyclic_realizable_iff {x : H} (hgen : KGenerates (ℵ₀ : Cardinal.{u}) ({x} : Set H)) :
    (∃ (R : Type u) (_ : Ring R) (_ : Nontrivial R) (_ : IsHereditary R),
        ∃ e : V(R).carrier → H, IsKHom ℵ₀ e ∧ Function.Bijective e) ↔
      ∀ n : ℕ, ℵ₀∙x ≠ n • x := by
  constructor
  · rintro ⟨R, _, _, -, e, he, hbij⟩ n
    exact ne_nsmul_of_realization hgen R e he hbij n
  · intro hx
    obtain ⟨R, hR, -, hher, hnt, e, he, hbij⟩ := realization_of_ne hgen hx (ULift.{u} ℚ)
    exact ⟨R, hR, hnt, hher, e, he, hbij⟩

/-- **The §5 preamble, second sentence** (`kappa_monoids.tex:1992`): a cyclic `ℵ₀`-monoid is
`V^{ℵ₀}(R)` for a nonzero hereditary ring iff it is `C ∪ {∞}` for a nonzero (reduced) cyclic
monoid `C` — `cyclic_realizable_iff` combined with `ne_nsmul_iff_exists_withTop`, whose docstring
records why `C` is taken reduced. -/
theorem cyclic_realizable_iff_withTop {x : H}
    (hgen : KGenerates (ℵ₀ : Cardinal.{u}) ({x} : Set H)) :
    (∃ (R : Type u) (_ : Ring R) (_ : Nontrivial R) (_ : IsHereditary R),
        ∃ e : V(R).carrier → H, IsKHom ℵ₀ e ∧ Function.Bijective e) ↔
      ∃ (C : Type u) (_ : AddCommMonoid C) (hC : IsConical C) (c : C), c ≠ 0 ∧
        (∀ y : C, ∃ n : ℕ, y = n • c) ∧
        letI := TrivExt.instKMonoid hC (le_refl (ℵ₀ : Cardinal.{u}))
        ∃ e : WithTop C → H, IsKHom ℵ₀ e ∧ Function.Bijective e :=
  (cyclic_realizable_iff hgen).trans (ne_nsmul_iff_exists_withTop hgen)

end Cyclic

end TwoGen

end KappaMonoid
