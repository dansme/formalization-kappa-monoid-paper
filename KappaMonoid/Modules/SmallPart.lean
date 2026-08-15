/-
The `λ⁻`-small part of a class of modules, and generation.
-/
import KappaMonoid.Modules.Theorem43

universe u v w

open Cardinal Function Set DirectSum
open scoped Classical

namespace KappaMonoid

open KMonoid LMonoid

variable (R : Type u) [Ring R]

variable {R}

section SmallPart

variable {κ : Cardinal.{u}} (C : ModuleClass R κ)

theorem ModuleClass.mem_lambdaSmallPart {a : C.carrier} {lam : Cardinal.{u}}
    (h : IsLambdaSmall R lam (C.rep a)) : a ∈ C.lambdaSmallPart lam := h

theorem ModuleClass.isLambdaSmall_of_mem {a : C.carrier} {lam : Cardinal.{u}}
    (h : a ∈ C.lambdaSmallPart lam) : IsLambdaSmall R lam (C.rep a) := h

theorem ModuleClass.lambdaSmallPart_isLSubset (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) :
    letI := C.instKMonoid hκ
    IsLSubset lam hlk (C.lambdaSmallPart lam) := by
  let := C.instKMonoid hκ
  constructor
  · -- the zero module is `λ⁻`-small
    have := C.subsingleton_rep_of_eq_zero (C.instKMonoid_zero hκ)
    intro ι N iAG iMod f
    exact isLambdaSmall_of_subsingleton (R := R) hlam.pos (C.rep 0) N iAG iMod f
  · -- a direct sum of `< λ` many `λ⁻`-small modules is `λ⁻`-small
    intro ι h x hx
    have hsmall : IsLambdaSmall R lam (⨁ i, C.rep (x i)) :=
      isLambdaSmall_dsum hlam h (fun i => C.rep (x i)) fun i => C.isLambdaSmall_of_mem (hx i)
    intro ι₂ N iAG iMod f
    exact IsLambdaSmall.of_equiv hsmall
      (C.rep_sumOf hκ (h.le.trans hlk) x).some.symm N iAG iMod f

theorem ModuleClass.lambdaSmallPart_summand (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u}) :
    letI := C.instKMonoid hκ
    ∀ a ∈ C.lambdaSmallPart lam, ∀ b : C.carrier, (∃ c, b + c = a) →
      b ∈ C.lambdaSmallPart lam := by
  let := C.instKMonoid hκ
  intro a ha b ⟨c, hc⟩
  have hprod : IsLambdaSmall R lam (C.rep b × C.rep c) :=
    IsLambdaSmall.of_equiv (C.isLambdaSmall_of_mem ha)
      ((C.iso_of_eq hc).some.symm.trans (C.rep_add hκ b c).some)
  intro ι N iAG iMod f
  exact hprod.of_prod_left N iAG iMod f

theorem ModuleClass.lambdaSmallPart_small (lam : Cardinal.{u}) :
    ∀ a ∈ C.lambdaSmallPart lam, IsLambdaSmall R lam (C.rep a) := by
  intro a ha ι N iAG iMod f
  exact ha N iAG iMod f

theorem ModuleClass.lambdaSmallPart_mono {lam lam' : Cardinal.{u}} (h : lam ≤ lam') :
    C.lambdaSmallPart lam ⊆ C.lambdaSmallPart lam' := by
  intro a ha ι N iAG iMod f
  exact IsLambdaSmall.mono h (C.isLambdaSmall_of_mem ha) N iAG iMod f

end SmallPart

section Gen

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

theorem KMonoid.KGenerates.mono {S S' : Set H} (h : S ⊆ S') (hgen : KGenerates κ S) :
    KGenerates κ S' :=
  Set.eq_univ_of_univ_subset (hgen ▸ KMonoid.kclosure_mono h)

end Gen

/-! ## Projective modules: Corollaries 4.5–4.7 -/

end KappaMonoid
