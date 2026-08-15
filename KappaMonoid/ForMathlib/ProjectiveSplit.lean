/-
Splitting a surjection onto a projective module.

Two forms of the same fact, both used repeatedly: a surjection onto a projective module splits, so
its source decomposes as the image of the splitting plus the kernel; and a one-sided inverse
`t ∘ i = id` makes `i ∘ t` an idempotent whose image is a copy of the projective module.

Nothing here mentions `κ`-monoids; the file depends only on Mathlib.
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Span.Basic

universe u v

namespace ForMathlib

variable {R : Type u} [Ring R] {F M : Type v} [AddCommGroup F] [Module R F] [AddCommGroup M]
  [Module R M]

/-- **A surjection onto a projective module splits.**  The splitting `σ` is injective, its image
is a complement of `ker π`, and it identifies `M` with that image.

This is the argument behind every "a projective module is a direct summand of a free module"
statement in the development: pick a surjection from a free module and apply this. -/
theorem exists_isCompl_range_of_surjective [Module.Projective R M] (π : F →ₗ[R] M)
    (hπ : Function.Surjective π) :
    ∃ σ : M →ₗ[R] F, (∀ q, π (σ q) = q) ∧ Function.Injective σ ∧
      IsCompl (LinearMap.range σ) (LinearMap.ker π) := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hσπ : ∀ q, π (σ q) = q := fun q => LinearMap.congr_fun hσ q
  have hσinj : Function.Injective σ := fun q q' h => by rw [← hσπ q, ← hσπ q', h]
  refine ⟨σ, hσπ, hσinj, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro y ⟨q, rfl⟩ hker
    have hq : q = 0 := by rw [← hσπ q]; exact hker
    rw [hq, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro y _
    refine Submodule.mem_sup.mpr ⟨σ (π y), ⟨π y, rfl⟩, y - σ (π y), ?_, by abel⟩
    show π (y - σ (π y)) = 0
    rw [map_sub, hσπ, sub_self]

/-- **A one-sided inverse gives an idempotent with the right image.**  If `t ∘ i = id` then
`π := i ∘ t` is idempotent, its image is that of `i`, and `M` is isomorphic to it.

This is how both Kaplansky's and Albrecht's theorems reduce a projective module to an idempotent
on a free module. -/
theorem exists_idempotent_of_leftInverse (t : F →ₗ[R] M) (i : M →ₗ[R] F)
    (hts : ∀ q, t (i q) = q) :
    ∃ π : F →ₗ[R] F, (∀ x, π (π x) = π x) ∧ LinearMap.range π = LinearMap.range i ∧
      Nonempty (M ≃ₗ[R] ↥(LinearMap.range π)) := by
  refine ⟨i ∘ₗ t, fun x => congrArg i (hts (t x)), ?_, ?_⟩
  · refine le_antisymm (LinearMap.range_comp_le_range _ _) ?_
    rintro _ ⟨q, rfl⟩
    exact ⟨i q, congrArg i (hts q)⟩
  · have hinj : Function.Injective i := fun p q h => by rw [← hts p, ← hts q, h]
    have hrange : LinearMap.range (i ∘ₗ t) = LinearMap.range i := by
      refine le_antisymm (LinearMap.range_comp_le_range _ _) ?_
      rintro _ ⟨q, rfl⟩
      exact ⟨i q, congrArg i (hts q)⟩
    exact ⟨(LinearEquiv.ofInjective i hinj).trans (LinearEquiv.ofEq _ _ hrange.symm)⟩

end ForMathlib
