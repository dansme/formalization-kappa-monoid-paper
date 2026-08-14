/-
Internal direct sums of a family of submodules, and the sub-sums cut out by a set of indices.
-/
import KappaMonoid.Modules.Small

universe u v w

open Cardinal Function Set DirectSum
open scoped Classical

namespace KappaMonoid

open KMonoid LMonoid

variable (R : Type u) [Ring R]


/-! ## The internal direct sum of a family of submodules -/

section DsSub

variable {ι : Type u} (N : ι → Type u) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- The internal direct sum `⨁ i, P i` of a family of submodules `P i ≤ N i`, as a submodule
of `⨁ i, N i`. -/
def dsSub (P : ∀ i, Submodule R (N i)) : Submodule R (⨁ i, N i) where
  carrier := {m | ∀ i, m i ∈ P i}
  add_mem' := by
    intro a b ha hb i
    show a i + b i ∈ P i
    exact (P i).add_mem (ha i) (hb i)
  zero_mem' := fun i => (P i).zero_mem
  smul_mem' := by
    intro c a ha i
    show c • a i ∈ P i
    exact (P i).smul_mem c (ha i)

theorem mem_dsSub {P : ∀ i, Submodule R (N i)} {m : ⨁ i, N i} :
    m ∈ dsSub R N P ↔ ∀ i, m i ∈ P i := Iff.rfl

theorem lmap_subtype_range (P : ∀ i, Submodule R (N i)) :
    LinearMap.range (DirectSum.lmap (fun i => (P i).subtype)) = dsSub R N P := by
  apply le_antisymm
  · rintro m ⟨x, rfl⟩ i
    rw [DirectSum.lmap_apply]
    exact (x i).2
  · intro m hm
    rw [← DirectSum.sum_support_of m]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine ⟨lof R ι (fun i => ↥(P i)) i ⟨m i, hm i⟩, ?_⟩
    rw [DirectSum.lmap_lof, lof_eq_of R]
    rfl

theorem lmap_subtype_injective (P : ∀ i, Submodule R (N i)) :
    Function.Injective (DirectSum.lmap (fun i => (P i).subtype)) :=
  (DirectSum.lmap_injective _).mpr fun _ => Subtype.val_injective

/-- `⨁ i, P i` really is the direct sum of the `P i`. -/
noncomputable def dsSubIso (P : ∀ i, Submodule R (N i)) :
    ↥(dsSub R N P) ≃ₗ[R] ⨁ i, ↥(P i) :=
  (LinearEquiv.ofEq _ _ (lmap_subtype_range R N P)).symm.trans
    (LinearEquiv.ofInjective _ (lmap_subtype_injective R N P)).symm

theorem dsSub_isCompl {P Q : ∀ i, Submodule R (N i)} (h : ∀ i, IsCompl (P i) (Q i)) :
    IsCompl (dsSub R N P) (dsSub R N Q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro m hmP hmQ
    refine DirectSum.ext (β := N) fun i => ?_
    show m i = 0
    exact Submodule.disjoint_def.mp (h i).disjoint (m i) (hmP i) (hmQ i)
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    set y : ⨁ i, N i :=
      DirectSum.lmap (fun i => (P i).projection (Q i) (h i)) m with hydef
    have hyi : ∀ i, y i = (P i).projection (Q i) (h i) (m i) := fun i =>
      DirectSum.lmap_apply _ m i
    have hyP : y ∈ dsSub R N P := by
      intro i
      rw [hyi i]
      exact Submodule.projection_apply_mem (h i) (m i)
    have hyQ : m - y ∈ dsSub R N Q := by
      intro i
      show m i - y i ∈ Q i
      rw [hyi i]
      refine (Submodule.projection_apply_eq_zero_iff (h i)).mp ?_
      rw [map_sub, Submodule.projection_apply_of_mem_left (h i)
        (Submodule.projection_apply_mem (h i) (m i)), sub_self]
    have : m = y + (m - y) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hyP) (Submodule.mem_sup_right hyQ)

end DsSub

end KappaMonoid
