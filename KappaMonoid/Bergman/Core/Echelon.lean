/-
**Echelon bases** (the linear algebra behind Bergman §8).

For a `k`-space `W` embedded in a space of finitely supported functions `M →₀ k`, and an injective
map `f : M → O` into a well-ordered set, `W` has a basis whose members have pairwise distinct
`f`-greatest terms (`EchBasis`, `nonempty_echBasis`).  Conversely a family with pairwise distinct
greatest terms is linearly independent, and the greatest term of a combination is the greatest
term of one of its members (`top_of_linearCombination`).
-/
import KappaMonoid.Bergman.Core.Pure

universe u

namespace Bergman.Core

open Module

variable {k : Type u} [Field k]

section Echelon

variable {M O : Type*} [LinearOrder O]

/-- `m` is the `f`-greatest term of `z`. -/
def IsTopF (f : M → O) (z : M →₀ k) (m : M) : Prop :=
  m ∈ z.support ∧ ∀ m' ∈ z.support, f m' ≤ f m

theorem exists_isTopF (f : M → O) {z : M →₀ k} (hz : z ≠ 0) : ∃ m, IsTopF f z m := by
  have hne : z.support.Nonempty := Finsupp.support_nonempty_iff.2 hz
  obtain ⟨m, hm, hm'⟩ := Finset.exists_max_image _ f hne
  exact ⟨m, hm, hm'⟩

theorem IsTopF.unique {f : M → O} (hf : Function.Injective f) {z : M →₀ k} {m m' : M}
    (h : IsTopF f z m) (h' : IsTopF f z m') : m = m' :=
  hf (le_antisymm (h'.2 m h.1) (h.2 m' h'.1))

/-- **The greatest term of a combination** of a family with distinct greatest terms. -/
theorem top_of_linearCombination {I : Type*} (f : M → O) (hf : Function.Injective f)
    (v : I → M →₀ k) (key : I → M) (hkey : Function.Injective key)
    (htop : ∀ i, IsTopF f (v i) (key i)) {c : I →₀ k} (hc : c ≠ 0) :
    ∃ i ∈ c.support, IsTopF f (Finsupp.linearCombination k v c) (key i) ∧
      ∀ i' ∈ c.support, f (key i') ≤ f (key i) := by
  classical
  have hne : c.support.Nonempty := Finsupp.support_nonempty_iff.2 hc
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image _ (fun i => f (key i)) hne
  have hsum : Finsupp.linearCombination k v c = ∑ i ∈ c.support, c i • v i := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine ⟨i₀, hi₀, ⟨?_, fun m hm => ?_⟩, hmax⟩
  · rw [hsum, Finsupp.mem_support_iff, Finsupp.finsetSum_apply,
      Finset.sum_eq_single i₀]
    · rw [Finsupp.smul_apply, smul_eq_mul]
      exact mul_ne_zero (Finsupp.mem_support_iff.1 hi₀)
        (Finsupp.mem_support_iff.1 (htop i₀).1)
    · intro i hi hne
      rw [Finsupp.smul_apply]
      by_cases h0 : v i (key i₀) = 0
      · rw [h0, smul_zero]
      · exfalso
        have h1 := (htop i).2 _ (Finsupp.mem_support_iff.2 h0)
        have h2 := hmax i hi
        exact hne (hkey (hf (le_antisymm h2 h1)))
    · intro h; exact absurd hi₀ h
  · rw [hsum] at hm
    obtain ⟨i, hi, hm⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hm)
    exact ((htop i).2 m (Finsupp.support_smul hm)).trans (hmax i hi)

theorem linearIndependent_of_top {I : Type*} (f : M → O) (hf : Function.Injective f)
    (v : I → M →₀ k) (key : I → M) (hkey : Function.Injective key)
    (htop : ∀ i, IsTopF f (v i) (key i)) : LinearIndependent k v := by
  rw [linearIndependent_iff]
  intro c hc
  by_contra hne
  obtain ⟨i, -, hi, -⟩ := top_of_linearCombination f hf v key hkey htop hne
  rw [hc] at hi
  exact absurd hi.1 (by simp)

variable {W : Type*} [AddCommGroup W] [Module k W]

/-- A basis of `W` (embedded by `φ`) with pairwise distinct greatest terms, indexed by them. -/
structure EchBasis (f : M → O) (φ : W →ₗ[k] M →₀ k) where
  /-- The greatest terms. -/
  s : Set M
  /-- The basis. -/
  b : Basis s k W
  top : ∀ m : s, IsTopF f (φ (b m)) m

theorem nonempty_echBasis [WellFoundedLT O] (f : M → O) (hf : Function.Injective f)
    (φ : W →ₗ[k] M →₀ k) (hφ : Function.Injective φ) : Nonempty (EchBasis f φ) := by
  classical
  let T : Set M := {m | ∃ y : W, y ≠ 0 ∧ IsTopF f (φ y) m}
  let v : T → W := fun m => m.2.choose
  have hv : ∀ m : T, IsTopF f (φ (v m)) m := fun m => m.2.choose_spec.2
  have hli : LinearIndependent k v := by
    refine LinearIndependent.of_comp φ ?_
    exact linearIndependent_of_top f hf (φ ∘ v) Subtype.val Subtype.val_injective hv
  have hsp : ∀ o : O, ∀ y : W, ∀ m, IsTopF f (φ y) m → f m = o →
      y ∈ Submodule.span k (Set.range v) := by
    intro o
    induction o using WellFoundedLT.induction with
    | _ o ih =>
      intro y m hm hmo
      have hy : y ≠ 0 := by
        rintro rfl; exact absurd hm.1 (by simp)
      let m' : T := ⟨m, y, hy, hm⟩
      set c : k := φ y m / φ (v m') m
      have hvm : φ (v m') m ≠ 0 := Finsupp.mem_support_iff.1 (hv m').1
      set y' := y - c • v m'
      have hyy : y = y' + c • v m' := by simp [y']
      rw [hyy]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨m', rfl⟩))
      by_cases hy' : y' = 0
      · rw [hy']; exact Submodule.zero_mem _
      obtain ⟨n, hn⟩ := exists_isTopF f ((map_ne_zero_iff φ hφ).2 hy')
      refine ih (f n) ?_ y' n hn rfl
      rw [← hmo]
      have hle : f n ≤ f m := by
        have h1 := hn.1
        rw [show φ y' = φ y - c • φ (v m') by simp [y']] at h1
        rcases Finset.mem_union.1 (Finsupp.support_sub h1) with h | h
        · exact hm.2 n h
        · exact (hv m').2 n (Finsupp.support_smul h)
      refine lt_of_le_of_ne hle fun he => ?_
      have hnm : n = m := hf he
      have h1 := hn.1
      rw [hnm, Finsupp.mem_support_iff] at h1
      apply h1
      simp only [y', map_sub, map_smul, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      change φ y m - φ y m / φ (v m') m * φ (v m') m = 0
      rw [div_mul_cancel₀ _ hvm, sub_self]
  refine ⟨⟨T, Basis.mk hli fun y _ => ?_, fun m => ?_⟩⟩
  · by_cases hy : y = 0
    · rw [hy]; exact Submodule.zero_mem _
    obtain ⟨m, hm⟩ := exists_isTopF f ((map_ne_zero_iff φ hφ).2 hy)
    exact hsp _ y m hm rfl
  · rw [Basis.mk_apply]; exact hv m

end Echelon

end Bergman.Core
