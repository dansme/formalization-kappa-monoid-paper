/-
Three `finsum` facts with no counterpart in Mathlib, used throughout the braiding constructions
of §§3 and 5.  Nothing here mentions `κ`-monoids; the file depends only on Mathlib and sits at
the bottom of the import graph.
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card

universe u v

/-- A constant sum over a finite set. -/
theorem finsum_mem_const_finite {α : Type u} {M : Type v} [AddCommMonoid M] {S : Set α}
    (hS : S.Finite) (c : M) : ∑ᶠ _i ∈ S, c = S.ncard • c := by
  classical
  have h1 : ∑ᶠ _i ∈ S, c = ∑ _i ∈ hS.toFinset, c := by
    rw [← finsum_mem_coe_finset, hS.coe_toFinset]
  rw [h1, Finset.sum_const, Set.ncard_eq_toFinset_card S hS]

/-- A finite sum of multiples of `c` is a multiple of `c`. -/
theorem exists_nsmul_finsum {M : Type v} [AddCommMonoid M] {ι : Type u} {S : Set ι}
    (hS : S.Finite) (F : ι → M) (c : M) (hF : ∀ i ∈ S, ∃ p : ℕ, F i = p • c) :
    ∃ p : ℕ, ∑ᶠ i ∈ S, F i = p • c := by
  classical
  revert hF
  induction S, hS using Set.Finite.induction_on with
  | empty => exact fun _ => ⟨0, by rw [finsum_mem_empty, zero_smul]⟩
  | @insert a S' ha hS' hind =>
    intro hF
    obtain ⟨p, hp⟩ := hind (fun i hi => hF i (Set.mem_insert_of_mem a hi))
    obtain ⟨q, hq⟩ := hF a (Set.mem_insert a S')
    exact ⟨q + p, by rw [finsum_mem_insert _ ha hS', hp, hq, add_smul]⟩

/-- A distinguished term of a finite sum is a summand of it. -/
theorem exists_add_eq_finsum_mem {M : Type v} [AddCommMonoid M] {ι : Type u} {S : Set ι}
    (hS : S.Finite) (f : ι → M) {i : ι} (hi : i ∈ S) : ∃ c, f i + c = ∑ᶠ j ∈ S, f j := by
  classical
  have hins : insert i (S \ {i}) = S := by
    rw [Set.insert_diff_singleton, Set.insert_eq_of_mem hi]
  refine ⟨∑ᶠ j ∈ (S \ {i}), f j, ?_⟩
  conv_rhs => rw [← hins]
  exact (finsum_mem_insert f (fun h => h.2 rfl) (hS.subset Set.diff_subset)).symm
