/-
Auxiliary lemmas on `λ⁻`-sums, and the `finsum` bridge for `λ = ℵ₀`.
-/
import KappaMonoid.Core

universe u v w

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid


/-! ## Auxiliary lemmas

Cardinal bookkeeping for the index type `ι × ℕ` of braiding partitions, and the `finsum`
bridge used for `λ = ℵ₀`. -/

section Aux

/-- `#(ι × ℕ) ≤ κ` whenever `#ι ≤ κ` and `κ` is infinite: the index type of braiding
partitions is no bigger than the index type of the families. -/
theorem mk_prod_nat_le {κ : Cardinal.{u}} {ι : Type u} (hκ : ℵ₀ ≤ κ) (hι : #ι ≤ κ) :
    #(ι × ℕ) ≤ κ := by
  have hmp : #(ι × ℕ) = #ι * ℵ₀ := by simp [Cardinal.mk_prod]
  rw [hmp]
  calc #ι * ℵ₀ ≤ κ * κ := mul_le_mul' hι hκ
    _ = κ := Cardinal.mul_eq_self hκ

/-! ## Finsum bridge for `λ = ℵ₀`

For `lam = ℵ₀` every index set occurring in a braiding is finite, so all the sums involved are
ordinary finite sums.  Working with `∑ᶠ i ∈ S, f i` (Mathlib's `finsum`) instead of
`lsumOf hS (fun i : S => f i)` removes the finiteness side conditions from the *terms* and gives
access to Mathlib's `finsum_mem_*` API. -/

/-- Splitting a `finsum` over a finite set along a subset. -/
theorem finsum_mem_split {α : Type u} {M : Type v} [AddCommMonoid M] (f : α → M) {S T : Set α}
    (hST : S ⊆ T) (hT : T.Finite) :
    ∑ᶠ i ∈ T, f i = (∑ᶠ i ∈ S, f i) + ∑ᶠ i ∈ T \ S, f i := by
  have hdisj : Disjoint S (T \ S) := by
    rw [Set.disjoint_left]; intro i hi hi'; exact hi'.2 hi
  rw [← finsum_mem_union hdisj (hT.subset hST) (hT.sdiff (t := S)), Set.union_sdiff_cancel hST]

/-- Indices outside a subset where the summand vanishes may be dropped from a `finsum`. -/
theorem finsum_mem_eq_of_diff_eq_zero {α : Type u} {M : Type v} [AddCommMonoid M] {f : α → M}
    {S T : Set α} (hST : S ⊆ T) (hT : T.Finite) (h0 : ∀ i ∈ T \ S, f i = 0) :
    ∑ᶠ i ∈ T, f i = ∑ᶠ i ∈ S, f i := by
  rw [finsum_mem_split f hST hT, finsum_mem_eq_zero_of_forall_eq_zero h0, add_zero]

/-- A set contained in a union splits into the parts it shares with the two pieces. -/
theorem eq_union_inter_of_subset_union {α : Type u} {A B C : Set α} (h : A ⊆ B ∪ C) :
    A = (B ∩ A) ∪ (A ∩ C) := by
  refine Set.Subset.antisymm (fun j hj => ?_) ?_
  · rcases h hj with hj' | hj'
    · exact Or.inl ⟨hj', hj⟩
    · exact Or.inr ⟨hj, hj'⟩
  · rintro j (⟨-, hj⟩ | ⟨hj, -⟩) <;> exact hj

/-- Variant of `eq_union_inter_of_subset_union` when the first piece is contained in `A`. -/
theorem eq_union_inter_of_subset_union' {α : Type u} {A B C : Set α} (h : A ⊆ B ∪ C)
    (hB : B ⊆ A) : A = B ∪ (A ∩ C) := by
  refine Set.Subset.antisymm (fun j hj => ?_) ?_
  · rcases h hj with hj' | hj'
    · exact Or.inl hj'
    · exact Or.inr ⟨hj, hj'⟩
  · rintro j (hj | ⟨hj, -⟩)
    · exact hB hj
    · exact hj

/-- A `finsum` over a three-element set. -/
theorem finsum_mem_triple {α : Type u} {M : Type v} [AddCommMonoid M] {a b c : α} (f : α → M)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ᶠ i ∈ ({a, b, c} : Set α), f i = f a + f b + f c := by
  rw [show ({a, b, c} : Set α) = insert a {b, c} from rfl,
    finsum_mem_insert f (by simp [hab, hac]) ((Set.finite_singleton c).insert b),
    finsum_mem_pair hbc, add_assoc]


end Aux

/-- The successor map of the limit well-order modelled by `ι × ℕ`. -/
def bsucc {ι : Type u} (p : ι × ℕ) : ι × ℕ := (p.1, p.2 + 1)

theorem bsucc_injective {ι : Type u} : Function.Injective (bsucc (ι := ι)) := by
  rintro ⟨a, n⟩ ⟨b, m⟩ h
  simp [bsucc, Prod.ext_iff] at h
  simp [h.1, h.2]

@[simp] theorem bsucc_snd_ne_zero {ι : Type u} (p : ι × ℕ) : (bsucc p).2 ≠ 0 := Nat.succ_ne_zero _

end KappaMonoid
