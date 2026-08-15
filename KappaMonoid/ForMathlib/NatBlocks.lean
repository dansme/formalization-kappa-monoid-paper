/-
Cutting `ℕ` into consecutive blocks.

`Nat.blockIdx` is the block index of a sequence of partial sums: for monotone `s` with `s 0 = 0`
it sends `j` to the `k` with `s k ≤ j < s (k+1)`, and leaves the slots beyond every `s l` — the
"leftovers", which occur exactly when `s` is bounded — where they are.  Section 5 uses it to cut
the slots of a form into consecutive blocks of prescribed sizes, and the fibres of `j ↦ j / d`
for the constant-size case.

Nothing here mentions `κ`-monoids; the file depends only on Mathlib.
-/
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Logic.Denumerable
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Card

universe u

open Cardinal

namespace Nat


/-- The fibre of `j ↦ j / d` is the interval `[dk, dk + d)`, which has `d` elements. -/
theorem div_fiber_eq {d : ℕ} (hd : 0 < d) (k : ℕ) :
    {n : ℕ | n / d = k} = Set.Ico (d * k) (d * k + d) := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_Ico]
  constructor
  · rintro rfl
    have h1 := Nat.div_add_mod n d
    have h2 := Nat.mod_lt n hd
    omega
  · rintro ⟨h1, h2⟩
    have h3 := Nat.div_add_mod n d
    have h4 := Nat.mod_lt n hd
    have h5 : d * (n / d) < d * (k + 1) := by rw [Nat.mul_succ]; omega
    have h6 : d * k < d * (n / d + 1) := by rw [Nat.mul_succ]; omega
    have hlt : n / d < k + 1 := Nat.lt_of_mul_lt_mul_left h5
    have hgt : k < n / d + 1 := Nat.lt_of_mul_lt_mul_left h6
    omega

theorem ncard_div_fiber {d : ℕ} (hd : 0 < d) (k : ℕ) : ({n : ℕ | n / d = k}).ncard = d := by
  rw [div_fiber_eq hd, Set.ncard_Ico_nat]
  omega

theorem finite_div_fiber {d : ℕ} (hd : 0 < d) (k : ℕ) : ({n : ℕ | n / d = k}).Finite := by
  rw [div_fiber_eq hd]; exact Set.finite_Ico _ _


open Classical in
/-- The block of `j` for a sequence of partial sums `s`: the largest `k` with `s k ≤ j`, and `j`
itself for the leftover slots, those beyond every `s l`. -/
noncomputable def blockIdx (s : ℕ → ℕ) (j : ℕ) : ℕ :=
  if h : ∃ l, j < s l then Nat.find h - 1 else j

/-- The fibre of `blockIdx` at `k`: the interval `[s k, s (k+1))`, together with `k` itself when
`k` is a leftover slot. -/
theorem blockIdx_fibre {s : ℕ → ℕ} (hs : Monotone s) (hs0 : s 0 = 0) (k : ℕ) :
    {j : ℕ | blockIdx s j = k}
      = Set.Ico (s k) (s (k + 1)) ∪ {j | (¬ ∃ l, j < s l) ∧ j = k} := by
  classical
  ext j
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ico, blockIdx]
  by_cases h : ∃ l, j < s l
  · rw [dif_pos h]
    have hf0 : ¬ (j < s 0) := by rw [hs0]; exact Nat.not_lt_zero j
    have hfpos : 1 ≤ Nat.find h := by
      by_contra hc
      have hz : Nat.find h = 0 := by omega
      exact hf0 (hz ▸ Nat.find_spec h)
    constructor
    · rintro rfl
      refine Or.inl ⟨Nat.not_lt.mp (Nat.find_min h (by omega)), ?_⟩
      rw [show Nat.find h - 1 + 1 = Nat.find h from by omega]
      exact Nat.find_spec h
    · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
      · have hle : Nat.find h ≤ k + 1 := Nat.find_le h2
        have hge : k + 1 ≤ Nat.find h := by
          by_contra hc
          exact absurd (lt_of_lt_of_le (Nat.find_spec h) (hs (by omega : Nat.find h ≤ k)))
            (Nat.not_lt.mpr h1)
        omega
      · exact absurd h h1
  · rw [dif_neg h]
    constructor
    · rintro rfl
      exact Or.inr ⟨h, rfl⟩
    · rintro (⟨-, h2⟩ | ⟨-, h2⟩)
      · exact absurd ⟨k + 1, h2⟩ h
      · exact h2

/-- For a strictly monotone `s` there are no leftover slots — `s` is unbounded — so the fibre of
`blockIdx` at `k` is exactly the block `[s k, s (k+1))`. -/
theorem blockIdx_fibre_of_strictMono {s : ℕ → ℕ} (hs : StrictMono s) (hs0 : s 0 = 0) (k : ℕ) :
    {j : ℕ | blockIdx s j = k} = Set.Ico (s k) (s (k + 1)) := by
  rw [blockIdx_fibre hs.monotone hs0]
  refine Set.union_eq_self_of_subset_right fun j hj => ?_
  exact absurd ⟨j + 1, lt_of_lt_of_le (Nat.lt_succ_self j) (hs.le_apply)⟩ hj.1

theorem blockIdx_fibre_finite {s : ℕ → ℕ} (hs : Monotone s) (hs0 : s 0 = 0) (k : ℕ) :
    {j : ℕ | blockIdx s j = k}.Finite := by
  rw [blockIdx_fibre hs hs0]
  exact (Set.finite_Ico _ _).union ((Set.finite_singleton k).subset fun j hj => hj.2)

end Nat

/-- An infinite index type of cardinality at most `ℵ₀` is in bijection with `ℕ`.  The bijection —
rather than a reindexing of one family by another — is what an `ℕ`-indexed construction needs when
it is to be transported to an index type in another universe. -/
theorem Cardinal.nonempty_equiv_nat_of_le_aleph0 {ι : Type u} (hι : #ι ≤ ℵ₀) (hinf : Infinite ι) :
    Nonempty (ℕ ≃ ι) := by
  have hc : Countable ι := Cardinal.mk_le_aleph0_iff.mp hι
  obtain ⟨d⟩ := nonempty_denumerable_iff.mpr ⟨hc, hinf⟩
  exact ⟨(@Denumerable.eqv ι d).symm⟩
