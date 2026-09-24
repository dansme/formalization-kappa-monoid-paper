/-
Cardinal sums: restriction to a set containing the support, the support bounded by the sum,
multiplication by a constant, and cardinal sums of natural numbers.  Nothing here mentions
`κ`-monoids; the file depends only on Mathlib and sits at the bottom of the import graph.
-/
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Algebra.BigOperators.Finprod

universe u

open Function

namespace Cardinal

/-- A cardinal sum may be restricted to any set outside of which the summands vanish. -/
theorem sum_eq_sum_subtype {ι : Type u} (f : ι → Cardinal.{u}) (S : Set ι)
    (hS : ∀ i ∉ S, f i = 0) : Cardinal.sum f = Cardinal.sum (fun i : S => f i) :=
  Cardinal.mk_congr
    { toFun := fun p => ⟨⟨p.1, by_contra fun h => (Cardinal.mk_eq_zero_iff.mp
        (by rw [Cardinal.mk_out]; exact hS p.1 h)).false p.2⟩, p.2⟩
      invFun := fun q => ⟨q.1.1, q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The support of a family of cardinals injects into its cardinal sum. -/
theorem mk_support_le_sum {ι : Type u} (c : ι → Cardinal.{u}) :
    #(support c) ≤ Cardinal.sum c := by
  classical
  have hne : ∀ i : support c, Nonempty (c (i : ι)).out := fun i =>
    Cardinal.mk_ne_zero_iff.mp (by rw [Cardinal.mk_out]; exact i.2)
  exact ⟨⟨fun i => ⟨(i : ι), (hne i).some⟩, fun i j hij => Subtype.ext (congrArg Sigma.fst hij)⟩⟩

/-- `Σ (f i · c) = (Σ f) · c` for cardinals. -/
theorem sum_mul_const {ι : Type u} (f : ι → Cardinal.{u}) (c : Cardinal.{u}) :
    Cardinal.sum (fun i => f i * c) = Cardinal.sum f * c := by
  obtain ⟨γ, rfl⟩ : ∃ γ : Type u, #γ = c := ⟨c.out, Cardinal.mk_out c⟩
  calc Cardinal.sum (fun i => f i * #γ) = Cardinal.sum (fun i => #((f i).out × γ)) := by
        congr 1; funext i; simp [Cardinal.mk_prod, Cardinal.mk_out]
    _ = #((i : ι) × ((f i).out × γ)) := (Cardinal.mk_sigma _).symm
    _ = #(((i : ι) × (f i).out) × γ) := Cardinal.mk_congr (Equiv.sigmaProdDistrib _ _).symm
    _ = Cardinal.sum f * #γ := by simp [Cardinal.mk_prod, Cardinal.mk_sigma, Cardinal.mk_out]

/-- A finite cardinal sum of natural numbers is their sum. -/
theorem sum_natCast_fintype {ι : Type u} [Fintype ι] (n : ι → ℕ) :
    Cardinal.sum (fun i => (n i : Cardinal.{u})) = ((∑ i, n i : ℕ) : Cardinal.{u}) := by
  have h1 : (fun i => (n i : Cardinal.{u})) = fun i => #(ULift.{u} (Fin (n i))) := by
    funext i; simp
  rw [h1, ← Cardinal.mk_sigma, Cardinal.mk_fintype, Fintype.card_sigma]
  simp

/-- A finitely supported family of natural numbers sums, as cardinals, to its `finsum`. -/
theorem sum_natCast_of_finite {ι : Type u} (n : ι → ℕ) (hn : (support n).Finite) :
    Cardinal.sum (fun i => (n i : Cardinal.{u})) = ((∑ᶠ i, n i : ℕ) : Cardinal.{u}) := by
  let : Fintype (support n) := hn.fintype
  have h := sum_natCast_fintype (fun i : support n => n i)
  rw [sum_eq_sum_subtype _ (support n) (fun i hi => by rw [not_not.mp hi, Nat.cast_zero]), h,
    ← finsum_eq_sum_of_fintype, finsum_set_coe_eq_finsum_mem, finsum_mem_support]

/-- An infinitely supported family of natural numbers sums, as cardinals, to the cardinality of
its support. -/
theorem sum_natCast_of_infinite {ι : Type u} (n : ι → ℕ) (hn : (support n).Infinite) :
    Cardinal.sum (fun i => (n i : Cardinal.{u})) = #(support n) := by
  have hinf : ℵ₀ ≤ #(support n) := Cardinal.infinite_iff.mp hn.to_subtype
  rw [sum_eq_sum_subtype _ (support n) (fun i hi => by rw [not_not.mp hi, Nat.cast_zero])]
  refine le_antisymm ?_ ?_
  · calc Cardinal.sum (fun i : support n => (n i : Cardinal.{u}))
        ≤ Cardinal.sum (fun _ : support n => ℵ₀) :=
          Cardinal.sum_le_sum _ _ fun i => Cardinal.natCast_lt_aleph0.le
      _ = #(support n) * ℵ₀ := Cardinal.sum_const' _ _
      _ = #(support n) := Cardinal.mul_aleph0_eq hinf
  · calc #(support n) = Cardinal.sum (fun _ : support n => (1 : Cardinal.{u})) := by
          rw [Cardinal.sum_const', mul_one]
      _ ≤ _ := Cardinal.sum_le_sum _ _ fun i =>
          Cardinal.one_le_iff_ne_zero.mpr (by exact_mod_cast i.2)

end Cardinal
