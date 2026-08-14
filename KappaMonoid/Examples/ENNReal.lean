/-
**Examples 2.3(2)**: the extended nonnegative reals.
-/
import KappaMonoid.Examples.TrivExt
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

universe u v

open Cardinal Function Set
open scoped Classical

namespace KappaMonoid

/-! ## Examples 2.3(2): the extended nonnegative reals

`ℝ≥0∞` is an `ℵ₀`-monoid with `Σ` the sum of the series.  Since every family in `ℝ≥0∞` is
summable, `tsum` satisfies the axioms outright; the additive monoid is the existing one, so this
is built with `SumData.toLMonoid'` rather than `toLMonoidOfZero`. -/

namespace ENNRealExample

open ENNReal

/-- `Σ` on `ℝ≥0∞`: the sum of the family as a series.  Universe-polymorphic in the index types,
since `tsum` is available for a family indexed by any type. -/
noncomputable def sumData : SumData (Order.succ (ℵ₀ : Cardinal.{u})) ENNReal where
  isRegular := Cardinal.isRegular_succ le_rfl
  sum _ x := ∑' i, x i
  sum_congr _ _ e x := e.tsum_eq x
  sum_unique := fun {ι} _ _ x => by
    letI : Fintype ι := Unique.fintype
    rw [tsum_fintype]
    exact Fintype.sum_unique x
  sum_sigma _ _ x _ := (ENNReal.tsum_sigma x).symm

theorem sumData_add (h : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) < Order.succ (ℵ₀ : Cardinal.{u}))
    (a b : ENNReal) :
    a + b = sumData.sum h (Sum.elim (fun _ => a) (fun _ => b)) := by
  show a + b = ∑' p : PUnit.{u + 1} ⊕ PUnit.{u + 1}, Sum.elim (fun _ => a) (fun _ => b) p
  rw [tsum_fintype, Fintype.sum_sum_type]
  simp

/-- **Examples 2.3(2)**: `ℝ≥0∞` is an `ℵ₀`-monoid, with its usual addition. -/
@[instance_reducible]
noncomputable def instKMonoid : KMonoid (ℵ₀ : Cardinal.{u}) ENNReal where
  toLMonoid := sumData.toLMonoid' sumData_add
  aleph0_le := le_rfl

/-- The `ℵ₀`-sum on `ℝ≥0∞` is the sum of the series. -/
@[simp] theorem instKMonoid_sumOf {ι : Type u} (h : #ι ≤ (ℵ₀ : Cardinal.{u})) (x : ι → ENNReal) :
    letI := instKMonoid
    KMonoid.sumOf (κ := (ℵ₀ : Cardinal.{u})) h x = ∑' i, x i := rfl

/-- The operation differs from the trivial `ℵ₀`-extension of `ℝ≥0` (Examples 2.3(1)): a family
with infinite support can have a finite sum. -/
theorem exists_infinite_support_sum_ne_top :
    ∃ x : ℕ → ENNReal, (Function.support x).Infinite ∧ ∑' i, x i ≠ ⊤ := by
  refine ⟨fun n => (2 : ENNReal)⁻¹ ^ n, ?_, ?_⟩
  · have hsupp : Function.support (fun n : ℕ => (2 : ENNReal)⁻¹ ^ n) = Set.univ := by
      ext n
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact pow_ne_zero n (by simp)
    rw [hsupp]
    exact Set.infinite_univ
  · rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (by simp)

end ENNRealExample

end KappaMonoid
