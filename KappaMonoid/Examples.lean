/-
Examples 2.3 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

The `κ`-monoid `V^κ(C)` of Examples 2.3(4) is built in `KappaMonoid/Modules.lean`; this file
contains the other three examples, none of which is a monoid of modules:

* 2.3(3) `Fcard κ`, the cardinals bounded by `κ`, with cardinal summation.  This is also the
  `κ`-monoid `F_κ` underlying the free `κ`-monoids of §2.1.
* 2.3(1) the *trivial `κ`-extension* `M ⊎ {∞}` of a reduced commutative monoid `M`, where a
  family sums to its finite sum if it has finite support inside `M`, and to `∞` otherwise.
* 2.3(2) `ℝ≥0 ∪ {∞} = ℝ≥0∞`, with `Σ` the sum of the series.
-/
import KappaMonoid.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

universe u v

open Cardinal Function Set

namespace KappaMonoid

/-! ## Cardinal summation

Three facts about `Cardinal.sum` matching the three axioms of `SumData`.  `Cardinal.sum f` is by
definition `#(Σ i, (f i).out)`, so each is an isomorphism of sigma types. -/

/-- Cardinal summation is invariant under reindexing. -/
theorem csum_congr {ι ι' : Type u} (e : ι ≃ ι') (f : ι' → Cardinal.{u}) :
    Cardinal.sum (f ∘ e) = Cardinal.sum f :=
  Cardinal.mk_sigma_congr e fun _ => rfl

/-- A cardinal sum over a one-point index type is its unique entry. -/
theorem csum_unique {ι : Type u} [Unique ι] (f : ι → Cardinal.{u}) :
    Cardinal.sum f = f default := by
  rw [show f = (fun _ : ι => f default) from funext fun i => by rw [Unique.eq_default i],
    Cardinal.sum_const' ι (f default), Cardinal.mk_eq_one ι, one_mul]

/-- Cardinal summation is associative over sigma types. -/
theorem csum_sigma {ι : Type u} {ρ : ι → Type u} (x : ∀ i, ρ i → Cardinal.{u}) :
    Cardinal.sum (fun i => Cardinal.sum (x i)) = Cardinal.sum fun p : (i : ι) × ρ i => x p.1 p.2 := by
  have hrow : ∀ i, #((Cardinal.sum (x i)).out) = #((j : ρ i) × (x i j).out) := by
    intro i
    rw [Cardinal.mk_out, Cardinal.mk_sigma]
    exact congrArg _ (funext fun j => (Cardinal.mk_out _).symm)
  calc Cardinal.sum (fun i => Cardinal.sum (x i))
      = #((i : ι) × (j : ρ i) × (x i j).out) := Cardinal.mk_sigma_congrRight hrow
    _ = Cardinal.sum fun p : (i : ι) × ρ i => x p.1 p.2 :=
        Cardinal.mk_congr (Equiv.sigmaAssoc (fun (i : ι) (j : ρ i) => (x i j).out)).symm

/-- A cardinal sum over a two-point index type is a sum of cardinals. -/
theorem csum_pair (α β : Cardinal.{u}) :
    Cardinal.sum (Sum.elim (fun _ : PUnit.{u + 1} => α) (fun _ : PUnit.{u + 1} => β)) = α + β := by
  have h1 : Cardinal.sum (Sum.elim (fun _ : PUnit.{u + 1} => α) (fun _ : PUnit.{u + 1} => β))
      = #((_ : PUnit.{u + 1}) × α.out ⊕ (_ : PUnit.{u + 1}) × β.out) :=
    Cardinal.mk_congr (Equiv.sumSigmaDistrib _)
  rw [h1, Cardinal.mk_sum, Cardinal.mk_sigma, Cardinal.mk_sigma, csum_unique, csum_unique,
    Cardinal.mk_out, Cardinal.mk_out, Cardinal.lift_id, Cardinal.lift_id]

/-- An empty cardinal sum is `0`. -/
theorem csum_isEmpty {ι : Type u} [IsEmpty ι] (f : ι → Cardinal.{u}) : Cardinal.sum f = 0 := by
  have : IsEmpty ((i : ι) × (f i).out) := ⟨fun q => IsEmpty.false q.1⟩
  exact Cardinal.mk_eq_zero _

/-- A `≤ κ`-indexed sum of cardinals `≤ κ` is `≤ κ`. -/
theorem csum_le_of_le {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) {ι : Type u} (hι : #ι ≤ κ)
    {f : ι → Cardinal.{u}} (hf : ∀ i, f i ≤ κ) : Cardinal.sum f ≤ κ :=
  calc Cardinal.sum f ≤ Cardinal.sum (fun _ : ι => κ) := Cardinal.sum_le_sum _ _ hf
    _ = #ι * κ := Cardinal.sum_const' ι κ
    _ ≤ κ * κ := mul_le_mul' hι le_rfl
    _ = κ := Cardinal.mul_eq_self hκ

/-! ## Examples 2.3(3): the cardinals bounded by `κ` -/

/-- `F_κ`, the `κ`-monoid of all cardinals `≤ κ` (Examples 2.3(3)). -/
abbrev Fcard (κ : Cardinal.{u}) : Type (u + 1) := {α : Cardinal.{u} // α ≤ κ}

namespace Fcard

variable {κ : Cardinal.{u}}

instance : Zero (Fcard κ) := ⟨⟨0, zero_le⟩⟩

@[simp] theorem val_zero : ((0 : Fcard κ) : Cardinal.{u}) = 0 := rfl

theorem ext {a b : Fcard κ} (h : (a : Cardinal.{u}) = b) : a = b := Subtype.ext h

/-- The summation data on `F_κ`: cardinal summation, which stays `≤ κ` by `csum_le_of_le`. -/
noncomputable def sumData (hκ : ℵ₀ ≤ κ) : SumData (Order.succ κ) (Fcard κ) where
  isRegular := Cardinal.isRegular_succ hκ
  sum {ι} h x :=
    ⟨Cardinal.sum fun i => (x i : Cardinal.{u}),
      csum_le_of_le hκ (KMonoid.le_of_lt_succ h) fun i => (x i).2⟩
  sum_congr _ _ e x := ext (csum_congr e fun i => (x i : Cardinal.{u}))
  sum_unique _ x := ext (csum_unique fun i => (x i : Cardinal.{u}))
  sum_sigma _ _ x _ := ext (csum_sigma fun i j => (x i j : Cardinal.{u}))

theorem sumData_zero (hκ : ℵ₀ ≤ κ) : (sumData hκ).zero = 0 := ext (csum_isEmpty _)

/-- **Examples 2.3(3)**: the cardinals `≤ κ` form a `κ`-monoid. -/
@[instance_reducible]
noncomputable def instKMonoid (hκ : ℵ₀ ≤ κ) : KMonoid κ (Fcard κ) where
  toLMonoid := (sumData hκ).toLMonoidOfZero (sumData_zero hκ)
  aleph0_le := hκ

/-- The `κ`-sum on `F_κ` is cardinal summation. -/
@[simp] theorem instKMonoid_sumOf (hκ : ℵ₀ ≤ κ) {ι : Type u} (h : #ι ≤ κ) (x : ι → Fcard κ) :
    letI := instKMonoid hκ
    ((KMonoid.sumOf (κ := κ) h x : Fcard κ) : Cardinal.{u})
      = Cardinal.sum fun i => (x i : Cardinal.{u}) := rfl

/-- Addition on `F_κ` is addition of cardinals. -/
theorem instKMonoid_add (hκ : ℵ₀ ≤ κ) (a b : Fcard κ) :
    letI := instKMonoid hκ
    ((a + b : Fcard κ) : Cardinal.{u}) = (a : Cardinal.{u}) + b := by
  letI := instKMonoid hκ
  have hu : #PUnit.{u + 1} ≤ κ := KMonoid.mk_le_of_finite (H := Fcard κ) _
  have hPP : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) ≤ κ := KMonoid.mk_sum_le (H := Fcard κ) hu hu
  rw [LMonoid.add_eq_lsumOf (lam := Order.succ κ) (KMonoid.lt_succ hPP) a b]
  show Cardinal.sum (fun p : PUnit.{u + 1} ⊕ PUnit.{u + 1} =>
      ((Sum.elim (fun _ => a) (fun _ => b) p : Fcard κ) : Cardinal.{u}))
    = (a : Cardinal.{u}) + b
  rw [show (fun p : PUnit.{u + 1} ⊕ PUnit.{u + 1} =>
        ((Sum.elim (fun _ => a) (fun _ => b) p : Fcard κ) : Cardinal.{u}))
      = Sum.elim (fun _ => (a : Cardinal.{u})) (fun _ => (b : Cardinal.{u})) from
    funext fun p => by rcases p with p | p <;> rfl]
  exact csum_pair _ _

end Fcard

/-! ## Examples 2.3(2): the extended nonnegative reals

`ℝ≥0∞` is an `ℵ₀`-monoid with `Σ` the sum of the series.  Since every family in `ℝ≥0∞` is
summable, `tsum` satisfies the axioms outright; the additive monoid is the existing one, so this
is built with `SumData.toLMonoid'` rather than `toLMonoidOfZero`. -/

namespace ENNRealExample

open ENNReal

/-- `Σ` on `ℝ≥0∞`: the sum of the family as a series. -/
noncomputable def sumData : SumData (Order.succ ℵ₀) ENNReal where
  isRegular := Cardinal.isRegular_succ le_rfl
  sum _ x := ∑' i, x i
  sum_congr _ _ e x := e.tsum_eq x
  sum_unique := fun {ι} _ _ x => by
    letI : Fintype ι := Unique.fintype
    rw [tsum_fintype]
    exact Fintype.sum_unique x
  sum_sigma _ _ x _ := (ENNReal.tsum_sigma x).symm

theorem sumData_add (h : #(PUnit.{1} ⊕ PUnit.{1}) < Order.succ ℵ₀) (a b : ENNReal) :
    a + b = sumData.sum h (Sum.elim (fun _ => a) (fun _ => b)) := by
  show a + b = ∑' p : PUnit.{1} ⊕ PUnit.{1}, Sum.elim (fun _ => a) (fun _ => b) p
  rw [tsum_fintype, Fintype.sum_sum_type]
  simp

/-- **Examples 2.3(2)**: `ℝ≥0∞` is an `ℵ₀`-monoid, with its usual addition. -/
@[instance_reducible]
noncomputable def instKMonoid : KMonoid ℵ₀ ENNReal where
  toLMonoid := sumData.toLMonoid' sumData_add
  aleph0_le := le_rfl

/-- The `ℵ₀`-sum on `ℝ≥0∞` is the sum of the series. -/
@[simp] theorem instKMonoid_sumOf {ι : Type} (h : #ι ≤ ℵ₀) (x : ι → ENNReal) :
    letI := instKMonoid
    KMonoid.sumOf (κ := ℵ₀) h x = ∑' i, x i := rfl

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
