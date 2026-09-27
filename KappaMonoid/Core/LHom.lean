/-
`λ = ℵ₀`: a `λ⁻`-monoid is an ordinary commutative monoid.  And `IsLHom`, the homomorphisms
from a `λ⁻`-monoid into a `κ`-monoid, with the reducedness of anything that embeds into one.
-/
import KappaMonoid.Core.Bare

universe u v w

open Cardinal Function Set

namespace KappaMonoid

/-! ## `λ = ℵ₀`: `λ⁻`-monoids are ordinary commutative monoids -/

namespace LMonoid

theorem mk_lt_aleph0_iff_finite {ι : Type u} : #ι < ℵ₀ ↔ Finite ι :=
  Cardinal.lt_aleph0_iff_finite

/-- For `λ = ℵ₀` every commutative monoid is a `λ⁻`-monoid, with the finite sum as its
summation. -/
@[instance_reducible]
noncomputable def ofAddCommMonoid (M : Type v) [inst : AddCommMonoid M] : LMonoid ℵ₀ M where
  toAddCommMonoid := inst
  isRegular := Cardinal.isRegular_aleph0
  sum := fun _ x => ∑ᶠ i, x i
  sum_congr := fun _ _ e x => finsum_comp_equiv e
  sum_unique := fun _ x =>
    finsum_eq_single x default fun b hb => absurd (Unique.eq_default b) hb
  sum_sigma := fun {ι ρ} h hρ x hσ => by
    have : Finite ι := mk_lt_aleph0_iff_finite.mp h
    have : ∀ i, Finite (ρ i) := fun i => mk_lt_aleph0_iff_finite.mp (hρ i)
    have : Finite ((i : ι) × ρ i) := mk_lt_aleph0_iff_finite.mp hσ
    let _ : Fintype ι := Fintype.ofFinite ι
    let _ : ∀ i, Fintype (ρ i) := fun i => Fintype.ofFinite (ρ i)
    rw [finsum_eq_sum_of_fintype]
    rw [show (fun i => ∑ᶠ j, x i j) = fun i => ∑ j, x i j from
      funext fun i => finsum_eq_sum_of_fintype _]
    rw [finsum_eq_sum_of_fintype, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  add_eq_sum := fun _ a b => by
    rw [finsum_eq_sum_of_fintype, Fintype.sum_sum_type]
    simp

/-- Sums over a finite index type are ordinary finite sums.  This is the bullet after Lemma 2.5
saying that `Σⁿ(x₁,…,xₙ) = x₁ + ⋯ + xₙ` for finite `n`, the binary operation being `Σ²`. -/
theorem lsumOf_eq_sum {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u} [Fintype ι]
    (h : #ι < lam) (x : ι → X) :
    lsumOf (lam := lam) h x = ∑ i, x i := by
  revert h x
  refine Fintype.induction_empty_option
    (P := fun (ι : Type u) [Fintype ι] =>
      ∀ (h : #ι < lam) (x : ι → X), lsumOf (lam := lam) h x = ∑ i, x i) ?_ ?_ ?_ ι
  · intro α β _ e ih h x
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    have hα : #α < lam := by rw [Cardinal.mk_congr e]; exact h
    rw [lsumOf_equiv (h := ⟨h⟩) (h' := ⟨hα⟩) e x, ih hα fun a => x (e a)]
    exact Equiv.sum_comp e x
  · intro h x
    rw [lsumOf_isEmpty (h := ⟨h⟩)]
    simp
  · intro α _ ih h x
    have hα : #α < lam := lt_of_le_of_lt (Cardinal.mk_le_of_injective (Option.some_injective α)) h
    have hu : #PUnit.{u + 1} < lam := by lam_small
    have hsum : #(α ⊕ PUnit.{u + 1}) < lam := by lam_small
    rw [lsumOf_equiv (h := ⟨h⟩) (h' := ⟨hsum⟩) (Equiv.optionEquivSumPUnit α).symm x,
      show (fun p => x ((Equiv.optionEquivSumPUnit α).symm p))
        = Sum.elim (fun a => x (some a)) (fun _ => x none) by
        funext p; rcases p with p | p <;> rfl,
      lsumOf_sumType (hα := ⟨hα⟩) (hβ := ⟨hu⟩), ih hα (fun a => x (some a)),
      lsumOf_unique (h := ⟨hu⟩),
      Fintype.sum_option]
    exact add_comm _ _

/-- For `λ = ℵ₀` the summation of any `λ⁻`-monoid structure is the ordinary finite sum. -/
theorem lsumOf_aleph0_eq_finsum {ι : Type u} [Fintype ι] (h : #ι < ℵ₀) {X : Type v}
    [LMonoid ℵ₀ X] (x : ι → X) : lsumOf (lam := ℵ₀) h x = ∑ i, x i :=
  lsumOf_eq_sum h x

/-- A `κ`-sum over a finite index type is the ordinary finite sum. -/
theorem _root_.KappaMonoid.KMonoid.sumOf_eq_sum {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]
    {ι : Type u} [Fintype ι] [h : CardLE ι κ] (x : ι → H) :
    ∑[≤ κ] i, x i = ∑ i, x i :=
  lsumOf_eq_sum _ x

/-- For `λ = ℵ₀`, a sum over a small subset is the `finsum` over that subset. -/
theorem lsumOf_eq_finsum {X : Type v} [LMonoid ℵ₀ X] {ι : Type u} {S : Set ι} (h : #S < ℵ₀)
    (f : ι → X) : ∑[ℵ₀] i ∈ S, f i = ∑ᶠ i ∈ S, f i := by
  have hfin : S.Finite := Cardinal.lt_aleph0_iff_set_finite.mp h
  let _ : Fintype S := hfin.fintype
  rw [lsumOf_aleph0_eq_finsum h (fun i : S => f i), ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem]

end LMonoid

/-! ## The reducedness of `λ⁻`-monoids that embed into `κ`-monoids

This is the observation behind the reducedness hypothesis of Theorem 3.12. -/

namespace LMonoid

/-- A `λ⁻`-homomorphism from a `λ⁻`-monoid into (the underlying `λ⁻`-monoid of) a
`κ`-monoid. -/
def IsLHom {lam κ : Cardinal.{u}} {X : Type v} {H : Type w} [LMonoid lam X] [KMonoid κ H]
    (hκ : lam ≤ Order.succ κ) (f : X → H) : Prop :=
  f 0 = 0 ∧ ∀ {ι : Type u} (h : #ι < lam) (x : ι → X),
    f (lsumOf (lam := lam) h x) = ∑[≤ κ] i, (f ∘ x) i

variable {lam κ : Cardinal.{u}} {X : Type v} {H : Type w} [LMonoid lam X] [KMonoid κ H]

/-- If a `λ⁻`-monoid `X` admits an injective additive map into a `κ`-monoid, then `X` is
reduced.  Since Theorem 3.12 asserts the existence of a `κ`-monoid `Ĥ ⊇ H`, this shows that
reducedness of `H` is a *necessary* hypothesis there. -/
theorem isConical_of_injective (f : X → H) (hf : Function.Injective f) (h0 : f 0 = 0)
    (hadd : ∀ a b, f (a + b) = f a + f b) : IsConical X := by
  intro a b hab
  have h : f a + f b = 0 := by rw [← hadd, hab, h0]
  obtain ⟨ha, hb⟩ := KMonoid.isConical κ H (f a) (f b) h
  exact ⟨hf (by rw [ha, h0]), hf (by rw [hb, h0])⟩

end LMonoid

end KappaMonoid
