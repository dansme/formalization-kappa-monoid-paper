/-
Preliminaries: cardinal arithmetic, the canonical index type `Idx κ`, and the two-element
index types that binary sums are built on.
-/
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel

universe u v w

open Cardinal Function Set

namespace KappaMonoid

/-! ## Preliminaries on cardinals and index types -/

/-- `Idx κ` is a fixed type of cardinality `κ`, playing the role of the von Neumann cardinal
`κ` used as an index set in the paper.  The axioms are stated over arbitrary index types instead;
`Idx κ` serves the constructions of Sections 3 and 4, which produce `κ`-indexed data. -/
abbrev Idx (κ : Cardinal.{u}) : Type u := κ.ord.ToType

@[simp] theorem mk_Idx (κ : Cardinal.{u}) : #(Idx κ) = κ := mk_ord_toType κ

theorem infinite_Idx {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) : Infinite (Idx κ) :=
  Cardinal.infinite_iff.mpr (by rw [mk_Idx]; exact hκ)

theorem nonempty_Idx {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) : Nonempty (Idx κ) :=
  have := infinite_Idx hκ
  inferInstance

theorem nontrivial_Idx {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) : Nontrivial (Idx κ) :=
  have := infinite_Idx hκ
  inferInstance

/-- An embedding of any type of cardinality `≤ κ` into `Idx κ`. -/
noncomputable def emb {ι : Type u} {κ : Cardinal.{u}} (h : #ι ≤ κ) : ι ↪ Idx κ :=
  ((Cardinal.le_def ι (Idx κ)).mp (by simpa using h)).some

/-- For infinite `κ` we have `κ * κ = κ`, hence a bijection `Idx κ × Idx κ ≃ Idx κ`. -/
noncomputable def pairEquiv {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) : Idx κ × Idx κ ≃ Idx κ :=
  (Cardinal.eq.mp (by simp [Cardinal.mul_eq_self hκ])).some

section Regular

variable {lam : Cardinal.{u}} (hlam : lam.IsRegular)
include hlam

theorem mk_lt_of_finite (ι : Type u) [Finite ι] : #ι < lam :=
  (Cardinal.lt_aleph0_iff_finite.mpr ‹_›).trans_le hlam.aleph0_le

/-- A `< λ`-indexed union of `< λ`-sized types is `< λ` (regularity of `λ`). -/
theorem mk_sigma_lt {ι : Type u} {ρ : ι → Type u} (h : #ι < lam) (hρ : ∀ i, #(ρ i) < lam) :
    #((i : ι) × ρ i) < lam := by
  have : Fact lam.IsRegular := ⟨hlam⟩
  rw [← hasCardinalLT_iff_cardinal_mk_lt]
  exact hasCardinalLT_sigma ρ lam ((hasCardinalLT_iff_cardinal_mk_lt _ _).mpr h)
    fun i => (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr (hρ i)

theorem mk_sum_lt {α β : Type u} (hα : #α < lam) (hβ : #β < lam) : #(α ⊕ β) < lam := by
  rw [← hasCardinalLT_iff_cardinal_mk_lt]
  exact (hasCardinalLT_sum_iff α β lam hlam.aleph0_le).mpr
    ⟨(hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hα, (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hβ⟩

theorem mk_prod_lt {α β : Type u} (hα : #α < lam) (hβ : #β < lam) : #(α × β) < lam := by
  rw [Cardinal.mk_prod]
  simpa using Cardinal.mul_lt_of_lt hlam.aleph0_le hα hβ

theorem mk_union_lt {ι : Type u} {S T : Set ι} (hS : #S < lam) (hT : #T < lam) :
    #(↥(S ∪ T)) < lam := by
  rw [← hasCardinalLT_iff_cardinal_mk_lt]
  exact hasCardinalLT_union hlam.aleph0_le ((hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hS)
    ((hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hT)

end Regular

/-! ### The paper's `λ ≤ κ⁺`

Definition 3.1(2) and everything built on it relate a `λ⁻`-monoid to a `κ`-monoid under the
hypothesis `λ ≤ κ⁺`.  All that is ever used of it is that a `< λ`-sized index set has size `≤ κ`,
which is `le_of_lt_of_le_succ`.  The hypothesis is genuinely weaker than `λ ≤ κ`: at `κ = ℵ₀` it
also admits `λ = ℵ₁`, which is the case Kaplansky's theorem supplies in Corollary 4.5. -/

/-- The content of the paper's `λ ≤ κ⁺`: a family indexed by fewer than `λ` elements is indexed
by at most `κ` elements. -/
theorem le_of_lt_of_le_succ {a lam κ : Cardinal.{u}} (hlk : lam ≤ Order.succ κ) (h : a < lam) :
    a ≤ κ :=
  Order.lt_succ_iff.mp (h.trans_le hlk)

/-- The converse direction: `λ ≤ κ` is the stronger hypothesis. -/
theorem le_succ_of_le {lam κ : Cardinal.{u}} (h : lam ≤ κ) : lam ≤ Order.succ κ :=
  h.trans (Order.le_succ κ)

/-- `ℵ₀ ≤ κ⁺` forces `ℵ₀ ≤ κ`: `ℵ₀` is a limit cardinal, so it is not `≤` any successor of a
finite cardinal.  This is what lets `λ ≤ κ⁺` with `λ` infinite keep `κ` infinite without a
separate hypothesis. -/
theorem aleph0_le_of_aleph0_le_succ {κ : Cardinal.{u}} (h : ℵ₀ ≤ Order.succ κ) : ℵ₀ ≤ κ := by
  by_contra hc
  exact absurd h (not_le.mpr (Cardinal.isSuccLimit_aleph0.succ_lt (not_le.mp hc)))

theorem mk_lt_of_injective {lam : Cardinal.{u}} {α β : Type u} (hβ : #β < lam) (f : α → β)
    (hf : Function.Injective f) : #α < lam :=
  (Cardinal.mk_le_of_injective hf).trans_lt hβ

/-! ### Two-element index types

Binary addition is a sum over a two-element index type; these are the equivalences used to
recognise it as such. -/

/-- `α ⊕ β` as a sigma type over the two-point type `PUnit ⊕ PUnit`, the index type of binary
addition: the two halves of `α ⊕ β` are the fibres. -/
def sumEquivSigma (α β : Type u) :
    α ⊕ β ≃ (p : PUnit.{u + 1} ⊕ PUnit.{u + 1}) × Sum.elim (fun _ => α) (fun _ => β) p where
  toFun := Sum.elim (fun a => ⟨.inl ⟨⟩, a⟩) (fun b => ⟨.inr ⟨⟩, b⟩)
  invFun
    | ⟨.inl _, a⟩ => .inl a
    | ⟨.inr _, b⟩ => .inr b
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro ⟨⟨⟩ | ⟨⟩, _⟩ <;> rfl

/-- `ULift Bool ≃ PUnit ⊕ PUnit`, sending `false` to the left and `true` to the right. -/
def uliftBoolEquiv : ULift.{u} Bool ≃ PUnit.{u + 1} ⊕ PUnit.{u + 1} :=
  (Equiv.ulift (α := Bool)).trans Equiv.boolEquivPUnitSumPUnit

end KappaMonoid
