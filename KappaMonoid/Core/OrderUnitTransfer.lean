/-
Example 2.13 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*,

its monoid-theoretic half.

* An order-unit is not unique: a faithful order-unit `u` may be traded for any `v` that dominates
  it and is dominated by it up to finite multiples, `u ≼ n v` and `v ≼ m u`.  This is what makes
  the class of every progenerator a faithful order-unit of `V^κ(R)`.
* The pieces of the size filtration `H_α` are described without `size`: for finite `α` the piece
  `H_α = H_0` consists of the elements below a finite multiple of `u`, and for infinite `α` of the
  elements below `α u`.  This is what makes `H_α = V^α(R)` a statement about generating sets.

The module-theoretic half is `Modules/Rings/Progenerator.lean`.
-/
import KappaMonoid.Core.OrderUnit

universe u v

open Cardinal

namespace KappaMonoid

namespace KMonoid

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-! ## Scalar multiples and the preorder -/

/-- Cardinal scalar multiplication is monotone in the element. -/
theorem cmul_le_cmul_right {a b : H} (h : a ≼ b) (γ : Cardinal.{u}) (hγ : γ ≤ κ) :
    cmul (κ := κ) γ hγ a ≼ cmul (κ := κ) γ hγ b := by
  obtain ⟨c, hc⟩ := h
  refine ⟨cmul (κ := κ) γ hγ c, ?_⟩
  rw [← hc]
  exact (LMonoid.lcmul_distrib (lam := Order.succ κ) (lt_succ_of_le hγ) a c).symm

/-- If `a ≼ n b` then `γ a ≼ (γ n) b`. -/
theorem cmul_le_cmul_mul_of_le_nsmul {a b : H} {n : ℕ} (h : a ≼ n • b) {γ : Cardinal.{u}}
    (hγ : γ ≤ κ) (hγn : γ * (n : Cardinal.{u}) ≤ κ) :
    cmul (κ := κ) γ hγ a ≼ cmul (κ := κ) (γ * (n : Cardinal.{u})) hγn b := by
  have hnκ : (n : Cardinal.{u}) ≤ κ :=
    le_trans (le_of_lt Cardinal.natCast_lt_aleph0) (aleph0_le (κ := κ) (H := H))
  refine AddLe.trans (cmul_le_cmul_right h γ hγ) (AddLe.of_eq ?_)
  rw [← cmul_natCast (κ := κ) b n]
  exact cmul_cmul hγ hnκ hγn b

/-- Finite multiples are monotone in the element. -/
theorem nsmul_le_nsmul_right {a b : H} (h : a ≼ b) (n : ℕ) : n • a ≼ n • b := by
  obtain ⟨c, hc⟩ := h
  exact ⟨n • c, by rw [← nsmul_add, hc]⟩

/-- Bounds by finite multiples compose: `a ≼ m b` and `b ≼ n c` give `a ≼ (m n) c`. -/
theorem le_mul_nsmul_of_le_nsmul {a b c : H} {m n : ℕ} (hab : a ≼ m • b) (hbc : b ≼ n • c) :
    a ≼ (m * n) • c :=
  AddLe.trans hab
    (AddLe.trans (nsmul_le_nsmul_right hbc m) (AddLe.of_eq (mul_nsmul' c m n).symm))

/-- A bound `a ≼ n b` may always be taken with `n ≥ 1`. -/
theorem le_succ_nsmul_of_le_nsmul {a b : H} {n : ℕ} (h : a ≼ n • b) : a ≼ (n + 1) • b :=
  AddLe.trans h ⟨b, (succ_nsmul b n).symm⟩

/-- For infinite `γ`, `a ≼ n b` gives `γ a ≼ γ b`: `γ · (n + 1) = γ`. -/
theorem cmul_le_cmul_of_le_nsmul {a b : H} {n : ℕ} (h : a ≼ n • b) {γ : Cardinal.{u}}
    (hγ0 : ℵ₀ ≤ γ) (hγ : γ ≤ κ) : cmul (κ := κ) γ hγ a ≼ cmul (κ := κ) γ hγ b := by
  have hmul : γ * ((n + 1 : ℕ) : Cardinal.{u}) = γ :=
    Cardinal.mul_eq_left hγ0
      ((le_of_lt Cardinal.natCast_lt_aleph0).trans hγ0) (Nat.cast_ne_zero.mpr (by omega))
  exact AddLe.trans
    (cmul_le_cmul_mul_of_le_nsmul (le_succ_nsmul_of_le_nsmul h) hγ (hmul.le.trans hγ))
    (AddLe.of_eq (cmul_congr hmul _ hγ b))

/-! ## Example 2.13: transferring a (faithful) order-unit -/

/-- **Example 2.13**, monoid half (order-units): if `u` is an order-unit and `u ≼ n v` for some
`n ∈ ℕ₀`, then `v` is an order-unit.

Paper proof (left implicit in the paper): `x ≼ κ u ≼ κ (n v) = (κ n) v ≼ κ v`. -/
theorem IsOrderUnit.of_le_nsmul {u v : H} (hu : IsOrderUnit (κ := κ) u) {n : ℕ}
    (huv : u ≼ n • v) : IsOrderUnit (κ := κ) v := fun x =>
  AddLe.trans (hu x)
    (cmul_le_cmul_of_le_nsmul huv (aleph0_le (κ := κ) (H := H)) le_rfl)

/-- **Example 2.13**, monoid half (faithful order-units): if `u` is a faithful order-unit and
`u ≼ n v`, `v ≼ m u` for some `n, m ∈ ℕ₀`, then `v` is a faithful order-unit.

This is the monoid-theoretic reason why, in `V^κ(R)`, the class of every progenerator is a faithful
order-unit (the paper states this without proof).

Paper proof (left implicit in the paper): if `β v ≼ α v` with `α < β ≤ κ` and `β` infinite, then
`β u ≼ β v ≼ α v ≼ (α (m + 1)) u`, and `α (m + 1) < β` — it is finite if `α` is, and equal to `α`
otherwise.  This contradicts the faithfulness of `u`. -/
theorem IsFaithful.of_le_nsmul {u v : H} (hu : IsFaithful (κ := κ) u) {n m : ℕ}
    (huv : u ≼ n • v) (hvu : v ≼ m • u) : IsFaithful (κ := κ) v := by
  refine ⟨hu.1.of_le_nsmul huv, fun α β hα hβ hαβ hβ0 hle => ?_⟩
  set γ : Cardinal.{u} := α * ((m + 1 : ℕ) : Cardinal.{u}) with hγdef
  have hγβ : γ < β := by
    rcases lt_or_ge α ℵ₀ with hfin | hinf
    · exact lt_of_lt_of_le (Cardinal.mul_lt_aleph0 hfin Cardinal.natCast_lt_aleph0) hβ0
    · rw [hγdef, Cardinal.mul_eq_left hinf ((le_of_lt Cardinal.natCast_lt_aleph0).trans hinf)
        (Nat.cast_ne_zero.mpr (by omega))]
      exact hαβ
  have hγ : γ ≤ κ := hγβ.le.trans hβ
  refine hu.2 γ β hγ hβ hγβ hβ0 ?_
  -- `β u ≼ β v ≼ α v ≼ γ u`
  exact AddLe.trans (cmul_le_cmul_of_le_nsmul huv hβ0 hβ)
    (AddLe.trans hle (cmul_le_cmul_mul_of_le_nsmul (le_succ_nsmul_of_le_nsmul hvu) hα hγ))

/-! ## The pieces of the size filtration -/

/-- **The finite pieces of the filtration are all `H_0`**: for a finite cardinal `α`, an element
lies in `H_α` exactly when it lies below some finite multiple of the order-unit.  This is the
paper's "`size(x) = 0` if `x ≤ n u` for some `n ∈ ℕ₀`". -/
theorem mem_part_iff_of_lt_aleph0 {u : H} (hu : IsOrderUnit (κ := κ) u) {α : Cardinal.{u}}
    (hα : α < ℵ₀) {x : H} : x ∈ part (κ := κ) u α ↔ ∃ n : ℕ, x ≼ n • u := by
  have hℵ₀ : (ℵ₀ : Cardinal.{u}) ≤ κ := aleph0_le (κ := κ) (H := H)
  constructor
  · intro hx
    obtain ⟨n, hn, hle⟩ := size_mem_sizeSet hu x
    obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.mp
      (Cardinal.add_lt_aleph0 ((mem_part.mp hx).trans_lt hα) Cardinal.natCast_lt_aleph0)
    refine ⟨k, AddLe.trans hle (AddLe.of_eq ?_)⟩
    rw [← cmul_natCast (κ := κ) u k]
    exact cmul_congr hk _ _ u
  · rintro ⟨n, hn⟩
    have hnκ : (n : Cardinal.{u}) ≤ κ := le_trans (le_of_lt Cardinal.natCast_lt_aleph0) hℵ₀
    have h0 : (0 : Cardinal.{u}) ∈ sizeSet (κ := κ) u x :=
      ⟨n, by rw [zero_add]; exact hnκ, AddLe.trans hn (AddLe.of_eq
        ((cmul_natCast (κ := κ) u n).symm.trans (cmul_congr (zero_add _).symm _ _ u)))⟩
    exact (size_le h0).trans (zero_le : (0 : Cardinal.{u}) ≤ α)

/-- **The infinite pieces of the filtration**: for infinite `α ≤ κ`, an element lies in `H_α`
exactly when it lies below `α u`. -/
theorem mem_part_iff_of_aleph0_le {u : H} (hu : IsOrderUnit (κ := κ) u) {α : Cardinal.{u}}
    (hα0 : ℵ₀ ≤ α) (hα : α ≤ κ) {x : H} :
    x ∈ part (κ := κ) u α ↔ x ≼ cmul (κ := κ) α hα u :=
  ⟨le_cmul_of_size_le hu hα0 hα, size_le_of_le hα⟩

end KMonoid

end KappaMonoid
