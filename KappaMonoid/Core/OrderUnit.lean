/-
Section 2.2 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

Order-units: Definition 2.11 (the algebraic preorder), Definition 2.12 (order-units and faithful
order-units), the `size` function with the filtration it induces, and Lemma 2.14.

The relation of Definition 2.11 is written `≼` rather than `≤`.  It is reflexive and transitive
but not antisymmetric — `not_antisymm` reproduces the paper's counterexample — so none of
Mathlib's canonically-ordered monoid classes applies.
-/
import KappaMonoid.Core

universe u v

open Cardinal

namespace KappaMonoid

/-! ## Definition 2.11: the algebraic preorder -/

/-- **Definition 2.11**: `a ≼ b` if `a + c = b` for some `c`.  Stated for an arbitrary
commutative monoid; the paper introduces it for a `κ`-monoid. -/
def AddLe {M : Type v} [AddCommMonoid M] (a b : M) : Prop := ∃ c : M, a + c = b

@[inherit_doc] scoped infix:50 " ≼ " => AddLe

namespace AddLe

variable {M : Type v} [AddCommMonoid M]

@[refl] theorem refl (a : M) : a ≼ a := ⟨0, add_zero a⟩

theorem trans {a b c : M} (hab : a ≼ b) (hbc : b ≼ c) : a ≼ c := by
  obtain ⟨u, hu⟩ := hab
  obtain ⟨v, hv⟩ := hbc
  exact ⟨u + v, by rw [← add_assoc, hu, hv]⟩

theorem of_eq {a b : M} (h : a = b) : a ≼ b := h ▸ refl a

theorem zero_le (a : M) : (0 : M) ≼ a := ⟨a, zero_add a⟩

theorem le_add_right (a b : M) : a ≼ a + b := ⟨b, rfl⟩

theorem add_le_add {a b c d : M} (hac : a ≼ c) (hbd : b ≼ d) : a + b ≼ c + d := by
  obtain ⟨w, hw⟩ := hac
  obtain ⟨v, hv⟩ := hbd
  refine ⟨w + v, ?_⟩
  rw [show a + b + (w + v) = (a + w) + (b + v) by
    rw [add_assoc, add_assoc, add_comm b (w + v), add_assoc, add_comm v b], hw, hv]

end AddLe

/-- The preorder of Definition 2.11 is not antisymmetric: the paper's example is `ℕ₀` modulo
`n ∼ n + 2`, i.e. `ZMod 2`, where `0 ≼ 1` and `1 ≼ 0` but `0 ≠ 1`. -/
theorem not_antisymm :
    ¬ ∀ (M : Type) (_ : AddCommMonoid M) (a b : M), a ≼ b → b ≼ a → a = b := fun hcon =>
  absurd (hcon (ZMod 2) inferInstance 0 1 ⟨1, by decide⟩ ⟨1, by decide⟩) (by decide)

namespace KMonoid

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-- Sums respect `≼` termwise. -/
theorem sumOf_le_sumOf {ι : Type u} (h : #ι ≤ κ) {x y : ι → H} (hxy : ∀ i, x i ≼ y i) :
    sumOf (κ := κ) h x ≼ sumOf (κ := κ) h y := by
  choose c hc using hxy
  exact ⟨sumOf (κ := κ) h c, by rw [← sumOf_add h x c, funext hc]⟩

/-- Cardinal scalar multiplication is monotone in the cardinal. -/
theorem cmul_le_cmul {γ α : Cardinal.{u}} (hγ : γ ≤ κ) (hα : α ≤ κ) (h : γ ≤ α) (u : H) :
    cmul (κ := κ) γ hγ u ≼ cmul (κ := κ) α hα u := by
  obtain ⟨δ, hδ⟩ := exists_add_of_le h
  have hsum : γ + δ ≤ κ := hδ ▸ hα
  have hδκ : δ ≤ κ := le_trans (self_le_add_left δ γ) hsum
  exact ⟨cmul (κ := κ) δ hδκ u,
    (cmul_add hγ hδκ hsum u).symm.trans (cmul_congr hδ.symm hsum hα u)⟩

/-! ## Definition 2.12: order-units -/

/-- **Definition 2.12(1)**: `u` is an *order-unit* if `x ≼ κ u` for every `x ∈ H`. -/
def IsOrderUnit (u : H) : Prop := ∀ x : H, x ≼ cmul (κ := κ) κ le_rfl u

/-- **Definition 2.12(2)**: an order-unit `u` is *faithful* if `β u ⋠ α u` for all cardinals
`α < β ≤ κ` with `β` infinite. -/
def IsFaithful (u : H) : Prop :=
  IsOrderUnit (κ := κ) u ∧ ∀ (α β : Cardinal.{u}) (hα : α ≤ κ) (hβ : β ≤ κ), α < β → ℵ₀ ≤ β →
    ¬ (cmul (κ := κ) β hβ u ≼ cmul (κ := κ) α hα u)

/-! ## Lemma 2.14 -/

/-- **Lemma 2.14**: if `t = κ u + l` then `t = κ u`.

Paper proof: `l ≼ κu` gives `l + l' = κu`, hence `l + κu = κu` by Lemma 2.8(2), hence
`t = κu + l = κu`. -/
theorem eq_cmul_top_of_add {u : H} (hu : IsOrderUnit (κ := κ) u) (l : H) {t : H}
    (ht : t = cmul (κ := κ) κ le_rfl u + l) : t = cmul (κ := κ) κ le_rfl u := by
  obtain ⟨l', hl'⟩ := hu l
  rw [ht, add_comm, add_cmul_top_eq hl']

/-! ## The size of an element

`size u x` is the least cardinal `α` with `x ≼ (α + n) u` for some `n ∈ ℕ`; the paper's
"cardinals modulo finite cardinals" is encoded by that `+ n`.  `size` depends on the choice of
order-unit. -/

/-- The set of cardinals `α` with `x ≼ (α + n) u` for some `n : ℕ`. -/
def sizeSet (u x : H) : Set Cardinal.{u} :=
  {α | ∃ n : ℕ, ∃ hn : α + (n : Cardinal.{u}) ≤ κ,
    x ≼ cmul (κ := κ) (α + (n : Cardinal.{u})) hn u}

theorem add_zero_cast (α : Cardinal.{u}) : α + ((0 : ℕ) : Cardinal.{u}) = α := by
  rw [Nat.cast_zero, add_zero]

/-- `κ` is always available as a bound, for an order-unit. -/
theorem top_mem_sizeSet {u : H} (hu : IsOrderUnit (κ := κ) u) (x : H) :
    κ ∈ sizeSet (κ := κ) u x :=
  ⟨0, le_of_eq_of_le (add_zero_cast κ) le_rfl,
    AddLe.trans (hu x) (AddLe.of_eq (cmul_congr (add_zero_cast κ).symm le_rfl _ u))⟩

/-- **The size of `x`** with respect to the order-unit `u`. -/
noncomputable def size (u x : H) : Cardinal.{u} := sInf (sizeSet (κ := κ) u x)

theorem size_le {u x : H} {α : Cardinal.{u}} (h : α ∈ sizeSet (κ := κ) u x) :
    size (κ := κ) u x ≤ α := csInf_le' h

theorem size_mem_sizeSet {u : H} (hu : IsOrderUnit (κ := κ) u) (x : H) :
    size (κ := κ) u x ∈ sizeSet (κ := κ) u x :=
  csInf_mem ⟨κ, top_mem_sizeSet hu x⟩

theorem size_le_top {u : H} (hu : IsOrderUnit (κ := κ) u) (x : H) : size (κ := κ) u x ≤ κ :=
  size_le (top_mem_sizeSet hu x)

/-- If `x ≼ α u` then `size x ≤ α`. -/
theorem size_le_of_le {u x : H} {α : Cardinal.{u}} (hα : α ≤ κ)
    (h : x ≼ cmul (κ := κ) α hα u) : size (κ := κ) u x ≤ α :=
  size_le ⟨0, le_of_eq_of_le (add_zero_cast α) hα,
    AddLe.trans h (AddLe.of_eq (cmul_congr (add_zero_cast α).symm hα _ u))⟩

/-- For an infinite bound the `+ n` may be dropped: `size x ≤ α` with `α` infinite gives
`x ≼ α u`. -/
theorem le_cmul_of_size_le {u : H} (hu : IsOrderUnit (κ := κ) u) {x : H} {α : Cardinal.{u}}
    (hα0 : ℵ₀ ≤ α) (hα : α ≤ κ) (h : size (κ := κ) u x ≤ α) : x ≼ cmul (κ := κ) α hα u := by
  obtain ⟨n, hn, hx⟩ := size_mem_sizeSet hu x
  refine AddLe.trans hx (cmul_le_cmul hn hα ?_ u)
  exact (add_le_add h
    (le_of_lt (lt_of_lt_of_le (Cardinal.natCast_lt_aleph0) hα0))).trans
    (le_of_eq (Cardinal.add_eq_left hα0 le_rfl))

/-! ## The filtration by size -/

/-- `H_α = {x : size x ≤ α}`, the paper's filtration `H_0 ⊆ H_{ℵ₀} ⊆ H_{ℵ₁} ⊆ ⋯`. -/
def part (u : H) (α : Cardinal.{u}) : Set H := {x | size (κ := κ) u x ≤ α}

theorem mem_part {u : H} {α : Cardinal.{u}} {x : H} :
    x ∈ part (κ := κ) u α ↔ size (κ := κ) u x ≤ α := Iff.rfl

/-- The filtration is increasing. -/
theorem part_mono {u : H} {α β : Cardinal.{u}} (h : α ≤ β) :
    part (κ := κ) u α ⊆ part (κ := κ) u β := fun _ hx => hx.trans h

/-- The whole monoid is the top piece of the filtration. -/
theorem part_top {u : H} (hu : IsOrderUnit (κ := κ) u) : part (κ := κ) u κ = Set.univ :=
  Set.eq_univ_of_forall fun x => size_le_top hu x

theorem zero_mem_part {u : H} (hu : IsOrderUnit (κ := κ) u) (α : Cardinal.{u}) :
    (0 : H) ∈ part (κ := κ) u α :=
  le_trans (size_le_of_le (κ := κ) (u := u) (zero_le' : (0 : Cardinal.{u}) ≤ κ)
    (AddLe.zero_le _)) (zero_le' : (0 : Cardinal.{u}) ≤ α)

/-- **`H_α` is closed under sums of at most `α` many of its elements**, for infinite `α ≤ κ`;
together with `zero_mem_part` this says that `H_α` is an `α`-submonoid.

Paper proof: if `x_i ≼ (α + n_i) u` for `i ∈ I` with `|I| ≤ α`, then `Σ x_i ≼ (Σ_i α) u` by
Lemma 2.7(2), and `Σ_{i ∈ I} α = |I| · α ≤ α · α = α`. -/
theorem sumOf_mem_part {u : H} (hu : IsOrderUnit (κ := κ) u) {α : Cardinal.{u}} (hα0 : ℵ₀ ≤ α)
    (hα : α ≤ κ) {ι : Type u} (hι : #ι ≤ α) (x : ι → H) (hx : ∀ i, x i ∈ part (κ := κ) u α) :
    sumOf (κ := κ) (hι.trans hα) x ∈ part (κ := κ) u α := by
  have hval : (Cardinal.sum fun _ : ι => α) ≤ α := by
    rw [Cardinal.sum_const']
    exact (mul_le_mul' hι le_rfl).trans (le_of_eq (Cardinal.mul_eq_self hα0))
  have hconst : (Cardinal.sum fun _ : ι => α) ≤ κ := hval.trans hα
  have hsum : sumOf (κ := κ) (hι.trans hα) x
      ≼ sumOf (κ := κ) (hι.trans hα) (fun _ => cmul (κ := κ) α hα u) :=
    sumOf_le_sumOf _ fun i => le_cmul_of_size_le hu hα0 hα (hx i)
  have hcm : sumOf (κ := κ) (hι.trans hα) (fun _ : ι => cmul (κ := κ) α hα u)
      = cmul (κ := κ) (Cardinal.sum fun _ : ι => α) hconst u :=
    (cmul_sumOf_cardinal (hι.trans hα) (fun _ => α) (fun _ => hα) hconst u).symm
  exact size_le_of_le hα
    (AddLe.trans (AddLe.trans hsum (AddLe.of_eq hcm)) (cmul_le_cmul hconst hα hval u))

/-! ## Faithfulness and the filtration -/

/-- For a faithful order-unit, `size (β u) = β` for every infinite `β ≤ κ`. -/
theorem size_cmul {u : H} (hu : IsFaithful (κ := κ) u) {β : Cardinal.{u}} (hβ0 : ℵ₀ ≤ β)
    (hβ : β ≤ κ) : size (κ := κ) u (cmul (κ := κ) β hβ u) = β := by
  refine le_antisymm (size_le_of_le hβ (AddLe.refl _)) ?_
  by_contra hcon
  replace hcon : size (κ := κ) u (cmul (κ := κ) β hβ u) < β := not_le.mp hcon
  obtain ⟨n, hn, hle⟩ := size_mem_sizeSet hu.1 (cmul (κ := κ) β hβ u)
  refine hu.2 (size (κ := κ) u (cmul (κ := κ) β hβ u) + (n : Cardinal.{u})) β hn hβ ?_ hβ0 hle
  rcases lt_or_ge (size (κ := κ) u (cmul (κ := κ) β hβ u)) ℵ₀ with hfin | hinf
  · exact lt_of_lt_of_le (Cardinal.add_lt_aleph0 hfin (Cardinal.natCast_lt_aleph0)) hβ0
  · rw [Cardinal.add_eq_left hinf
      (le_of_lt (lt_of_lt_of_le (Cardinal.natCast_lt_aleph0) hinf))]
    exact hcon

/-- **The order-unit `u` is faithful exactly when every inclusion in its filtration is proper.**
This is the characterisation stated in §2.2 after the definition of `size`. -/
theorem isFaithful_iff {u : H} (hu : IsOrderUnit (κ := κ) u) :
    IsFaithful (κ := κ) u ↔
      ∀ (α β : Cardinal.{u}), α < β → β ≤ κ → ℵ₀ ≤ β →
        part (κ := κ) u α ⊂ part (κ := κ) u β := by
  constructor
  · intro hfaith α β hαβ hβ hβ0
    refine ⟨part_mono (le_of_lt hαβ), fun hsub => ?_⟩
    -- `β u` lies in `H_β` but not in `H_α`
    have hmem : cmul (κ := κ) β hβ u ∈ part (κ := κ) u β :=
      le_of_eq (size_cmul hfaith hβ0 hβ)
    have := hsub hmem
    rw [mem_part, size_cmul hfaith hβ0 hβ] at this
    exact absurd this (not_le_of_gt hαβ)
  · intro hproper
    refine ⟨hu, fun α β hα hβ hαβ hβ0 hle => ?_⟩
    -- if `β u ≼ α u` then `H_β ⊆ H_α`, so the inclusion `H_α ⊆ H_β` is not proper
    have hsub : part (κ := κ) u β ⊆ part (κ := κ) u α := fun x hx =>
      size_le_of_le hα (AddLe.trans (le_cmul_of_size_le hu hβ0 hβ hx) hle)
    exact absurd (Set.Subset.antisymm (hproper α β hαβ hβ hβ0).1 hsub)
      (hproper α β hαβ hβ hβ0).ne

end KMonoid

end KappaMonoid
