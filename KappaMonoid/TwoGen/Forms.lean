/-
**Section 5: forms.**

A *form* `α X₁ + β X₂` records how many copies of each generator a family uses.  `ℕ∞` is exactly
`{0, 1, 2, …, ℵ₀}`, which makes "is this coefficient finite?" decidable — every proof in the section
branches on it — and `Cardinal.ofENat` pushes a coefficient into `Cardinal`.

This file carries the encoding: `ecmul`, `eval`, `Form`, the index type `FormIdx = ℕ ⊕ ℕ` of a
form's slots, the family `familyOfForm` realising a form, its `slots`, and `BraidedForms`.  It also
carries the two facts about generation that the rest of §5 runs on: `exists_form` (every element of
`H` has a form — the sentence opening §5) and `mem_of_divisorClosed_of_generates` (the paper's
parenthetical from Lemma 5.1).
-/
import KappaMonoid.Core.AddOf
import KappaMonoid.Core.OrderUnit
import KappaMonoid.Braiding
import KappaMonoid.ForMathlib.Finprod

universe u v

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

-- The cardinal universe is pinned to `H`'s: `§5` fixes `κ = ℵ₀` and works in a single universe, and
-- leaving `ℵ₀`'s universe to be auto-bound makes two occurrences in one statement refer to
-- *different* universes (trap 5 of `CLAUDE.md`).
variable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]

/-! ## Forms

A *form* `α X₁ + β X₂` records how many copies of each generator a family uses.  `ℕ∞` is exactly
`{0, 1, 2, …, ℵ₀}`, and it makes "is this coefficient finite?" decidable, which every proof in the
section branches on. -/

-- The cardinal universe is pinned to `H`'s: `§5` fixes `κ = ℵ₀` and works in a single universe, and
-- leaving `ℵ₀`'s universe to be auto-bound makes two occurrences in one statement refer to
-- *different* universes (trap 5 of `CLAUDE.md`).
variable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]

/-- The `ℵ₀`-sum of a constant family is `ℵ₀` copies of its value. -/
theorem ksum_const (c : H) :
    KMonoid.ksum (κ := ℵ₀) (fun _ : Idx (ℵ₀ : Cardinal.{u}) => c)
      = ℵ₀∙c := by
  rw [← KMonoid.sumOf_Idx, ← KMonoid.cmul_eq_sumOf]
  exact KMonoid.cmul_congr (mk_Idx (ℵ₀ : Cardinal.{u})) _ le_rfl c

/-- A constant family over a finite index set sums to a finite multiple of its value.  This is the
bookkeeping every block of a braiding needs: the pieces of a braiding partition are `ℵ₀⁻`-small,
hence finite, so each block sum is an honest `n • c`. -/
theorem sumOf_const_finite {ι : Type u} {T : Set ι} (hT : #T < (ℵ₀ : Cardinal.{u})) (c : H) :
    ∃ m : ℕ, #T = (m : Cardinal.{u}) ∧
      KMonoid.sumOf (κ := ℵ₀) hT.le (fun _ : T => c) = m • c := by
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hT
  refine ⟨m, hm, ?_⟩
  rw [← KMonoid.cmul_eq_sumOf hT.le c,
    KMonoid.cmul_congr hm hT.le (le_of_lt Cardinal.natCast_lt_aleph0) c]
  exact KMonoid.cmul_natCast c m

/-- A **form** `α X₁ + β X₂`: a pair of coefficients in `{0, 1, 2, …, ℵ₀}`. -/
abbrev Form : Type := ℕ∞ × ℕ∞

/-- `a` copies of `x`, where `a = ⊤` means `ℵ₀` copies. -/
noncomputable def ecmul (a : ℕ∞) (x : H) : H :=
  KMonoid.cmul (κ := ℵ₀) (Cardinal.ofENat a) (Cardinal.ofENat_le_aleph0 a) x

@[simp] theorem ecmul_top (x : H) : ecmul (⊤ : ℕ∞) x = ℵ₀∙x := by
  simp [ecmul]

/-- The element of `H` represented by a form. -/
noncomputable def eval (x₁ x₂ : H) (F : Form) : H := ecmul F.1 x₁ + ecmul F.2 x₂

@[simp] theorem ecmul_zero (x : H) : ecmul (0 : ℕ∞) x = 0 := by
  rw [ecmul, KMonoid.cmul_congr (by simp : Cardinal.ofENat (0 : ℕ∞) = 0) _ zero_le,
    KMonoid.cmul_zero_cardinal]

@[simp] theorem ecmul_one (x : H) : ecmul (1 : ℕ∞) x = x := by
  rw [ecmul, KMonoid.cmul_congr (by simp : Cardinal.ofENat (1 : ℕ∞) = 1) _
    (le_of_lt Cardinal.one_lt_aleph0), KMonoid.cmul_one]

/-- Every cardinal `≤ ℵ₀` is a coefficient: `ℕ∞` is exactly `{0, 1, 2, …, ℵ₀}`. -/
theorem exists_ofENat_of_le_aleph0 {c : Cardinal.{u}} (h : c ≤ ℵ₀) :
    ∃ a : ℕ∞, Cardinal.ofENat a = c := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · obtain ⟨n, rfl⟩ := Cardinal.lt_aleph0.mp hlt
    exact ⟨(n : ℕ∞), by simp⟩
  · exact ⟨⊤, Cardinal.ofENat_top⟩

/-- A nonzero number of copies of `x` has `x` as a summand. -/
theorem self_addLe_ecmul {a : ℕ∞} (ha : a ≠ 0) (x : H) : x ≼ ecmul a x := by
  have h1 : (1 : Cardinal.{u}) ≤ Cardinal.ofENat a :=
    Cardinal.one_le_iff_ne_zero.mpr (by simpa using ha)
  have h := KMonoid.cmul_le_cmul (κ := ℵ₀) (le_of_lt Cardinal.one_lt_aleph0)
    (Cardinal.ofENat_le_aleph0 a) h1 x
  rwa [KMonoid.cmul_one] at h

/-- A `κ`-submonoid absorbs `ecmul`: any number `≤ ℵ₀` of copies of one of its elements is again a
sum of a family in it. -/
theorem IsKSubmonoid.ecmul_mem {S : Set H} (hS : KMonoid.IsKSubmonoid (ℵ₀ : Cardinal.{u}) S)
    {x : H} (hx : x ∈ S) (a : ℕ∞) : ecmul a x ∈ S := by
  have hmk : #(Idx (Cardinal.ofENat a)) ≤ (ℵ₀ : Cardinal.{u}) :=
    le_of_eq_of_le (mk_Idx _) (Cardinal.ofENat_le_aleph0 a)
  have hrw : ecmul a x
      = KMonoid.sumOf (κ := ℵ₀) hmk (fun _ : Idx (Cardinal.ofENat a) => x) := by
    rw [← KMonoid.cmul_eq_sumOf hmk x, ecmul]
    exact KMonoid.cmul_congr (mk_Idx _).symm _ _ x
  rw [hrw]
  exact hS.sumOf_mem hmk _ fun _ => hx

/-- A form is *infinite* if at least one coefficient is. -/
def Form.IsInfinite (F : Form) : Prop := F.1 = ⊤ ∨ F.2 = ⊤

/-- A form is *finite* otherwise. -/
def Form.IsFinite (F : Form) : Prop := F.1 ≠ ⊤ ∧ F.2 ≠ ⊤

/-- A form is finite exactly when both of its coefficients are. -/
theorem Form.not_isInfinite_iff (F : Form) : ¬ F.IsInfinite ↔ F.IsFinite := by
  simp [Form.IsInfinite, Form.IsFinite, not_or]

/-- **Every element of `H` has a form**, which is the sentence opening §5: "every `y ∈ H` can be
represented as `y = Σ_{k ∈ ℵ₀} y_k` with `y_k` equal to either `x₁` or `x₂`".

Proof: the elements representable by a form are a `κ`-submonoid — an `ℵ₀`-indexed sum of forms is
the form whose coefficients are the cardinal sums, which stay `≤ ℵ₀` because `ℵ₀ · ℵ₀ = ℵ₀`, and
every cardinal `≤ ℵ₀` is a coefficient (`exists_ofENat_of_le_aleph0`) — and it contains `x₁` and
`x₂`, so it contains all of `⟨x₁, x₂⟩ = H`. -/
theorem exists_form (x₁ x₂ : H)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H)) (y : H) :
    ∃ F : Form, eval x₁ x₂ F = y := by
  have hidx : #(Idx (ℵ₀ : Cardinal.{u})) ≤ (ℵ₀ : Cardinal.{u}) := le_of_eq (mk_Idx _)
  have hsub : KMonoid.IsKSubmonoid (ℵ₀ : Cardinal.{u}) {y : H | ∃ F : Form, eval x₁ x₂ F = y} := by
    constructor
    · exact ⟨(0, 0), by rw [eval, ecmul_zero, ecmul_zero, add_zero]⟩
    · intro z hz
      choose F hF using hz
      -- the coefficient sums, and the coefficients they come from
      have hbound : ∀ c : Idx (ℵ₀ : Cardinal.{u}) → ℕ∞,
          Cardinal.sum (fun i => Cardinal.ofENat (c i)) ≤ (ℵ₀ : Cardinal.{u}) := by
        intro c
        refine le_trans (Cardinal.sum_le_sum _ (fun _ => (ℵ₀ : Cardinal.{u}))
          fun i => Cardinal.ofENat_le_aleph0 (c i)) ?_
        rw [Cardinal.sum_const', mk_Idx]
        exact le_of_eq (Cardinal.mul_eq_left le_rfl le_rfl Cardinal.aleph0_ne_zero)
      -- an `ℵ₀`-sum of `ecmul`s is an `ecmul` by the cardinal sum
      have hslot : ∀ (c : Idx (ℵ₀ : Cardinal.{u}) → ℕ∞) (x : H), ∃ a : ℕ∞,
          KMonoid.ksum (κ := ℵ₀) (fun i => ecmul (c i) x) = ecmul a x := by
        intro c x
        obtain ⟨a, ha⟩ := exists_ofENat_of_le_aleph0 (hbound c)
        refine ⟨a, ?_⟩
        simp only [ecmul]
        rw [← KMonoid.sumOf_Idx,
          ← KMonoid.cmul_sumOf_cardinal hidx (fun i => Cardinal.ofENat (c i))
            (fun i => Cardinal.ofENat_le_aleph0 (c i)) (hbound c) x]
        exact KMonoid.cmul_congr ha.symm _ _ x
      obtain ⟨α, hα⟩ := hslot (fun i => (F i).1) x₁
      obtain ⟨β, hβ⟩ := hslot (fun i => (F i).2) x₂
      refine ⟨(α, β), ?_⟩
      rw [show z = fun i => ecmul (F i).1 x₁ + ecmul (F i).2 x₂ from
          funext fun i => (hF i).symm,
        ← KMonoid.sumOf_Idx, KMonoid.sumOf_add hidx, KMonoid.sumOf_Idx, KMonoid.sumOf_Idx,
        hα, hβ, eval]
  refine KMonoid.kclosure_le ?_ hsub (KMonoid.kGenerates_iff.mp hgen y)
  rintro w (rfl | rfl)
  · exact ⟨(1, 0), by rw [eval, ecmul_one, ecmul_zero, add_zero]⟩
  · exact ⟨(0, 1), by rw [eval, ecmul_one, ecmul_zero, zero_add]⟩

/-- The index type of a family in an `ℵ₀`-monoid: `ℕ`, lifted into `Type u` because `BraidingData`
indexes by a type in the cardinal's universe. -/
abbrev Nats : Type u := ULift.{u} ℕ

/-- The index type of the family realising a form: one copy of `ℕ` for the `X₁` slots and one for
the `X₂` slots.

**Two summands, not one.**  Listing the `α` copies of `x₁` first and the `β` copies of `x₂` after
them, all inside a single copy of `ℕ`, is wrong as soon as `α = ℵ₀`: there is then no slot left
for `x₂`, and `sumOf_familyOfForm` would be false — take `H = F_{ℵ₀}`, `x₁ = 0`, `x₂ = 1` and
`F = (ℵ₀, 1)`, where the family is identically `0` but the form evaluates to `1`.  Keeping the two
kinds of slot in two summands of the index type is faithful to the paper (one generator per slot)
and makes the sum split by `sumOf_sumType`. -/
abbrev FormIdx : Type u := Nats.{u} ⊕ Nats.{u}

/-- The family realising a form: the `n`-th `X₁`-slot holds `x₁` while `n < α`, the `n`-th
`X₂`-slot holds `x₂` while `n < β`, and all other slots hold `0`. -/
noncomputable def familyOfForm (x₁ x₂ : H) (F : Form) : FormIdx.{u} → H :=
  Sum.elim (fun n => if ((n.down : ℕ) : ℕ∞) < F.1 then x₁ else 0)
    (fun n => if ((n.down : ℕ) : ℕ∞) < F.2 then x₂ else 0)

/-- `Nats`, the universe-lifted copy of `ℕ`, is countable, -/
theorem mk_nats : #(Nats.{u}) = (ℵ₀ : Cardinal.{u}) := by simp [Nats]

/-- and so may index an `ℵ₀`-sum. -/
theorem mk_nats_le_aleph0 : #(Nats.{u}) ≤ (ℵ₀ : Cardinal.{u}) := le_of_eq mk_nats

/-- The slots of a form — two copies of `ℕ` — are countable, -/
theorem mk_formIdx : #(FormIdx.{u}) = (ℵ₀ : Cardinal.{u}) := by
  rw [FormIdx, Cardinal.mk_sum, mk_nats, Cardinal.lift_id, Cardinal.aleph0_add_aleph0]

/-- and so may index an `ℵ₀`-sum. -/
theorem mk_formIdx_le_aleph0 : #(FormIdx.{u}) ≤ (ℵ₀ : Cardinal.{u}) := le_of_eq mk_formIdx

/-- The slots a coefficient uses: `{n : ℕ | n < α}` has exactly `α` elements, `ℵ₀` when `α = ℵ₀`. -/
theorem mk_slots (α : ℕ∞) :
    #{n : Nats.{u} | ((n.down : ℕ) : ℕ∞) < α} = Cardinal.ofENat α := by
  rcases eq_or_ne α ⊤ with rfl | hα
  · have huniv : {n : Nats.{u} | ((n.down : ℕ) : ℕ∞) < ⊤} = Set.univ :=
      Set.eq_univ_of_forall fun n => WithTop.coe_lt_top (n.down : ℕ)
    rw [huniv, Cardinal.mk_univ, mk_nats, Cardinal.ofENat_top]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, α = (k : ℕ∞) := ⟨α.toNat, (ENat.natCast_toNat hα).symm⟩
    have e : {n : Nats.{u} | ((n.down : ℕ) : ℕ∞) < (k : ℕ∞)} ≃ ULift.{u} (Fin k) :=
      (Equiv.subtypeEquiv Equiv.ulift fun n => by exact_mod_cast Iff.rfl).trans
        (Fin.equivSubtype.symm.trans Equiv.ulift.symm)
    rw [Cardinal.mk_congr e, Cardinal.ofENat_nat]
    simp

/-- The family of a form sums to the element the form represents. -/
theorem sumOf_familyOfForm (x₁ x₂ : H) (F : Form) :
    KMonoid.sumOf (κ := ℵ₀) mk_formIdx_le_aleph0 (familyOfForm x₁ x₂ F) = eval x₁ x₂ F := by
  classical
  have hslot : ∀ (a : ℕ∞) (x : H),
      KMonoid.sumOf (κ := ℵ₀) mk_nats_le_aleph0
          (fun n : Nats.{u} => if ((n.down : ℕ) : ℕ∞) < a then x else 0) = ecmul a x := by
    intro a x
    have h1 : KMonoid.sumOf (κ := ℵ₀) mk_nats_le_aleph0
          (fun n : Nats.{u} => if ((n.down : ℕ) : ℕ∞) < a then x else 0)
        = KMonoid.cmul (κ := ℵ₀) #{n : Nats.{u} | ((n.down : ℕ) : ℕ∞) < a}
            (le_of_eq_of_le (mk_slots a) (Cardinal.ofENat_le_aleph0 a)) x :=
      KMonoid.sumOf_indicator mk_nats_le_aleph0
        (le_of_eq_of_le (mk_slots a) (Cardinal.ofENat_le_aleph0 a)) x _
        (fun i hi => if_pos hi) (fun i hi => if_neg hi)
    rw [h1, ecmul]
    exact KMonoid.cmul_congr (mk_slots a) _ (Cardinal.ofENat_le_aleph0 a) x
  rw [familyOfForm,
    KMonoid.sumOf_sumType mk_nats_le_aleph0 mk_nats_le_aleph0 mk_formIdx_le_aleph0,
    hslot F.1 x₁, hslot F.2 x₂, eval]

/-! ### The slots of a form

Where a form's family can be nonzero.  A finite form uses finitely many slots; an infinite form
uses infinitely many, and — provided the generator involved is nonzero — its family really has
infinite support.  This is the only content of Lemma 5.2(1). -/

/-- The slots a form's family may use. -/
def slots (F : Form) : Set FormIdx.{u} :=
  (Sum.inl '' {n : Nats.{u} | ((n.down : ℕ) : ℕ∞) < F.1}) ∪
    (Sum.inr '' {n : Nats.{u} | ((n.down : ℕ) : ℕ∞) < F.2})

/-- Outside the slots a form prescribes, its family vanishes. -/
theorem familyOfForm_eq_zero_of_notMem_slots (x₁ x₂ : H) {F : Form} {i : FormIdx.{u}}
    (hi : i ∉ slots.{u} F) : familyOfForm x₁ x₂ F i = 0 := by
  rcases i with n | n
  · have hn : ¬ (((n.down : ℕ) : ℕ∞) < F.1) := fun h => hi (Or.inl ⟨n, h, rfl⟩)
    show (if ((n.down : ℕ) : ℕ∞) < F.1 then x₁ else 0) = 0
    rw [if_neg hn]
  · have hn : ¬ (((n.down : ℕ) : ℕ∞) < F.2) := fun h => hi (Or.inr ⟨n, h, rfl⟩)
    show (if ((n.down : ℕ) : ℕ∞) < F.2 then x₂ else 0) = 0
    rw [if_neg hn]

/-- A finite form uses only finitely many slots. -/
theorem mk_slots_lt {F : Form} (hF : F.IsFinite) : #(slots.{u} F) < (ℵ₀ : Cardinal.{u}) := by
  rw [Cardinal.lt_aleph0_iff_set_finite]
  have hfin : ∀ a : ℕ∞, a ≠ ⊤ → {n : Nats.{u} | ((n.down : ℕ) : ℕ∞) < a}.Finite := by
    intro a ha
    rw [← Cardinal.lt_aleph0_iff_set_finite, mk_slots a, Cardinal.ofENat_lt_aleph0]
    exact Ne.lt_top ha
  exact ((hfin F.1 hF.1).image _).union ((hfin F.2 hF.2).image _)

/-- An infinite form's family has infinite support, as soon as both generators are nonzero. -/
theorem infinite_support_familyOfForm (x₁ x₂ : H) {F : Form} (hF : F.IsInfinite)
    (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) :
    (Function.support (familyOfForm x₁ x₂ F)).Infinite := by
  rcases hF with h | h
  · refine Set.infinite_of_injective_forall_mem
      (f := fun n : Nats.{u} => (Sum.inl n : FormIdx.{u})) (fun a b hab => by simpa using hab) ?_
    intro n
    show familyOfForm x₁ x₂ F (Sum.inl n) ≠ 0
    show (if ((n.down : ℕ) : ℕ∞) < F.1 then x₁ else 0) ≠ 0
    rw [if_pos (h ▸ WithTop.coe_lt_top (n.down : ℕ))]
    exact h₁
  · refine Set.infinite_of_injective_forall_mem
      (f := fun n : Nats.{u} => (Sum.inr n : FormIdx.{u})) (fun a b hab => by simpa using hab) ?_
    intro n
    show familyOfForm x₁ x₂ F (Sum.inr n) ≠ 0
    show (if ((n.down : ℕ) : ℕ∞) < F.2 then x₂ else 0) ≠ 0
    rw [if_pos (h ▸ WithTop.coe_lt_top (n.down : ℕ))]
    exact h₂

/-- `y` **has a finite form**. -/
def HasFiniteForm (x₁ x₂ y : H) : Prop := ∃ F : Form, F.IsFinite ∧ eval x₁ x₂ F = y

/-- `y` **has an infinite form**. -/
def HasInfiniteForm (x₁ x₂ y : H) : Prop := ∃ F : Form, F.IsInfinite ∧ eval x₁ x₂ F = y

/-- The condition (iii) of Theorem 5.3: no element of `H` has both a finite and an infinite form.
This is the hypothesis that most of Lemma 5.2 runs on. -/
def NoMixedForms (x₁ x₂ : H) : Prop :=
  ∀ y : H, ¬ (HasFiniteForm x₁ x₂ y ∧ HasInfiniteForm x₁ x₂ y)

/-- Two forms are **braided over `add (x₁ + x₂)`** when their families are.

The families take values in `H`; braiding is a statement about the `ℵ₀⁻`-monoid `add (x₁ + x₂)`,
so the members must be produced there.  `hmem` is that side condition, discharged in practice by
`KMonoid.addOf_isSaturated` from `Core/AddOf.lean`. -/
def BraidedForms (x₁ x₂ : H) (F G : Form)
    (hF : ∀ n, familyOfForm x₁ x₂ F n ∈ add((x₁ + x₂)))
    (hG : ∀ n, familyOfForm x₁ x₂ G n ∈ add((x₁ + x₂))) : Prop :=

  IsBraided ℵ₀ (ι := FormIdx.{u})
    (fun n => (⟨familyOfForm x₁ x₂ F n, hF n⟩ : ↥(add((x₁ + x₂)))))
    (fun n => (⟨familyOfForm x₁ x₂ G n, hG n⟩ : ↥(add((x₁ + x₂)))))

end TwoGen

end KappaMonoid
