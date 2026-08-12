/-
**Scaffolding for Section 5** of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*:

*Realization to hereditary rings for two-generated `ℵ₀`-monoids.*

Every proof here is `sorry`.  The file is deliberately **not** imported by `KappaMonoid.lean`, so
`lake build` continues to check a `sorry`-free development; build it on its own with

    lake build KappaMonoid.Section5

Section 5 classifies the non-cyclic `ℵ₀`-monoids on two generators that arise as `V^{ℵ₀}(R)` for
a hereditary ring.  It is written throughout in terms of *forms* `α X₁ + β X₂` with coefficients
in `{0, 1, 2, …, ℵ₀}`, encoded here as `ℕ∞` and pushed into `Cardinal` by `Cardinal.ofENat`.

Two things to know before starting:

* Lemma 5.1 and both directions of Theorem 5.3 go through Corollary 4.7(1), which is still `sorry`
  in `KappaMonoid/Section4.lean` and rests on axiom A5.  Nothing downstream of them closes first.
* Proposition 5.4 needs trace ideals, which Mathlib does not have.  They are developed here from
  scratch rather than assumed — the two facts involved are elementary.

See `SECTION5-PLAN.md`.
-/
import KappaMonoid.Section4
import Mathlib.LinearAlgebra.Projection

universe u v

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

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
      = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl c := by
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

/-- A `κ`-homomorphism commutes with `cmul`: both sides are the sum of the constant family. -/
theorem map_cmul_of_isKHom {K : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) K] {g : H → K}
    (hg : KMonoid.IsKHom (ℵ₀ : Cardinal.{u}) g) {α : Cardinal.{u}} (hα : α ≤ ℵ₀) (x : H) :
    g (KMonoid.cmul (κ := ℵ₀) α hα x) = KMonoid.cmul (κ := ℵ₀) α hα (g x) := by
  have hmk : #(Idx α) ≤ (ℵ₀ : Cardinal.{u}) := le_of_eq_of_le (mk_Idx α) hα
  have h1 : KMonoid.cmul (κ := ℵ₀) α hα x = KMonoid.sumOf (κ := ℵ₀) hmk (fun _ : Idx α => x) :=
    (KMonoid.cmul_congr (mk_Idx α).symm hα hmk x).trans (KMonoid.cmul_eq_sumOf hmk x)
  have h2 : KMonoid.cmul (κ := ℵ₀) α hα (g x)
      = KMonoid.sumOf (κ := ℵ₀) hmk (fun _ : Idx α => g x) :=
    (KMonoid.cmul_congr (mk_Idx α).symm hα hmk (g x)).trans (KMonoid.cmul_eq_sumOf hmk (g x))
  rw [h1, h2, hg.map_sumOf hmk (fun _ : Idx α => x)]
  rfl

/-- A **form** `α X₁ + β X₂`: a pair of coefficients in `{0, 1, 2, …, ℵ₀}`. -/
abbrev Form : Type := ℕ∞ × ℕ∞

/-- `a` copies of `x`, where `a = ⊤` means `ℵ₀` copies. -/
noncomputable def ecmul (a : ℕ∞) (x : H) : H :=
  KMonoid.cmul (κ := ℵ₀) (Cardinal.ofENat a) (Cardinal.ofENat_le_aleph0 a) x

@[simp] theorem ecmul_top (x : H) : ecmul (⊤ : ℕ∞) x = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x := by
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

**This corrects the scaffold.**  Listing the `α` copies of `x₁` first and the `β` copies of `x₂`
after them, all inside a single copy of `ℕ`, is wrong as soon as `α = ℵ₀`: there is then no slot
left for `x₂`, and `sumOf_familyOfForm` is false — take `H = F_{ℵ₀}`, `x₁ = 0`, `x₂ = 1` and
`F = (ℵ₀, 1)`, where the family is identically `0` but the form evaluates to `1`.  Keeping the two
kinds of slot in two summands of the index type is faithful to the paper (one generator per slot)
and makes the sum split by `sumOf_sumType`. -/
abbrev FormIdx : Type u := Nats.{u} ⊕ Nats.{u}

/-- The family realising a form: the `n`-th `X₁`-slot holds `x₁` while `n < α`, the `n`-th
`X₂`-slot holds `x₂` while `n < β`, and all other slots hold `0`. -/
noncomputable def familyOfForm (x₁ x₂ : H) (F : Form) : FormIdx.{u} → H :=
  Sum.elim (fun n => if ((n.down : ℕ) : ℕ∞) < F.1 then x₁ else 0)
    (fun n => if ((n.down : ℕ) : ℕ∞) < F.2 then x₂ else 0)

theorem mk_nats : #(Nats.{u}) = (ℵ₀ : Cardinal.{u}) := by simp [Nats]

theorem mk_nats_le_aleph0 : #(Nats.{u}) ≤ (ℵ₀ : Cardinal.{u}) := le_of_eq mk_nats

theorem mk_formIdx : #(FormIdx.{u}) = (ℵ₀ : Cardinal.{u}) := by
  rw [FormIdx, Cardinal.mk_sum, mk_nats, Cardinal.lift_id, Cardinal.aleph0_add_aleph0]

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
`KMonoid.addOf_isSaturated` from `Section4.lean`. -/
def BraidedForms (x₁ x₂ : H) (F G : Form)
    (hF : ∀ n, familyOfForm x₁ x₂ F n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hG : ∀ n, familyOfForm x₁ x₂ G n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) : Prop :=
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  IsBraided ℵ₀ (ι := FormIdx.{u})
    (fun n => (⟨familyOfForm x₁ x₂ F n, hF n⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
    (fun n => (⟨familyOfForm x₁ x₂ G n, hG n⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))

/-! ## Lemma 5.1

If `H ≅ V^{ℵ₀}(R)` for a ring whose projectives are direct sums of finitely generated modules,
then `x₁` and `x₂` are classes of finitely generated modules, `H` is braided over `add (x₁ + x₂)`,
and `V(R) ≅ add (x₁ + x₂) = ⟨x₁, x₂⟩`. -/

/-- **The paper's parenthetical, isolated.**

If a *divisor-closed* subset `S` generates `H` as an `ℵ₀`-monoid and `H` is not cyclic, then both
generators lie in `S`.  Otherwise, say `x₁ ∉ S`: every `y ∈ S` has a form (`exists_form`) whose
`X₁`-coefficient must vanish — else `x₁ ≼ y` would put `x₁` in `S` — so `S ⊆ ⟨x₂⟩` and
`H = ⟨S⟩ = ⟨x₂⟩` is cyclic.

Lemma 5.1 uses it with `S = e⁻¹(V(R))`, and the hereditary half of Proposition 5.4 with
`S = V(R)` itself, to see that the two generators are finitely generated. -/
theorem mem_of_divisorClosed_of_generates (x₁ x₂ : H) {S : Set H}
    (hSsat : ∀ a ∈ S, ∀ b c : H, a = b + c → b ∈ S)
    (hSgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) S)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x} : Set H)) :
    x₁ ∈ S ∧ x₂ ∈ S := by
  have key : ∀ a b : H, KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({a, b} : Set H) → a ∈ S := by
    intro a b hab
    by_contra haS
    -- otherwise every element of `S` is a multiple of `b` alone
    have hsub : S ⊆ KMonoid.kclosure (ℵ₀ : Cardinal.{u}) ({b} : Set H) := by
      intro y hy
      obtain ⟨F, hF⟩ := exists_form a b hab y
      have hα : F.1 = 0 := by
        by_contra hne
        obtain ⟨c, hc⟩ := self_addLe_ecmul hne a
        exact haS (hSsat y hy a (c + ecmul F.2 b)
          (by rw [← hF, eval, ← hc, add_assoc]))
      rw [← hF, eval, hα, ecmul_zero, zero_add]
      exact IsKSubmonoid.ecmul_mem
        (S := KMonoid.kclosure (ℵ₀ : Cardinal.{u}) ({b} : Set H))
        (KMonoid.isKSubmonoid_kclosure _ _) (KMonoid.subset_kclosure rfl) F.2
    refine hnoncyclic b (Set.eq_univ_of_univ_subset ?_)
    rw [← hSgen]
    exact KMonoid.kclosure_le hsub (KMonoid.isKSubmonoid_kclosure _ _)
  exact ⟨key x₁ x₂ hgen, key x₂ x₁ (by rwa [Set.pair_comm])⟩

section Lemma51

variable (R : Type u) [Ring R]

/-- **Lemma 5.1**: two generators of `V^{ℵ₀}(R)` force braidedness over `add (x₁ + x₂)`.

Follows from `corollary_4_5_three` and `corollary_4_7_one_backward`.  The step needing care is
that *both* `x₁` and `x₂` must arise from finitely generated modules: otherwise `V(R)` would be
cyclic, hence so would `V^{ℵ₀}(R)`, contradicting non-cyclicity.  That is where the non-cyclicity
hypothesis first bites. -/
theorem lemma_5_1 (hfg : EveryProjectiveIsSumOfFG R) (x₁ x₂ : H)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H))
    (e : H → (projClass R ℵ₀ le_rfl).carrier)
    (hhom : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl; KMonoid.IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) :
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
    IsBraidedOver ℵ₀ ℵ₀ ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) H le_rfl (fun y => (y : H)) := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    ((projClass R ℵ₀ le_rfl).lambdaSmallPart_isLSubset le_rfl ℵ₀ Cardinal.isRegular_aleph0 le_rfl)
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  -- Corollary 4.5(3): `V^{ℵ₀}(R)` is braided over `V(R)`, the `ℵ₀⁻`-small classes
  have hbrV := (corollary_4_5_three R ℵ₀ le_rfl hfg).1
  -- `S = e⁻¹(V(R))` is the set of elements of `H` corresponding to finitely generated modules
  set S : Set H := e ⁻¹' ((projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀) with hSdef
  have hWsub := (projClass R ℵ₀ le_rfl).lambdaSmallPart_isLSubset le_rfl ℵ₀
    Cardinal.isRegular_aleph0 le_rfl
  have h0S : (0 : H) ∈ S := by
    show e 0 ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀
    rw [hhom.1]
    exact hWsub.zero_mem
  -- `V(R)` is closed under binary sums: `+` is a two-element `ℵ₀⁻`-sum
  have hWadd : ∀ p q : (projClass R ℵ₀ le_rfl).carrier,
      p ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ →
      q ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ →
      p + q ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ := by
    intro p q hp hq
    have hUB : #(ULift.{u} Bool) < (ℵ₀ : Cardinal.{u}) :=
      Cardinal.lt_aleph0_iff_finite.mpr inferInstance
    -- ascribe the type: `IsLambdaSmall` unfolds to a `∀`, so an unascribed `have` over-applies
    have hmem : KMonoid.sumOf (κ := ℵ₀) (hUB.le.trans le_rfl)
        (fun t : ULift.{u} Bool => if t.down then p else q)
          ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ :=
      hWsub.sumOf_mem hUB _ (by rintro ⟨(_ | _)⟩ <;> simpa)
    rwa [KMonoid.sumOf_two p q (hUB.le.trans le_rfl)] at hmem
  have haddS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := by
    intro a ha b hb
    show e (a + b) ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀
    rw [KMonoid.IsKHom.map_add hhom]
    exact hWadd _ _ ha hb
  -- `S` is divisor-closed, because `V(R)` is (a summand of a f.g. module is f.g.)
  have hSsat : ∀ a ∈ S, ∀ b c : H, a = b + c → b ∈ S := by
    intro a ha b c habc
    exact (projClass R ℵ₀ le_rfl).lambdaSmallPart_summand le_rfl ℵ₀ (e a) ha (e b)
      ⟨e c, by rw [← KMonoid.IsKHom.map_add hhom, ← habc]⟩
  -- and `S` generates `H`, because `V(R)` generates `V^{ℵ₀}(R)`
  have hSgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) S := by
    refine KMonoid.kGenerates_iff.mpr fun h => ?_
    obtain ⟨z, hz⟩ := hbrV.generates (e h)
    choose w hw using fun i => hbij.2 ((z i : (projClass R ℵ₀ le_rfl).carrier))
    refine (KMonoid.mem_kclosure_iff (S := S) h0S h).mpr ⟨w, fun i => ?_, hbij.1 ?_⟩
    · show e (w i) ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀
      rw [hw i]
      exact (z i).2
    · rw [hz, hhom.2 w]
      exact congrArg _ (funext fun i => (hw i).symm)
  -- **the paper's parenthetical**: both generators lie in `S`, else `H` would be cyclic
  obtain ⟨hx₁S, hx₂S⟩ :=
    mem_of_divisorClosed_of_generates x₁ x₂ hSsat hSgen hgen hnoncyclic
  -- hence `add (x₁ + x₂) ⊆ S`: it is generated by a divisor-closed set containing `x₁ + x₂`
  have hnsmulS : ∀ (n : ℕ) (a : H), a ∈ S → n • a ∈ S := by
    intro n a ha
    induction n with
    | zero => rwa [zero_nsmul]
    | succ p hp => rw [succ_nsmul]; exact haddS _ hp _ ha
  have hTS : ∀ a ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂),
      e a ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ := by
    rintro a ⟨z, n, hzn⟩
    refine hSsat _ ?_ a z hzn.symm
    rw [KMonoid.cmul_natCast]
    exact hnsmulS n _ (haddS _ hx₁S _ hx₂S)
  -- `add (x₁ + x₂)` still generates `H`, since it contains both generators
  have hx₁T : x₁ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  have hTgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) (KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hgen]
    refine KMonoid.kclosure_le ?_ (KMonoid.isKSubmonoid_kclosure _ _)
    rintro w (rfl | rfl)
    · exact KMonoid.subset_kclosure hx₁T
    · exact KMonoid.subset_kclosure hx₂T
  exact IsBraidedOver.of_kIso_subset Cardinal.isRegular_aleph0 hWsub
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)) hbrV hhom hbij hTS
    (KMonoid.addOf_isSaturated (x₁ + x₂)) hTgen

end Lemma51

/-! ## Lemma 5.2 (`easyfactlemma1`)

Five basic facts about forms and braiding.  Parts (1), (2) and (5) are cheap; (3) is the longest
proof in the section and (4) is its counterpart for incomparable generators. -/

section Lemma52

variable (x₁ x₂ : H)

/-- In the setting of §5 the generators are nonzero: a zero generator could be dropped, making `H`
cyclic.  This is what supplies the non-degeneracy hypotheses of Lemma 5.2(1). -/
theorem ne_zero_of_not_cyclic (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (hnc : ∀ x : H, ¬ KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x} : Set H)) :
    x₁ ≠ 0 ∧ x₂ ≠ 0 := by
  have key : ∀ a b : H, a = 0 → KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({a, b} : Set H) →
      KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({b} : Set H) := by
    intro a b ha hab
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hab]
    refine KMonoid.kclosure_le (fun y hy => ?_) (KMonoid.isKSubmonoid_kclosure _ _)
    rcases hy with rfl | hy
    · rw [ha]
      exact (KMonoid.isKSubmonoid_kclosure (ℵ₀ : Cardinal.{u}) ({b} : Set H)).zero_mem
    · exact KMonoid.subset_kclosure hy
  refine ⟨fun h => hnc x₂ (key x₁ x₂ h hgen), fun h => hnc x₁ (key x₂ x₁ h ?_)⟩
  rwa [Set.pair_comm]

/-- `add (x₁ + x₂)` is reduced: it is a submonoid of a `κ`-monoid, and those are reduced by
Lemma 2.8(1). -/
theorem isConical_addOf :
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
    IsConical ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  exact LMonoid.isConical_of_injective (lam := (ℵ₀ : Cardinal.{u})) (κ := (ℵ₀ : Cardinal.{u}))
    (fun y : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) => (y : H)) Subtype.val_injective rfl
    (fun _ _ => rfl)

/-- Inside `add (x₁ + x₂)` a form's family has the same support as in `H`. -/
theorem support_subtype_familyOfForm (F : Form)
    (hF : ∀ i, familyOfForm x₁ x₂ F i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
    Function.support (fun i => (⟨familyOfForm x₁ x₂ F i, hF i⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) = Function.support (familyOfForm x₁ x₂ F) := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  ext i
  exact ⟨fun hi hz => hi (Subtype.ext hz), fun hi hz => hi (congrArg Subtype.val hz)⟩

/-- The support of a form's family is contained in its slots. -/
theorem support_subset_slots (F : Form) :
    Function.support (familyOfForm x₁ x₂ F) ⊆ slots.{u} F := by
  intro i hi
  by_contra hni
  exact hi (familyOfForm_eq_zero_of_notMem_slots x₁ x₂ hni)

/-- The `add (x₁ + x₂)`-valued family of a *finite* form has support of size `< ℵ₀`. -/
theorem mk_support_subtype_lt {F : Form} (hF : F.IsFinite)
    (hFm : ∀ i, familyOfForm x₁ x₂ F i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
    #(Function.support (fun i => (⟨familyOfForm x₁ x₂ F i, hFm i⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))) < (ℵ₀ : Cardinal.{u}) := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  rw [support_subtype_familyOfForm x₁ x₂ F hFm]
  exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset (support_subset_slots x₁ x₂ F))
    (mk_slots_lt hF)

/-- **Lemma 5.2(1)**: an infinite and a finite form cannot be braided.

**This corrects the scaffold**, which omitted the non-degeneracy hypotheses: with `x₁ = 0` the
infinite form `(ℵ₀, 0)` has the identically zero family, which *is* braided with the finite form
`(0, 0)`.  In §5 the hypotheses come free from non-cyclicity — see `ne_zero_of_not_cyclic`.

Proof: the finite form's family has finite support, so by the converse of Lemma 3.4(1)
(`IsBraided.mk_support_lt`, which needs reducedness of `add (x₁ + x₂)`) a braided partner has
finite support too; but an infinite form's family has infinite support. -/
theorem lemma_5_2_one (F G : Form) (hF : F.IsInfinite) (hG : G.IsFinite)
    (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0)
    (hFm : ∀ n, familyOfForm x₁ x₂ F n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ n, familyOfForm x₁ x₂ G n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    ¬ BraidedForms x₁ x₂ F G hFm hGm := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  intro hbr
  have hbr' : IsBraided (ℵ₀ : Cardinal.{u})
      (fun i => (⟨familyOfForm x₁ x₂ F i, hFm i⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
      (fun i => (⟨familyOfForm x₁ x₂ G i, hGm i⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) := hbr
  have hsuppF := hbr'.symm.mk_support_lt (isConical_addOf x₁ x₂)
    (mk_support_subtype_lt x₁ x₂ hG hGm)
  rw [support_subtype_familyOfForm x₁ x₂ F hFm] at hsuppF
  exact infinite_support_familyOfForm x₁ x₂ hF h₁ h₂
    (Cardinal.lt_aleph0_iff_set_finite.mp hsuppF)

/-- The sum of a finite form's family over its slots is the element the form represents. -/
theorem coe_lsumOf_slots {F : Form} (hF : F.IsFinite)
    (hFm : ∀ i, familyOfForm x₁ x₂ F i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
    ((LMonoid.lsumOf (lam := (ℵ₀ : Cardinal.{u})) (mk_slots_lt hF)
        (fun i : slots.{u} F => (⟨familyOfForm x₁ x₂ F i, hFm i⟩ :
          ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) = eval x₁ x₂ F := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  -- the coercion of a submonoid sum *is* the sum in `H` (`IsLSubset.coe_lsumOf` is `rfl`)
  show KMonoid.sumOf (κ := ℵ₀) ((mk_slots_lt hF).le.trans le_rfl)
      (fun i : slots.{u} F => familyOfForm x₁ x₂ F i) = eval x₁ x₂ F
  rw [← KMonoid.sumOf_eq_sumOf_subset mk_formIdx_le_aleph0 ((mk_slots_lt hF).le.trans le_rfl)
    (familyOfForm x₁ x₂ F) fun i hi => familyOfForm_eq_zero_of_notMem_slots x₁ x₂ hi]
  exact sumOf_familyOfForm x₁ x₂ F

/-- **Lemma 5.2(2)**: two finite forms of the same element are braided over `add (x₁ + x₂)`.

Both families are supported on finitely many slots and have the same sum there, which is
`isBraided_of_small_sets`. -/
theorem lemma_5_2_two (F G : Form) (hF : F.IsFinite) (hG : G.IsFinite)
    (heq : eval x₁ x₂ F = eval x₁ x₂ G)
    (hFm : ∀ n, familyOfForm x₁ x₂ F n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ n, familyOfForm x₁ x₂ G n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ F G hFm hGm := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  exact isBraided_of_small_sets (mk_slots_lt hF) (mk_slots_lt hG)
    (fun i hi => Subtype.ext (familyOfForm_eq_zero_of_notMem_slots x₁ x₂ hi))
    (fun i hi => Subtype.ext (familyOfForm_eq_zero_of_notMem_slots x₁ x₂ hi))
    (Subtype.ext (by rw [coe_lsumOf_slots x₁ x₂ hF hFm, coe_lsumOf_slots x₁ x₂ hG hGm]; exact heq))

/-! ### Fibres of a level function on `FormIdx`

`IsBraided.of_levels` (Braiding.lean) reduces building a braiding to a pair of *level functions*
`FormIdx → ℕ` with finite fibres and two block equations.  A level function on `FormIdx` is a
`Sum.elim` of two level functions on `Nats`, its fibre splits accordingly, and the families of §5
are constant on each half — so every block sum is `(#fibre) • x₁ + (#fibre) • x₂`.  These are the
counts that come up: an interval fibre `j / d = k` has `d` elements, a singleton fibre one, and the
`X₁`-slots of a finite form are `{j < A}`. -/

section Fibres

/-- A constant sum over a finite set. -/
theorem finsum_mem_const_finite {α : Type u} {M : Type v} [AddCommMonoid M] {S : Set α}
    (hS : S.Finite) (c : M) : ∑ᶠ _i ∈ S, c = S.ncard • c := by
  classical
  have h1 : ∑ᶠ _i ∈ S, c = ∑ _i ∈ hS.toFinset, c := by
    rw [← finsum_mem_coe_finset, hS.coe_toFinset]
  rw [h1, Finset.sum_const, Set.ncard_eq_toFinset_card S hS]

/-- A subset of `Nats` cut out by a subset of `ℕ` is its image. -/
theorem nats_setOf (T : Set ℕ) : {j : Nats.{u} | j.down ∈ T} = ULift.up '' T := by
  ext ⟨j⟩
  refine ⟨fun h => ⟨j, h, rfl⟩, ?_⟩
  rintro ⟨j', hj', hje⟩
  have hj : j' = j := congrArg ULift.down hje
  subst hj
  exact hj'

theorem ncard_nats_setOf (T : Set ℕ) : ({j : Nats.{u} | j.down ∈ T}).ncard = T.ncard := by
  rw [nats_setOf]
  exact Set.ncard_image_of_injective T (fun a b hab => congrArg ULift.down hab)

theorem finite_nats_setOf {T : Set ℕ} (hT : T.Finite) : ({j : Nats.{u} | j.down ∈ T}).Finite := by
  rw [nats_setOf]; exact hT.image _

/-- The fibre of `j ↦ j / d` is the interval `[dk, dk + d)`, which has `d` elements. -/
theorem div_fiber_eq {d : ℕ} (hd : 0 < d) (k : ℕ) :
    {n : ℕ | n / d = k} = Set.Ico (d * k) (d * k + d) := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
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

/-- The fibre of a level function on `FormIdx` splits into its two halves. -/
theorem fiber_elim (f g : Nats.{u} → ℕ) (k : ℕ) :
    {i : FormIdx.{u} | Sum.elim f g i = k}
      = Sum.inl '' {j : Nats.{u} | f j = k} ∪ Sum.inr '' {j : Nats.{u} | g j = k} := by
  ext i
  rcases i with j | j <;> simp

theorem finite_fiber_elim {f g : Nats.{u} → ℕ} {k : ℕ}
    (hf : {j : Nats.{u} | f j = k}.Finite) (hg : {j : Nats.{u} | g j = k}.Finite) :
    {i : FormIdx.{u} | Sum.elim f g i = k}.Finite := by
  rw [fiber_elim]
  exact (hf.image _).union (hg.image _)

/-- **The block sum of a family constant on each half of `FormIdx`**: it is `#fibre` copies of the
value on the left half plus `#fibre` copies of the value on the right half. -/
theorem finsum_fiber_const {M : Type v} [AddCommMonoid M] {f g : Nats.{u} → ℕ} {k : ℕ}
    (hf : {j : Nats.{u} | f j = k}.Finite) (hg : {j : Nats.{u} | g j = k}.Finite)
    (F : FormIdx.{u} → M) {a b : M}
    (hfa : ∀ j ∈ {j : Nats.{u} | f j = k}, F (Sum.inl j) = a)
    (hgb : ∀ j ∈ {j : Nats.{u} | g j = k}, F (Sum.inr j) = b) :
    ∑ᶠ i ∈ {i : FormIdx.{u} | Sum.elim f g i = k}, F i
      = ({j : Nats.{u} | f j = k}).ncard • a + ({j : Nats.{u} | g j = k}).ncard • b := by
  classical
  have hdisj : Disjoint (Sum.inl '' {j : Nats.{u} | f j = k})
      (Sum.inr '' {j : Nats.{u} | g j = k}) := by
    refine Set.disjoint_left.mpr ?_
    rintro i ⟨j, -, rfl⟩ ⟨j', -, hj'⟩
    exact Sum.inl_ne_inr hj'.symm
  rw [fiber_elim, finsum_mem_union hdisj (hf.image _) (hg.image _),
    finsum_mem_image Sum.inl_injective.injOn, finsum_mem_image Sum.inr_injective.injOn,
    finsum_mem_congr rfl hfa, finsum_mem_congr rfl hgb,
    finsum_mem_const_finite hf, finsum_mem_const_finite hg]

end Fibres

/-! ### The fibre counts used by Lemma 5.2(3) -/

theorem ecmul_add (a b : ℕ∞) (x : H) : ecmul (a + b) x = ecmul a x + ecmul b x := by
  have hc : Cardinal.ofENat (a + b) = Cardinal.ofENat a + Cardinal.ofENat b := by simp
  have hle : Cardinal.ofENat a + Cardinal.ofENat b ≤ ℵ₀ := hc ▸ Cardinal.ofENat_le_aleph0 (a + b)
  rw [ecmul, ecmul, ecmul, KMonoid.cmul_congr hc _ hle,
    KMonoid.cmul_add (Cardinal.ofENat_le_aleph0 a) (Cardinal.ofENat_le_aleph0 b) hle]

theorem ecmul_one_add (a : ℕ∞) (x : H) : ecmul (1 + a) x = x + ecmul a x := by
  have hc : Cardinal.ofENat (1 + a) = 1 + Cardinal.ofENat a := by simp
  have hle : (1 : Cardinal.{u}) + Cardinal.ofENat a ≤ ℵ₀ := hc ▸ Cardinal.ofENat_le_aleph0 (1 + a)
  rw [ecmul, ecmul, KMonoid.cmul_congr hc _ hle,
    KMonoid.cmul_add (le_of_lt Cardinal.one_lt_aleph0) (Cardinal.ofENat_le_aleph0 a) hle,
    KMonoid.cmul_one]

theorem ecmul_natCast (k : ℕ) (x : H) : ecmul ((k : ℕ) : ℕ∞) x = k • x := by
  rw [ecmul, KMonoid.cmul_congr (by simp : Cardinal.ofENat ((k : ℕ) : ℕ∞) = ((k : ℕ) : Cardinal.{u}))
    _ (le_of_lt Cardinal.natCast_lt_aleph0)]
  exact KMonoid.cmul_natCast x k

/-- `add y` is closed under binary sums: `+` is a two-element `ℵ₀⁻`-sum. -/
theorem addOf_add_mem {y a b : H} (ha : a ∈ KMonoid.addOf (κ := ℵ₀) y)
    (hb : b ∈ KMonoid.addOf (κ := ℵ₀) y) : a + b ∈ KMonoid.addOf (κ := ℵ₀) y := by
  have hUB : #(ULift.{u} Bool) < (ℵ₀ : Cardinal.{u}) :=
    Cardinal.lt_aleph0_iff_finite.mpr inferInstance
  have hmem : KMonoid.sumOf (κ := ℵ₀) (hUB.le.trans le_rfl)
      (fun p : ULift.{u} Bool => if p.down then a else b) ∈ KMonoid.addOf (κ := ℵ₀) y :=
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl y).sumOf_mem hUB _ (by rintro ⟨(_ | _)⟩ <;> simpa)
  rwa [KMonoid.sumOf_two a b (hUB.le.trans le_rfl)] at hmem

theorem addOf_nsmul_mem {y a : H} (ha : a ∈ KMonoid.addOf (κ := ℵ₀) y) (k : ℕ) :
    k • a ∈ KMonoid.addOf (κ := ℵ₀) y := by
  induction k with
  | zero =>
    rw [zero_nsmul]
    exact (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl y).zero_mem
  | succ p hp => rw [succ_nsmul]; exact addOf_add_mem hp ha

/-- `add a ⊆ add b` as soon as `a ∈ add b`. -/
theorem addOf_subset_of_mem {a b : H} (h : a ∈ KMonoid.addOf (κ := ℵ₀) b) :
    KMonoid.addOf (κ := ℵ₀) a ⊆ KMonoid.addOf (κ := ℵ₀) b := by
  rintro y ⟨z, n, hzn⟩
  refine KMonoid.addOf_isSaturated b
    (KMonoid.cmul (κ := ℵ₀) (n : Cardinal.{u})
      (le_trans (le_of_lt Cardinal.natCast_lt_aleph0) le_rfl) a) ?_ y z hzn.symm
  rw [KMonoid.cmul_natCast]
  exact addOf_nsmul_mem h n

/-- The fibre at `0` of the level function that parks the first `A` slots on level `0`. -/
theorem levelA_fiber_zero (A : ℕ) :
    {j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = 0}
      = {j : Nats.{u} | j.down < A} := by
  ext ⟨j⟩
  by_cases h : j < A <;> simp [h]

/-- Its fibre at `k + 1` is the singleton `{A + k}`. -/
theorem levelA_fiber_succ (A k : ℕ) :
    {j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = k + 1}
      = {j : Nats.{u} | j.down = A + k} := by
  ext ⟨j⟩
  by_cases h : j < A <;> simp [h] <;> omega

theorem divsucc_fiber_zero (n : ℕ) : {j : Nats.{u} | j.down / n + 1 = 0} = ∅ := by
  ext ⟨j⟩; simp

theorem divsucc_fiber_succ (n k : ℕ) :
    {j : Nats.{u} | j.down / n + 1 = k + 1} = {j : Nats.{u} | j.down / n = k} := by
  ext ⟨j⟩; simp


theorem familyOfForm_inl (F : Form) (j : Nats.{u}) :
    familyOfForm x₁ x₂ F (Sum.inl j) = if ((j.down : ℕ) : ℕ∞) < F.1 then x₁ else 0 := rfl

theorem familyOfForm_inr (F : Form) (j : Nats.{u}) :
    familyOfForm x₁ x₂ F (Sum.inr j) = if ((j.down : ℕ) : ℕ∞) < F.2 then x₂ else 0 := rfl

/-- Every slot of every form lies in `add (x₁ + x₂)`. -/
theorem familyOfForm_mem (F : Form) (i : FormIdx.{u}) :
    familyOfForm x₁ x₂ F i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) := by
  have h₁ : x₁ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have h₂ : x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  have h0 : (0 : H) ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)).zero_mem
  rcases i with j | j
  · rw [familyOfForm_inl]; split <;> assumption
  · rw [familyOfForm_inr]; split <;> assumption

theorem ncard_nats_div {d : ℕ} (hd : 0 < d) (k : ℕ) :
    ({j : Nats.{u} | j.down / d = k}).ncard = d :=
  (ncard_nats_setOf {n : ℕ | n / d = k}).trans (ncard_div_fiber hd k)

theorem finite_nats_div {d : ℕ} (hd : 0 < d) (k : ℕ) : ({j : Nats.{u} | j.down / d = k}).Finite :=
  finite_nats_setOf (finite_div_fiber hd k)

theorem ncard_nats_eq (k : ℕ) : ({j : Nats.{u} | j.down = k}).ncard = 1 :=
  (ncard_nats_setOf {k}).trans (Set.ncard_singleton k)

theorem finite_nats_eq (k : ℕ) : ({j : Nats.{u} | j.down = k}).Finite :=
  finite_nats_setOf (Set.finite_singleton k)

theorem ncard_nats_lt (A : ℕ) : ({j : Nats.{u} | j.down < A}).ncard = A :=
  (ncard_nats_setOf (Set.Iio A)).trans (Set.ncard_Iio_nat A)

theorem finite_nats_lt (A : ℕ) : ({j : Nats.{u} | j.down < A}).Finite :=
  finite_nats_setOf (Set.finite_Iio A)

/-- The coercion of a `finsum` over a finite set from `add (x₁ + x₂)` to `H`: the block sums of a
braiding built inside the submonoid may be computed in `H`. -/
theorem coe_finsum_mem {S : Set FormIdx.{u}} (hS : S.Finite) (f : FormIdx.{u} → H)
    (hf : ∀ i, f i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
    (((∑ᶠ i ∈ S, (⟨f i, hf i⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) = ∑ᶠ i ∈ S, f i := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  exact AddMonoidHom.map_finsum_mem _
    ({ toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) →+ H) hS

/-- **The heart of Lemma 5.2(3)**: `α X₁ + ℵ₀ X₂` is braided with `ℵ₀ X₂`, for every `α ≤ ℵ₀`.

The paper writes down the partitions outright; here they are given as *level functions* on
`FormIdx`, one for each copy of `ℕ`, and fed to `IsBraided.of_levels`.

For `α = A` finite, `A x₁ ∈ add x₂` gives `A x₁ + t = n x₂` with `n ≥ 1`, and the levels are

    cI = (j ↦ if j < A then 0 else j - A + 1) ⊕ (j ↦ j / n + 1),   cJ = (j ↦ j) ⊕ (j ↦ j / n),
    u ≡ A x₁,   v 0 = 0,   v (k+1) = t,

so that level `0` of `I` collects exactly the `A` copies of `x₁` and every later level collects
`n` copies of `x₂`, which is `t + A x₁`.

For `α = ℵ₀` one first re-derives `m x₂ = (m'+1) x₁ + n' x₂` with `m'`, `n'` finite — this is where
`NoMixedForms` and the generation hypothesis enter, since `t = m' x₁ + n' x₂` would otherwise give
`m x₂` an infinite form alongside its finite one — and then the two families have *equal* block
sums, so `v ≡ 0`:

    cI = (j ↦ j / (m'+1)) ⊕ (j ↦ j / (n'+1)),   cJ = (j ↦ j) ⊕ (j ↦ j / m),   u ≡ m x₂.

**This corrects the scaffold**, which omitted the generation hypothesis `hgen`; it is a standing
assumption of §5 and the `α = ℵ₀` case genuinely needs it. -/
theorem braidedForms_of_top (hmem : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂) (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H)) (α : ℕ∞)
    (hFm : ∀ n, familyOfForm x₁ x₂ (α, ⊤) n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ n, familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ (α, ⊤) ((0 : ℕ∞), ⊤) hFm hGm := by
  classical
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  have hx₁T : x₁ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  show IsBraided (ℵ₀ : Cardinal.{u})
    (fun i => (⟨familyOfForm x₁ x₂ (α, ⊤) i, hFm i⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
    (fun i => (⟨familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) i, hGm i⟩ :
      ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
  -- a degenerate case: with `x₁ = 0` the two families are literally equal
  rcases eq_or_ne x₁ 0 with hx0 | hx0
  · have hfam : (fun i => (⟨familyOfForm x₁ x₂ (α, ⊤) i, hFm i⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
      = (fun i => (⟨familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) i, hGm i⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) := by
      funext i
      refine Subtype.ext ?_
      rcases i with j | j
      · show familyOfForm x₁ x₂ (α, ⊤) (Sum.inl j)
          = familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) (Sum.inl j)
        rw [familyOfForm_inl, familyOfForm_inl]
        simp [hx0]
      · show familyOfForm x₁ x₂ (α, ⊤) (Sum.inr j)
          = familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) (Sum.inr j)
        rfl
    -- `IsBraided.refl` is `@[refl]`, so `rw` closes the goal
    rw [hfam]
  -- `x₁ + z = m₀ x₂` with `m₀ ≥ 1`
  obtain ⟨z, m₀, hz⟩ := hmem
  rw [KMonoid.cmul_natCast] at hz
  have hm₀ : m₀ ≠ 0 := by
    rintro rfl
    rw [zero_nsmul] at hz
    exact hx0 (KMonoid.isConical (ℵ₀ : Cardinal.{u}) H x₁ z hz).1
  rcases eq_or_ne α ⊤ with rfl | hα
  · -- **the case `α = ℵ₀`**: re-derive `m x₂ = (m'+1) x₁ + n' x₂` and match the block sums
    obtain ⟨G, hG⟩ := exists_form x₁ x₂ hgen z
    have hGfin : G.1 ≠ ⊤ ∧ G.2 ≠ ⊤ := by
      by_contra hcon
      refine hmix (m₀ • x₂) ⟨⟨(0, (m₀ : ℕ∞)), ⟨by simp, by simp⟩, ?_⟩, ⟨(1 + G.1, G.2), ?_, ?_⟩⟩
      · rw [eval, ecmul_zero, zero_add, ecmul_natCast]
      · rcases not_and_or.mp hcon with h | h
        · exact Or.inl (by rw [not_ne_iff.mp h]; exact add_top 1)
        · exact Or.inr (not_ne_iff.mp h)
      · rw [eval, ecmul_one_add, add_assoc, ← eval, hG, hz]
    obtain ⟨m', hm'⟩ : ∃ m' : ℕ, G.1 = (m' : ℕ∞) := ⟨G.1.toNat, (ENat.natCast_toNat hGfin.1).symm⟩
    obtain ⟨n', hn'⟩ : ∃ n' : ℕ, G.2 = (n' : ℕ∞) := ⟨G.2.toNat, (ENat.natCast_toNat hGfin.2).symm⟩
    -- `(m'+1) x₁ + (n'+1) x₂ = (m₀+1) x₂`
    have hkey : (m' + 1) • x₁ + (n' + 1) • x₂ = (m₀ + 1) • x₂ := by
      have hzval : z = m' • x₁ + n' • x₂ := by
        rw [← hG, eval, hm', hn', ecmul_natCast, ecmul_natCast]
      rw [succ_nsmul x₁ m', succ_nsmul x₂ n', succ_nsmul x₂ m₀, ← hz, hzval]
      abel
    have hmT : (m₀ + 1) • x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) := addOf_nsmul_mem hx₂T _
    refine IsBraided.of_levels (Sum.inl (ULift.up 0))
      (Sum.elim (fun j => j.down / (m' + 1)) (fun j => j.down / (n' + 1)))
      (Sum.elim (fun j => j.down) (fun j => j.down / (m₀ + 1)))
      (fun k => finite_fiber_elim (finite_nats_div (Nat.succ_pos m') k)
        (finite_nats_div (Nat.succ_pos n') k))
      (fun k => finite_fiber_elim (finite_nats_eq k) (finite_nats_div (Nat.succ_pos m₀) k))
      (fun _ => ⟨(m₀ + 1) • x₂, hmT⟩) (fun _ => 0) rfl (fun k => ?_) (fun k => ?_)
    · refine Subtype.ext ?_
      rw [coe_finsum_mem x₁ x₂
          (finite_fiber_elim (finite_nats_div (Nat.succ_pos m') k)
            (finite_nats_div (Nat.succ_pos n') k)) _ hFm,
        finsum_fiber_const (a := x₁) (b := x₂) (finite_nats_div (Nat.succ_pos m') k)
          (finite_nats_div (Nat.succ_pos n') k) _
          (fun j _ => by rw [familyOfForm_inl]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ)))
          (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        ncard_nats_div (Nat.succ_pos m') k, ncard_nats_div (Nat.succ_pos n') k]
      show (m' + 1) • x₁ + (n' + 1) • x₂ = ((0 : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H)
        + (m₀ + 1) • x₂
      rw [hkey]
      exact (zero_add _).symm
    · refine Subtype.ext ?_
      rw [coe_finsum_mem x₁ x₂
          (finite_fiber_elim (finite_nats_eq k) (finite_nats_div (Nat.succ_pos m₀) k)) _ hGm,
        finsum_fiber_const (a := (0 : H)) (b := x₂) (finite_nats_eq k)
          (finite_nats_div (Nat.succ_pos m₀) k) _
          (fun j _ => by rw [familyOfForm_inl]; exact if_neg (by simp))
          (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        ncard_nats_eq k, ncard_nats_div (Nat.succ_pos m₀) k, smul_zero, zero_add]
      show (m₀ + 1) • x₂ = ((0 : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) + (m₀ + 1) • x₂
      exact (zero_add _).symm
  -- **the case `α = A` finite**: the level-`0` block carries the `A` copies of `x₁`
  obtain ⟨A, rfl⟩ : ∃ A : ℕ, α = (A : ℕ∞) := ⟨α.toNat, (ENat.natCast_toNat hα).symm⟩
  set n : ℕ := A * m₀ + 1 with hndef
  set t : H := A • z + x₂ with htdef
  have hnt : A • x₁ + t = n • x₂ := by
    rw [htdef, hndef, ← add_assoc, ← smul_add, hz, smul_smul, succ_nsmul]
  have hAT : A • x₁ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) := addOf_nsmul_mem hx₁T _
  have htT : t ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (addOf_nsmul_mem hx₂T n) t (A • x₁)
      (by rw [← hnt]; exact add_comm _ _)
  have hnpos : 0 < n := Nat.succ_pos _
  refine IsBraided.of_levels (Sum.inl (ULift.up 0))
    (Sum.elim (fun j => if j.down < A then 0 else (j.down - A) + 1) (fun j => j.down / n + 1))
    (Sum.elim (fun j => j.down) (fun j => j.down / n))
    (fun k => ?_) (fun k => finite_fiber_elim (finite_nats_eq k) (finite_nats_div hnpos k))
    (fun _ => ⟨A • x₁, hAT⟩) (fun k => if k = 0 then 0 else ⟨t, htT⟩) (if_pos rfl)
    (fun k => ?_) (fun k => ?_)
  · rcases k with _ | K
    · exact finite_fiber_elim (by rw [levelA_fiber_zero]; exact finite_nats_lt A)
        (by rw [divsucc_fiber_zero]; exact Set.finite_empty)
    · exact finite_fiber_elim (by rw [levelA_fiber_succ]; exact finite_nats_eq (A + K))
        (by rw [divsucc_fiber_succ]; exact finite_nats_div hnpos K)
  · rcases k with _ | K
    · refine Subtype.ext ?_
      have hf : {j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = 0}.Finite := by
        rw [levelA_fiber_zero]; exact finite_nats_lt A
      have hg : {j : Nats.{u} | j.down / n + 1 = 0}.Finite := by
        rw [divsucc_fiber_zero]; exact Set.finite_empty
      rw [coe_finsum_mem x₁ x₂ (finite_fiber_elim hf hg) _ hFm,
        finsum_fiber_const (a := x₁) (b := x₂) hf hg _
          (fun j hj => by
            rw [levelA_fiber_zero] at hj
            rw [familyOfForm_inl]
            refine if_pos ?_
            show ((j.down : ℕ) : ℕ∞) < ((A : ℕ) : ℕ∞)
            exact_mod_cast (hj : (j.down : ℕ) < A))
          (fun j hj => by rw [divsucc_fiber_zero] at hj; exact absurd hj (Set.notMem_empty j)),
        show ({j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = 0}).ncard = A by
          rw [levelA_fiber_zero]; exact ncard_nats_lt A,
        show ({j : Nats.{u} | j.down / n + 1 = 0}).ncard = 0 by
          rw [divsucc_fiber_zero]; exact Set.ncard_empty _,
        zero_smul, add_zero]
      show A • x₁ = ((if (0 : ℕ) = 0 then (0 : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))
        else ⟨t, htT⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) + A • x₁
      rw [if_pos rfl]
      exact (zero_add _).symm
    · refine Subtype.ext ?_
      have hf : {j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = K + 1}.Finite := by
        rw [levelA_fiber_succ]; exact finite_nats_eq (A + K)
      have hg : {j : Nats.{u} | j.down / n + 1 = K + 1}.Finite := by
        rw [divsucc_fiber_succ]; exact finite_nats_div hnpos K
      rw [coe_finsum_mem x₁ x₂ (finite_fiber_elim hf hg) _ hFm,
        finsum_fiber_const (a := (0 : H)) (b := x₂) hf hg _
          (fun j hj => by
            rw [levelA_fiber_succ] at hj
            rw [familyOfForm_inl]
            refine if_neg ?_
            show ¬ (((j.down : ℕ) : ℕ∞) < ((A : ℕ) : ℕ∞))
            have hja : (j.down : ℕ) = A + K := hj
            rw [hja]
            exact_mod_cast Nat.not_lt.mpr (Nat.le_add_right A K))
          (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        show ({j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = K + 1}).ncard = 1 by
          rw [levelA_fiber_succ]; exact ncard_nats_eq (A + K),
        show ({j : Nats.{u} | j.down / n + 1 = K + 1}).ncard = n by
          rw [divsucc_fiber_succ]; exact ncard_nats_div hnpos K,
        smul_zero, zero_add]
      show n • x₂ = ((if K + 1 = 0 then (0 : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))
        else ⟨t, htT⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) + A • x₁
      rw [if_neg (Nat.succ_ne_zero K)]
      show n • x₂ = t + A • x₁
      rw [← hnt]
      exact add_comm _ _
  · refine Subtype.ext ?_
    rw [coe_finsum_mem x₁ x₂ (finite_fiber_elim (finite_nats_eq k) (finite_nats_div hnpos k)) _ hGm,
      finsum_fiber_const (a := (0 : H)) (b := x₂) (finite_nats_eq k) (finite_nats_div hnpos k) _
        (fun j _ => by rw [familyOfForm_inl]; exact if_neg (by simp))
        (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
      ncard_nats_eq k, ncard_nats_div hnpos k, smul_zero, zero_add]
    show n • x₂ = ((if k + 1 = 0 then (0 : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))
      else ⟨t, htT⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) + A • x₁
    rw [if_neg (Nat.succ_ne_zero k)]
    show n • x₂ = t + A • x₁
    rw [← hnt]
    exact add_comm _ _

/-- **Lemma 5.2(3)**: if `x₁ ∈ add x₂` and no element has both a finite and an infinite form, then
`α X₁ + ℵ₀ X₂` and `β X₁ + ℵ₀ X₂` are braided, for all `α, β ≤ ℵ₀`.

As in the paper, symmetry and transitivity of the braiding relation (Lemma 3.8) reduce this to the
case `β = 0`, which is `braidedForms_of_top`. -/
theorem lemma_5_2_three (hmem : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂) (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H)) (α β : ℕ∞)
    (hFm : ∀ n, familyOfForm x₁ x₂ (α, ⊤) n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ n, familyOfForm x₁ x₂ (β, ⊤) n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ (α, ⊤) (β, ⊤) hFm hGm := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  have hZm : ∀ n, familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    fun n => familyOfForm_mem x₁ x₂ _ n
  exact IsBraided.trans_aleph0 (braidedForms_of_top x₁ x₂ hmem hmix hgen α hFm hZm)
    (IsBraided.symm (braidedForms_of_top x₁ x₂ hmem hmix hgen β hGm hZm))

/-! ### Extra bookkeeping for Lemma 5.2(4) -/

/-- A finite sum of multiples of `c` is a multiple of `c`. -/
theorem exists_nsmul_finsum {M : Type v} [AddCommMonoid M] {ι : Type u} {S : Set ι}
    (hS : S.Finite) (F : ι → M) (c : M) (hF : ∀ i ∈ S, ∃ p : ℕ, F i = p • c) :
    ∃ p : ℕ, ∑ᶠ i ∈ S, F i = p • c := by
  classical
  revert hF
  induction S, hS using Set.Finite.induction_on with
  | empty => exact fun _ => ⟨0, by rw [finsum_mem_empty, zero_smul]⟩
  | @insert a S' ha hS' hind =>
    intro hF
    obtain ⟨p, hp⟩ := hind (fun i hi => hF i (Set.mem_insert_of_mem a hi))
    obtain ⟨q, hq⟩ := hF a (Set.mem_insert a S')
    exact ⟨q + p, by rw [finsum_mem_insert _ ha hS', hp, hq, add_smul]⟩

/-- The coercion `add (x₁ + x₂) → H` commutes with `nsmul`. -/
theorem coe_nsmul_addOf (k : ℕ) (a : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) :
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
    ((k • a : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) = k • (a : H) := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul]; rfl
  | succ p hp => rw [succ_nsmul, succ_nsmul, ← hp]; rfl

/-- The slots at which the family of `c X₁ + ℵ₀ X₂` takes the value `x₁`. -/
def oneSlots (c : ℕ) : Set FormIdx.{u} := Sum.inl '' {j : Nats.{u} | j.down < c}

theorem finite_oneSlots (c : ℕ) : (oneSlots.{u} c).Finite := (finite_nats_lt c).image _

theorem ncard_oneSlots (c : ℕ) : (oneSlots.{u} c).ncard = c := by
  rw [oneSlots, Set.ncard_image_of_injective _ Sum.inl_injective]
  exact ncard_nats_lt c

theorem familyOfForm_eq_of_mem_oneSlots {c : ℕ} {i : FormIdx.{u}} (hi : i ∈ oneSlots.{u} c) :
    familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i = x₁ := by
  obtain ⟨j, hj, rfl⟩ := hi
  rw [familyOfForm_inl]
  refine if_pos ?_
  show ((j.down : ℕ) : ℕ∞) < ((c : ℕ) : ℕ∞)
  exact_mod_cast hj

theorem familyOfForm_eq_of_notMem_oneSlots {c : ℕ} {i : FormIdx.{u}} (hi : i ∉ oneSlots.{u} c) :
    familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i = x₂ ∨ familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i = 0 := by
  rcases i with j | j
  · refine Or.inr ?_
    rw [familyOfForm_inl]
    refine if_neg ?_
    show ¬ (((j.down : ℕ) : ℕ∞) < ((c : ℕ) : ℕ∞))
    intro h
    exact hi ⟨j, by exact_mod_cast h, rfl⟩
  · refine Or.inl ?_
    rw [familyOfForm_inr]
    exact if_pos (WithTop.coe_lt_top (j.down : ℕ))

/-- **A block sum of the family of `c X₁ + ℵ₀ X₂`** over a finite set of slots containing all the
`x₁`-slots is `c x₁ + p x₂` for some finite `p`: the `x₁`-slots contribute exactly `c` copies and
every other slot carries `x₂` or `0`. -/
theorem exists_block_value {c : ℕ} {S : Set FormIdx.{u}} (hS : S.Finite)
    (hsub : oneSlots.{u} c ⊆ S)
    (hFm : ∀ i, familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hx₁T : x₁ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hx₂T : x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
    ∃ p : ℕ, (∑ᶠ i ∈ S, (⟨familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i, hFm i⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
      = c • (⟨x₁, hx₁T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))
        + p • (⟨x₂, hx₂T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) := by
  classical
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  have hsplit : S = oneSlots.{u} c ∪ (S \ oneSlots.{u} c) := (Set.union_diff_cancel hsub).symm
  have hdisj : Disjoint (oneSlots.{u} c) (S \ oneSlots.{u} c) := Set.disjoint_sdiff_right
  have hdfin : (S \ oneSlots.{u} c).Finite := hS.subset Set.diff_subset
  obtain ⟨p, hp⟩ := exists_nsmul_finsum hdfin
    (fun i => (⟨familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i, hFm i⟩ :
      ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
    (⟨x₂, hx₂T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))
    (fun i (hi : i ∈ S \ oneSlots.{u} c) => by
      rcases familyOfForm_eq_of_notMem_oneSlots x₁ x₂ hi.2 with h | h
      · exact ⟨1, by rw [one_smul]; exact Subtype.ext h⟩
      · exact ⟨0, by rw [zero_smul]; exact Subtype.ext h⟩)
  refine ⟨p, ?_⟩
  rw [hsplit, finsum_mem_union hdisj (finite_oneSlots c) hdfin, hp,
    finsum_mem_congr rfl (fun i hi => (Subtype.ext (familyOfForm_eq_of_mem_oneSlots x₁ x₂ hi) :
      (⟨familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i, hFm i⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) = ⟨x₁, hx₁T⟩)),
    finsum_mem_const_finite (finite_oneSlots c), ncard_oneSlots]

/-- **Lemma 5.2(4)**: for incomparable generators, a braiding of `m X₁ + ℵ₀ X₂` with
`n X₁ + ℵ₀ X₂` forces a finite relation `m x₁ + k x₂ = n x₁ + k' x₂`.

Paper proof, adapted to the block structure `ι × ℕ` of `BraidingData` — where the positions form
countably many `ω`-chains rather than one well-order, so the paper's single cut `μ ≤ α` becomes a
*rectangle*: choose a finite set `A` of chains and a level `K` such that every one of the finitely
many `x₁`-slots of either family lies in some `I (a,k)` resp. `J (a,k)` with `a ∈ A`, `k ≤ K`.
`BraidingData.telescope` then gives

    n x₁ + q x₂ = m x₁ + p x₂ + Σ_{a ∈ A} v (a, K+1),

because each of the two rectangles is a finite set of slots containing all the `x₁`-slots of its
family (`exists_block_value`).  Finally `I (a, K+1)` contains no `x₁`-slot at all, so
`v (a,K+1) + u (a,K+1)` is a finite multiple of `x₂`; hence `v (a,K+1) ∈ add x₂`, so its form has
zero `X₁`-coefficient (`x₁ ∉ add x₂`) and finite `X₂`-coefficient (`NoMixedForms`, applied to that
finite multiple of `x₂`).

**This corrects the scaffold**, which omitted the generation hypothesis `hgen`; it is a standing
assumption of §5, and the last step needs it to write `v (a,K+1)` in a form at all. -/
theorem lemma_5_2_four (hmem : x₁ ∉ KMonoid.addOf (κ := ℵ₀) x₂) (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H)) (m n : ℕ)
    (hFm : ∀ i, familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ i, familyOfForm x₁ x₂ ((n : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hbr : BraidedForms x₁ x₂ ((m : ℕ∞), ⊤) ((n : ℕ∞), ⊤) hFm hGm) :
    ∃ k k' : ℕ, eval x₁ x₂ ((m : ℕ∞), (k : ℕ∞)) = eval x₁ x₂ ((n : ℕ∞), (k' : ℕ∞)) := by
  classical
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  have hx₁T : x₁ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  obtain ⟨D⟩ := hbr
  -- the finitely many `x₁`-slots of the two families, and the blocks holding them
  have hWfin : (oneSlots.{u} m ∪ oneSlots.{u} n).Finite :=
    (finite_oneSlots m).union (finite_oneSlots n)
  have hPPfin : ((fun i => IsBraided.blockOf D.I D.I_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
      ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)).Finite :=
    (hWfin.image _).union (hWfin.image _)
  have hAfin : (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
      ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))).Finite :=
    hPPfin.image _
  obtain ⟨K, hK⟩ := (hPPfin.image Prod.snd).bddAbove
  -- disjointness of the rectangle pieces
  have hdisjK : ∀ (P : FormIdx.{u} × ℕ → Set FormIdx.{u}),
      (∀ p q, p ≠ q → Disjoint (P p) (P q)) → ∀ a : FormIdx.{u},
        ((↑(Finset.range (K + 1)) : Set ℕ)).PairwiseDisjoint (fun k => P (a, k)) := by
    intro P hP a k _ k' _ hkk'
    exact hP (a, k) (a, k') fun h => hkk' (congrArg Prod.snd h)
  have hdisjA : ∀ (P : FormIdx.{u} × ℕ → Set FormIdx.{u}),
      (∀ p q, p ≠ q → Disjoint (P p) (P q)) →
      (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
        ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))).PairwiseDisjoint
        (fun a => ⋃ k ∈ (↑(Finset.range (K + 1)) : Set ℕ), P (a, k)) := by
    intro P hP a _ a' _ haa'
    refine Set.disjoint_left.mpr ?_
    intro i hi hi'
    obtain ⟨k, -, hk⟩ := Set.mem_iUnion₂.mp hi
    obtain ⟨k', -, hk'⟩ := Set.mem_iUnion₂.mp hi'
    exact Set.disjoint_left.mp (hP (a, k) (a', k') fun h => haa' (congrArg Prod.fst h)) hk hk'
  -- the two rectangles, as finite sets of slots
  have hrect : ∀ (P : FormIdx.{u} × ℕ → Set FormIdx.{u}),
      (∀ p, #(P p) < (ℵ₀ : Cardinal.{u})) →
      (⋃ a ∈ (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
        ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))),
        ⋃ k ∈ (↑(Finset.range (K + 1)) : Set ℕ), P (a, k)).Finite := by
    intro P hP
    exact hAfin.biUnion fun a _ => (Finset.range (K + 1)).finite_toSet.biUnion
      fun k _ => Cardinal.lt_aleph0_iff_set_finite.mp (hP (a, k))
  -- the rectangle sums are the double sums the telescoping identity speaks about
  have hrectsum : ∀ (P : FormIdx.{u} × ℕ → Set FormIdx.{u})
      (hPd : ∀ p q, p ≠ q → Disjoint (P p) (P q)) (hPs : ∀ p, #(P p) < (ℵ₀ : Cardinal.{u}))
      (f : FormIdx.{u} → ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))),
      (∑ᶠ i ∈ (⋃ a ∈ (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) ''
          (oneSlots.{u} m ∪ oneSlots.{u} n)
          ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))),
          ⋃ k ∈ (↑(Finset.range (K + 1)) : Set ℕ), P (a, k)), f i)
        = ∑ᶠ a ∈ (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) ''
            (oneSlots.{u} m ∪ oneSlots.{u} n)
            ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))),
            ∑ k ∈ Finset.range (K + 1),
              LMonoid.lsumOf (lam := (ℵ₀ : Cardinal.{u})) (hPs (a, k)) (fun i : P (a, k) => f i) := by
    intro P hPd hPs f
    rw [finsum_mem_biUnion (hdisjA P hPd) hAfin
      (fun a _ => (Finset.range (K + 1)).finite_toSet.biUnion
        fun k _ => Cardinal.lt_aleph0_iff_set_finite.mp (hPs (a, k)))]
    refine finsum_mem_congr rfl fun a _ => ?_
    rw [finsum_mem_biUnion (hdisjK P hPd a) (Finset.range (K + 1)).finite_toSet
      (fun k _ => Cardinal.lt_aleph0_iff_set_finite.mp (hPs (a, k))), finsum_mem_coe_finset]
    exact Finset.sum_congr rfl fun k _ => (LMonoid.lsumOf_eq_finsum (hPs (a, k)) f).symm
  -- the rectangles cover the `x₁`-slots
  have hcover : ∀ (P : FormIdx.{u} × ℕ → Set FormIdx.{u}) (hcov : (⋃ p, P p) = Set.univ),
      ((fun i => IsBraided.blockOf P hcov i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
        ⊆ (fun i => IsBraided.blockOf D.I D.I_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
          ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)) →
      ∀ c : ℕ, oneSlots.{u} c ⊆ oneSlots.{u} m ∪ oneSlots.{u} n →
      oneSlots.{u} c ⊆ ⋃ a ∈ (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) ''
        (oneSlots.{u} m ∪ oneSlots.{u} n)
        ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))),
        ⋃ k ∈ (↑(Finset.range (K + 1)) : Set ℕ), P (a, k) := by
    intro P hcov hsub c hc i hi
    have hpp : IsBraided.blockOf P hcov i ∈ (fun i => IsBraided.blockOf D.I D.I_cover i) ''
        (oneSlots.{u} m ∪ oneSlots.{u} n)
        ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n) :=
      hsub ⟨i, hc hi, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨(IsBraided.blockOf P hcov i).1, ⟨_, hpp, rfl⟩, ?_⟩
    refine Set.mem_iUnion₂.mpr ⟨(IsBraided.blockOf P hcov i).2, ?_, ?_⟩
    · simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (hK ⟨_, hpp, rfl⟩)
    · rw [Prod.mk.eta]
      exact IsBraided.mem_blockOf P hcov i
  -- the two block values
  obtain ⟨p, hp⟩ := exists_block_value x₁ x₂ (hrect D.I D.I_small)
    (hcover D.I D.I_cover Set.subset_union_left m Set.subset_union_left) hFm hx₁T hx₂T
  obtain ⟨q, hq⟩ := exists_block_value x₁ x₂ (hrect D.J D.J_small)
    (hcover D.J D.J_cover Set.subset_union_right n Set.subset_union_right) hGm hx₁T hx₂T
  -- the surviving `v`-terms are finite multiples of `x₂`
  have hV : ∃ r : ℕ, (∑ᶠ a ∈ (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) ''
      (oneSlots.{u} m ∪ oneSlots.{u} n)
      ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))),
      D.v (a, K + 1)) = r • (⟨x₂, hx₂T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) := by
    refine exists_nsmul_finsum hAfin _ _ fun a _ => ?_
    -- no `x₁`-slot survives past level `K`
    have hno : ∀ i ∈ D.I (a, K + 1), familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i = x₂
        ∨ familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i = 0 := by
      intro i hi
      refine familyOfForm_eq_of_notMem_oneSlots x₁ x₂ fun hone => ?_
      have hb : IsBraided.blockOf D.I D.I_cover i = (a, K + 1) := IsBraided.blockOf_eq D.I_disjoint D.I_cover hi
      have hpp : IsBraided.blockOf D.I D.I_cover i ∈ (fun i => IsBraided.blockOf D.I D.I_cover i) ''
          (oneSlots.{u} m ∪ oneSlots.{u} n)
          ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n) :=
        Set.mem_union_left _ ⟨i, Set.mem_union_left _ hone, rfl⟩
      have := hK (Set.mem_image_of_mem Prod.snd hpp)
      rw [hb] at this
      omega
    -- so the block sums to a finite multiple of `x₂`
    obtain ⟨r', hr'⟩ := exists_nsmul_finsum
      (Cardinal.lt_aleph0_iff_set_finite.mp (D.I_small (a, K + 1)))
      (fun i => (⟨familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i, hFm i⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
      (⟨x₂, hx₂T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))
      (fun i hi => by
        rcases hno i hi with h | h
        · exact ⟨1, by rw [one_smul]; exact Subtype.ext h⟩
        · exact ⟨0, by rw [zero_smul]; exact Subtype.ext h⟩)
    have hblock : D.v (a, K + 1) + D.u (a, K + 1)
        = r' • (⟨x₂, hx₂T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) := by
      rw [← hr', ← LMonoid.lsumOf_eq_finsum (D.I_small (a, K + 1))]
      exact (D.hI (a, K + 1)).symm
    -- read the equation in `H` and use that `x₁ ∉ add x₂`
    have hblockH : (D.v (a, K + 1) : H) + (D.u (a, K + 1) : H) = r' • x₂ := by
      have := congrArg Subtype.val hblock
      rwa [coe_nsmul_addOf x₁ x₂ r' ⟨x₂, hx₂T⟩] at this
    have hvadd : (D.v (a, K + 1) : H) ∈ KMonoid.addOf (κ := ℵ₀) x₂ :=
      ⟨(D.u (a, K + 1) : H), r', by rw [KMonoid.cmul_natCast]; exact hblockH⟩
    obtain ⟨F, hF⟩ := exists_form x₁ x₂ hgen ((D.v (a, K + 1) : H))
    have hF1 : F.1 = 0 := by
      by_contra hne
      obtain ⟨w, hw⟩ := self_addLe_ecmul hne x₁
      exact hmem ⟨w + ecmul F.2 x₂ + (D.u (a, K + 1) : H), r', by
        rw [KMonoid.cmul_natCast, ← hblockH, ← hF, eval, ← hw]
        abel⟩
    have hF2 : F.2 ≠ ⊤ := by
      intro htop
      obtain ⟨G, hG⟩ := exists_form x₁ x₂ hgen ((D.u (a, K + 1) : H))
      refine hmix (r' • x₂) ⟨⟨(0, (r' : ℕ∞)), ⟨by simp, by simp⟩, ?_⟩, ⟨(G.1, ⊤), Or.inr rfl, ?_⟩⟩
      · rw [eval, ecmul_zero, zero_add, ecmul_natCast]
      · have hu : ecmul (⊤ : ℕ∞) x₂ + ecmul G.2 x₂ = ecmul (⊤ : ℕ∞) x₂ := by
          rw [← ecmul_add, top_add]
        calc eval x₁ x₂ (G.1, ⊤) = ecmul G.1 x₁ + ecmul (⊤ : ℕ∞) x₂ := rfl
          _ = ecmul G.1 x₁ + (ecmul (⊤ : ℕ∞) x₂ + ecmul G.2 x₂) := by rw [hu]
          _ = ecmul (⊤ : ℕ∞) x₂ + (ecmul G.1 x₁ + ecmul G.2 x₂) := by abel
          _ = eval x₁ x₂ F + eval x₁ x₂ G := by
                rw [eval, eval, hF1, htop, ecmul_zero, zero_add]
          _ = (D.v (a, K + 1) : H) + (D.u (a, K + 1) : H) := by rw [hF, hG]
          _ = r' • x₂ := hblockH
    obtain ⟨g, hg⟩ : ∃ g : ℕ, F.2 = (g : ℕ∞) := ⟨F.2.toNat, (ENat.natCast_toNat hF2).symm⟩
    refine ⟨g, Subtype.ext ?_⟩
    rw [coe_nsmul_addOf x₁ x₂ g ⟨x₂, hx₂T⟩]
    show (D.v (a, K + 1) : H) = g • x₂
    rw [← hF, eval, hF1, hg, ecmul_zero, zero_add, ecmul_natCast]
  obtain ⟨r, hr⟩ := hV
  -- telescope, and read off the finite relation
  have htel := D.telescope hAfin K
  rw [← hrectsum D.J D.J_disjoint D.J_small
      (fun i => (⟨familyOfForm x₁ x₂ ((n : ℕ∞), ⊤) i, hGm i⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))),
    ← hrectsum D.I D.I_disjoint D.I_small
      (fun i => (⟨familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i, hFm i⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))),
    hp, hq, hr] at htel
  have htelH : n • x₁ + q • x₂ = m • x₁ + p • x₂ + r • x₂ := by
    have hc : ((n • (⟨x₁, hx₁T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) :
          ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H)
        + ((q • (⟨x₂, hx₂T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) :
          ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H)
        = ((m • (⟨x₁, hx₁T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) :
            ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H)
          + ((p • (⟨x₂, hx₂T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) :
            ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H)
          + ((r • (⟨x₂, hx₂T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) :
            ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) := congrArg Subtype.val htel
    rwa [coe_nsmul_addOf x₁ x₂ n ⟨x₁, hx₁T⟩, coe_nsmul_addOf x₁ x₂ q ⟨x₂, hx₂T⟩,
      coe_nsmul_addOf x₁ x₂ m ⟨x₁, hx₁T⟩, coe_nsmul_addOf x₁ x₂ p ⟨x₂, hx₂T⟩,
      coe_nsmul_addOf x₁ x₂ r ⟨x₂, hx₂T⟩] at hc
  refine ⟨p + r, q, ?_⟩
  rw [eval, eval, ecmul_natCast, ecmul_natCast, ecmul_natCast, ecmul_natCast, add_nsmul,
    ← add_assoc, ← htelH]

/-- **`ℵ₀ x₂` absorbs any number of copies of `x₁`** as soon as `x₁ ∈ add x₂`: from `x₁ + z = n x₂`
one gets `β x₁ ≼ ℵ₀ x₁ ≼ ℵ₀ (n x₂) = ℵ₀ x₂`, and Lemma 2.8(2) (`add_cmul_top_eq`) turns a summand of
`ℵ₀ x₂` into an absorbed one.  The degenerate case `n = 0` forces `x₁ = 0` by reducedness. -/
theorem cmul_top_absorb (h : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂) (β : ℕ∞) :
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ + ecmul β x₁
      = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ := by
  obtain ⟨z, n, hzn⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `0 · x₂ = 0`, so `x₁ = 0` and there is nothing to absorb
    have h0 : x₁ + z = 0 := by
      rw [hzn, KMonoid.cmul_congr (by rw [Nat.cast_zero] : ((0 : ℕ) : Cardinal.{u}) = 0) _ zero_le,
        KMonoid.cmul_zero_cardinal]
    rw [(KMonoid.isConical (ℵ₀ : Cardinal.{u}) H x₁ z h0).1, ecmul, KMonoid.cmul_zero, add_zero]
  · -- `ℵ₀ · n = ℵ₀`
    have hmul : (ℵ₀ : Cardinal.{u}) * ((n : ℕ) : Cardinal.{u}) = ℵ₀ :=
      Cardinal.mul_eq_left le_rfl (le_of_lt Cardinal.natCast_lt_aleph0)
        (by exact_mod_cast hn.ne')
    have hnκ : ((n : ℕ) : Cardinal.{u}) ≤ ℵ₀ := le_of_lt Cardinal.natCast_lt_aleph0
    -- `ℵ₀ x₁ + ℵ₀ z = ℵ₀ (x₁ + z) = ℵ₀ (n x₂) = ℵ₀ x₂`
    have hstep : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl z
        = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ := by
      rw [← KMonoid.cmul_top_distrib, hzn, KMonoid.cmul_cmul le_rfl hnκ (le_of_eq hmul),
        KMonoid.cmul_congr hmul (le_of_eq hmul) le_rfl x₂]
    -- so `β x₁ ≼ ℵ₀ x₁ ≼ ℵ₀ x₂`
    obtain ⟨w, hw⟩ : ecmul β x₁ ≼ KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ :=
      AddLe.trans
        (KMonoid.cmul_le_cmul (Cardinal.ofENat_le_aleph0 β) le_rfl
          (Cardinal.ofENat_le_aleph0 β) x₁)
        ⟨KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl z, hstep⟩
    rw [add_comm]
    exact KMonoid.add_cmul_top_eq hw

/-- **Lemma 5.2(5)**: if `H` is braided over `add (x₁ + x₂)`, then `x₁ ∈ add x₂` exactly when
`ℵ₀ (x₁ + x₂) = ℵ₀ x₂`.

Forward is `cmul_top_absorb`: `ℵ₀ x₂` swallows `ℵ₀ x₁`.

Backward is where the work is.  The paper's "we conclude that there exist positive integers `m`,
`n`" hides a block induction, which the formal proof runs explicitly.  Braid the constant families
`(x₁ + x₂)` and `(x₂)` — they have the same `ℵ₀`-sum by hypothesis — and let `k` be the least
level of the block `a` whose `I`-piece is nonempty.  Below `k` the `I`-pieces are empty, so
`v + u = 0` there and reducedness of `H` kills both; the `J`-equation one level down then reads
`v (a,k) = r x₂` with `r = #J (a,k-1)` finite (and `v (a,0) = 0` when `k = 0`).  The two braiding
equations at level `k` now give

    m (x₁ + x₂) = r x₂ + u (a,k)    and    u (a,k) + v (a,k+1) = s x₂,

with `m = #I (a,k) ≥ 1` and `s = #J (a,k)`, so `x₁ ≼ m (x₁ + x₂) ≼ (r + s) x₂`. -/
theorem lemma_5_2_five
    (hbr : letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
      IsBraidedOver ℵ₀ ℵ₀ ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) H le_rfl (fun y => (y : H))) :
    x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂ ↔
      KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (x₁ + x₂) = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ := by
  classical
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  constructor
  · -- `ℵ₀ (x₁ + x₂) = ℵ₀ x₁ + ℵ₀ x₂ = ℵ₀ x₂`
    intro h
    rw [KMonoid.cmul_top_distrib, add_comm]
    have habs := cmul_top_absorb x₁ x₂ h ⊤
    rwa [ecmul_top] at habs
  intro heq
  -- the two constant families, in `add (x₁ + x₂)`
  have hx12 : x₁ + x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) := KMonoid.self_mem_addOf _
  have hx2 : x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ hx12 x₂ x₁ (add_comm x₁ x₂)
  have hsum : (KMonoid.ksum (κ := ℵ₀) fun _ : Idx (ℵ₀ : Cardinal.{u}) => x₁ + x₂)
      = KMonoid.ksum (κ := ℵ₀) fun _ : Idx (ℵ₀ : Cardinal.{u}) => x₂ := by
    rw [ksum_const, ksum_const]; exact heq
  obtain ⟨D⟩ := hbr.braided (fun _ => ⟨x₁ + x₂, hx12⟩) (fun _ => ⟨x₂, hx2⟩) hsum
  -- the braiding equations, read in `H` (the coercion of a `λ⁻`-sum *is* the ambient sum)
  have hIcoe : ∀ q : Idx (ℵ₀ : Cardinal.{u}) × ℕ,
      KMonoid.sumOf (κ := ℵ₀) (D.I_small q).le (fun _ : D.I q => x₁ + x₂)
        = ((D.v q : H) + (D.u q : H)) := fun q => congrArg Subtype.val (D.hI q)
  have hJcoe : ∀ (b : Idx (ℵ₀ : Cardinal.{u})) (j : ℕ),
      KMonoid.sumOf (κ := ℵ₀) (D.J_small (b, j)).le (fun _ : D.J (b, j) => x₂)
        = ((D.v (b, j + 1) : H) + (D.u (b, j) : H)) :=
    fun b j => congrArg Subtype.val (D.hJ (b, j))
  -- some block has a nonempty `I`-piece; take the least level of that block at which it does
  obtain ⟨i₀⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  obtain ⟨⟨a, k₀⟩, hp⟩ : ∃ q, i₀ ∈ D.I q :=
    Set.mem_iUnion.mp (by rw [D.I_cover]; trivial)
  have hex : ∃ k : ℕ, (D.I (a, k)).Nonempty := ⟨k₀, ⟨i₀, hp⟩⟩
  obtain ⟨k, hk, hlow⟩ : ∃ k : ℕ, (D.I (a, k)).Nonempty ∧ ∀ j < k, D.I (a, j) = ∅ :=
    ⟨Nat.find hex, Nat.find_spec hex,
      fun j hj => Set.not_nonempty_iff_eq_empty.mp (Nat.find_min hex hj)⟩
  -- below level `k` both braiding families vanish, by reducedness
  have hzero : ∀ j < k, (D.v (a, j) : H) = 0 ∧ (D.u (a, j) : H) = 0 := by
    intro j hj
    obtain ⟨m, hm, hmsum⟩ := sumOf_const_finite (D.I_small (a, j)) (x₁ + x₂)
    have hm0 : m = 0 := by
      have : ((m : ℕ) : Cardinal.{u}) = 0 := by rw [← hm, hlow j hj]; simp
      exact_mod_cast this
    refine KMonoid.isConical (ℵ₀ : Cardinal.{u}) H _ _ ?_
    rw [← hIcoe (a, j), hmsum, hm0, zero_nsmul]
  -- so `v (a,k)` is a finite multiple of `x₂`
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (D.v (a, k) : H) = r • x₂ := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact ⟨0, by rw [D.v_limit a, zero_nsmul]; rfl⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    obtain ⟨s, _, hssum⟩ := sumOf_const_finite (D.J_small (a, j)) x₂
    have hj := hJcoe a j
    rw [hssum, (hzero j (Nat.lt_succ_self j)).2, add_zero] at hj
    exact ⟨s, hj.symm⟩
  -- and `u (a,k)` is a summand of a finite multiple of `x₂`
  obtain ⟨s, _, hssum⟩ := sumOf_const_finite (D.J_small (a, k)) x₂
  have hu : (D.u (a, k) : H) + (D.v (a, k + 1) : H) = s • x₂ := by
    have h := hJcoe a k
    rw [hssum] at h
    rw [h]
    exact add_comm _ _
  -- the `I`-equation at level `k`, with `m ≥ 1` copies of `x₁ + x₂`
  obtain ⟨m, hmcard, hmsum⟩ := sumOf_const_finite (D.I_small (a, k)) (x₁ + x₂)
  have hIeq : m • (x₁ + x₂) = r • x₂ + (D.u (a, k) : H) := by
    rw [← hmsum, hIcoe (a, k), hr]
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [h0, Nat.cast_zero] at hmcard
    exact Cardinal.mk_ne_zero_iff.mpr hk.to_subtype hmcard
  -- read off `x₁ + z = (r + s) x₂`
  refine ⟨x₂ + m' • (x₁ + x₂) + (D.v (a, k + 1) : H), r + s, ?_⟩
  have hsplit : x₁ + (x₂ + m' • (x₁ + x₂)) = (m' + 1) • (x₁ + x₂) := by
    rw [succ_nsmul, ← add_assoc]
    exact add_comm _ _
  rw [KMonoid.cmul_natCast, add_nsmul]
  calc x₁ + (x₂ + m' • (x₁ + x₂) + (D.v (a, k + 1) : H))
      = (x₁ + (x₂ + m' • (x₁ + x₂))) + (D.v (a, k + 1) : H) := (add_assoc _ _ _).symm
    _ = (m' + 1) • (x₁ + x₂) + (D.v (a, k + 1) : H) := by rw [hsplit]
    _ = (r • x₂ + (D.u (a, k) : H)) + (D.v (a, k + 1) : H) := by rw [hIeq]
    _ = r • x₂ + ((D.u (a, k) : H) + (D.v (a, k + 1) : H)) := add_assoc _ _ _
    _ = r • x₂ + s • x₂ := by rw [hu]

end Lemma52

/-! ## Theorem 5.3 (`hereditarycasecor`)

The main result of the section. -/

section Theorem53

variable (x₁ x₂ : H)

/-- Condition (i) of Theorem 5.3, for the ordered pair `(a, b)` of generators. -/
def Cond1 (a b : H) : Prop :=
  ∀ n : ℕ, KMonoid.cmul (κ := ℵ₀) (n : Cardinal.{u})
        (le_trans (le_of_lt Cardinal.natCast_lt_aleph0) le_rfl) a
      + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b
    = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl a + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b →
      KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b
          = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl a + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b
        ∧ a ∈ KMonoid.addOf (κ := ℵ₀) b

/-- Condition (ii) of Theorem 5.3, for the ordered pair `(a, b)` of generators. -/
def Cond2 (a b : H) : Prop :=
  a ∉ KMonoid.addOf (κ := ℵ₀) b →
    ∀ m n : ℕ, eval a b ((m : ℕ∞), ⊤) = eval a b ((n : ℕ∞), ⊤) →
      ∃ k k' : ℕ, eval a b ((m : ℕ∞), (k : ℕ∞)) = eval a b ((n : ℕ∞), (k' : ℕ∞))

/-! ### Moving between `FormIdx` and `Idx ℵ₀`

`BraidedForms` compares families indexed by `FormIdx`, while `IsBraidedOver.braided` speaks about
families indexed by `Idx ℵ₀`.  Both index types are countable, and `IsBraided.comp_equiv` moves a
braiding across the identification. -/

/-- A fixed identification of the slots of a form with the index type of an `ℵ₀`-sum. -/
noncomputable def formIdxEquiv : FormIdx.{u} ≃ Idx (ℵ₀ : Cardinal.{u}) :=
  (Cardinal.eq.mp (mk_formIdx.{u}.trans (mk_Idx (ℵ₀ : Cardinal.{u})).symm)).some

/-- The `ℵ₀`-sum of a form's family, read along `formIdxEquiv`, is the element the form
represents. -/
theorem ksum_familyOfForm (F : Form) :
    KMonoid.ksum (κ := ℵ₀) (fun i => familyOfForm x₁ x₂ F (formIdxEquiv.{u}.symm i))
      = eval x₁ x₂ F := by
  rw [← sumOf_familyOfForm x₁ x₂ F, ← KMonoid.sumOf_Idx]
  exact (KMonoid.sumOf_equiv mk_formIdx_le_aleph0 (le_of_eq (mk_Idx _))
    formIdxEquiv.{u}.symm (familyOfForm x₁ x₂ F)).symm

/-- **Two forms of the same element are braided**, as soon as `H` is braided over `add (x₁ + x₂)`.
This is what turns the hypothesis of Theorem 5.3's forward direction into the input of Lemma
5.2. -/
theorem braidedForms_of_braidedOver
    (hbr : letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
      IsBraidedOver ℵ₀ ℵ₀ ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) H le_rfl (fun y => (y : H)))
    (F G : Form) (heq : eval x₁ x₂ F = eval x₁ x₂ G)
    (hFm : ∀ i, familyOfForm x₁ x₂ F i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ i, familyOfForm x₁ x₂ G i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ F G hFm hGm := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  have hsum : (KMonoid.ksum (κ := ℵ₀) fun i =>
        ((⟨familyOfForm x₁ x₂ F (formIdxEquiv.{u}.symm i), hFm _⟩ :
          ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H))
      = KMonoid.ksum (κ := ℵ₀) fun i =>
        ((⟨familyOfForm x₁ x₂ G (formIdxEquiv.{u}.symm i), hGm _⟩ :
          ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) := by
    rw [show (fun i => ((⟨familyOfForm x₁ x₂ F (formIdxEquiv.{u}.symm i), hFm _⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H))
      = (fun i => familyOfForm x₁ x₂ F (formIdxEquiv.{u}.symm i)) from rfl,
      show (fun i => ((⟨familyOfForm x₁ x₂ G (formIdxEquiv.{u}.symm i), hGm _⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H))
      = (fun i => familyOfForm x₁ x₂ G (formIdxEquiv.{u}.symm i)) from rfl,
      ksum_familyOfForm, ksum_familyOfForm]
    exact heq
  have h := (hbr.braided _ _ hsum).comp_equiv formIdxEquiv.{u}
  show IsBraided (ℵ₀ : Cardinal.{u}) _ _
  convert h using 2 <;> simp

/-- `NoMixedForms` does not depend on the order of the generators. -/
theorem eval_swap (a b : H) (F : Form) : eval a b F = eval b a (F.2, F.1) := by
  rw [eval, eval, add_comm]

theorem noMixedForms_swap (h : NoMixedForms x₁ x₂) : NoMixedForms x₂ x₁ := by
  rintro y ⟨⟨F, hF, hFe⟩, ⟨G, hG, hGe⟩⟩
  exact h y ⟨⟨(F.2, F.1), ⟨hF.2, hF.1⟩, by rw [← hFe, eval_swap]⟩,
    ⟨(G.2, G.1), by rcases hG with h | h; exacts [Or.inr h, Or.inl h], by rw [← hGe, eval_swap]⟩⟩

/-- The two orderings of the generators give the same `add (x₁ + x₂)`. -/
theorem addOf_add_swap : KMonoid.addOf (κ := ℵ₀) (x₂ + x₁) = KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) := by
  rw [add_comm]

/-- A distinguished term of a finite sum is a summand of it. -/
theorem addLe_finsum_mem {M : Type v} [AddCommMonoid M] {ι : Type u} {S : Set ι} (hS : S.Finite)
    (f : ι → M) {i : ι} (hi : i ∈ S) : ∃ c, f i + c = ∑ᶠ j ∈ S, f j := by
  classical
  have hins : insert i (S \ {i}) = S := by
    rw [Set.insert_diff_singleton, Set.insert_eq_of_mem hi]
  refine ⟨∑ᶠ j ∈ (S \ {i}), f j, ?_⟩
  conv_rhs => rw [← hins]
  exact (finsum_mem_insert f (fun h => h.2 rfl) (hS.subset Set.diff_subset)).symm

/-- **The counting step of Theorem 5.3(i)**.

If a form with finitely many copies of `x₁` is braided with `ℵ₀ X₁ + ℵ₀ X₂`, then `x₁ ∈ add x₂`.

This is the paper's "all but finitely many blocks sum to `|I_μ| x_j`, while the other form has
infinitely many copies of `x_i`".  Only finitely many `I`-blocks meet the `x₁`-slots of the finite
form, but infinitely many `J`-blocks meet the `x₁`-slots of `ℵ₀ X₁ + ℵ₀ X₂` (each block is finite).
So some position `p` has `x₁` inside `J p` while neither `I p` nor `I (p+1)` meets an `x₁`-slot;
then `u p` and `v (p+1)` are both summands of finite multiples of `x₂`, and

    x₁ ≼ Σ_{J p} y = v (p+1) + u p ≼ (r + r') x₂. -/
theorem mem_addOf_of_braidedForms_top (n : ℕ)
    (hFm : ∀ i, familyOfForm x₁ x₂ ((n : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ i, familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hbr : BraidedForms x₁ x₂ ((n : ℕ∞), ⊤) ((⊤ : ℕ∞), ⊤) hFm hGm) :
    x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂ := by
  classical
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  have hx₂T : x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  obtain ⟨D⟩ := hbr
  -- the `I`-blocks meeting an `x₁`-slot of the finite form, and their `bsucc`-predecessors
  have hBad : ((fun i => IsBraided.blockOf D.I D.I_cover i) '' oneSlots.{u} n).Finite :=
    (finite_oneSlots n).image _
  have hBad' : (((fun i => IsBraided.blockOf D.I D.I_cover i) '' oneSlots.{u} n)
      ∪ bsucc ⁻¹' ((fun i => IsBraided.blockOf D.I D.I_cover i) '' oneSlots.{u} n)).Finite :=
    hBad.union (hBad.preimage (Function.Injective.injOn bsucc_injective))
  -- the `J`-blocks meeting an `x₁`-slot of `ℵ₀ X₁ + ℵ₀ X₂`: infinitely many
  have hWinf : (Set.range (Sum.inl : Nats.{u} → FormIdx.{u})).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun j : Nats.{u} => (Sum.inl j : FormIdx.{u}))
      (fun a b hab => by simpa using hab) (fun j => Set.mem_range_self j)
  have hGoodinf : ((fun i => IsBraided.blockOf D.J D.J_cover i) ''
      (Set.range (Sum.inl : Nats.{u} → FormIdx.{u}))).Infinite := by
    intro hfin
    refine hWinf ?_
    refine Set.Finite.subset (hfin.biUnion fun p _ =>
      Cardinal.lt_aleph0_iff_set_finite.mp (D.J_small p)) fun i hi => ?_
    exact Set.mem_biUnion (Set.mem_image_of_mem _ hi) (IsBraided.mem_blockOf D.J D.J_cover i)
  obtain ⟨p, hpGood, hpBad⟩ := (hGoodinf.diff hBad').nonempty
  -- at `p` and at `p + 1` the `I`-blocks carry only `x₂`
  have hIblock : ∀ q : FormIdx.{u} × ℕ,
      q ∉ (fun i => IsBraided.blockOf D.I D.I_cover i) '' oneSlots.{u} n →
      ∃ r : ℕ, D.v q + D.u q = r • (⟨x₂, hx₂T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) := by
    intro q hq
    obtain ⟨r, hr⟩ := exists_nsmul_finsum (Cardinal.lt_aleph0_iff_set_finite.mp (D.I_small q))
      (fun i => (⟨familyOfForm x₁ x₂ ((n : ℕ∞), ⊤) i, hFm i⟩ :
        ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
      (⟨x₂, hx₂T⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))
      (fun i hi => by
        have hone : i ∉ oneSlots.{u} n := fun hmem =>
          hq ⟨i, hmem, IsBraided.blockOf_eq D.I_disjoint D.I_cover hi⟩
        rcases familyOfForm_eq_of_notMem_oneSlots x₁ x₂ hone with h | h
        · exact ⟨1, by rw [one_smul]; exact Subtype.ext h⟩
        · exact ⟨0, by rw [zero_smul]; exact Subtype.ext h⟩)
    exact ⟨r, by rw [← hr, ← LMonoid.lsumOf_eq_finsum (D.I_small q)]; exact (D.hI q).symm⟩
  obtain ⟨r, hr⟩ := hIblock p fun h => hpBad (Set.mem_union_left _ h)
  obtain ⟨r', hr'⟩ := hIblock (bsucc p) fun h => hpBad (Set.mem_union_right _ h)
  -- and `x₁` is a summand of the `J`-block at `p`
  obtain ⟨i₀, hi₀J, hi₀W⟩ : ∃ i, i ∈ D.J p ∧ i ∈ Set.range (Sum.inl : Nats.{u} → FormIdx.{u}) := by
    obtain ⟨i, hiW, hip⟩ := hpGood
    exact ⟨i, hip ▸ IsBraided.mem_blockOf D.J D.J_cover i, hiW⟩
  obtain ⟨j, rfl⟩ := hi₀W
  obtain ⟨c, hc⟩ := addLe_finsum_mem (Cardinal.lt_aleph0_iff_set_finite.mp (D.J_small p))
    (fun i => (⟨familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) i, hGm i⟩ :
      ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) hi₀J
  have hJp : (∑ᶠ i ∈ D.J p, (⟨familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) i, hGm i⟩ :
      ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) = D.v (bsucc p) + D.u p := by
    rw [← LMonoid.lsumOf_eq_finsum (D.J_small p)]
    exact D.hJ p
  rw [hJp] at hc
  -- read the whole thing in `H`
  have hval : (familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) (Sum.inl j)) = x₁ := by
    rw [familyOfForm_inl]
    exact if_pos (WithTop.coe_lt_top (j.down : ℕ))
  have hcH : x₁ + (c : H) = (D.v (bsucc p) : H) + (D.u p : H) := by
    have hcc : ((⟨familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) (Sum.inl j), hGm _⟩ :
          ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) + (c : H)
        = (D.v (bsucc p) : H) + (D.u p : H) := congrArg Subtype.val hc
    rwa [show ((⟨familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) (Sum.inl j), hGm _⟩ :
      ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) : H) = x₁ from hval] at hcc
  have hrH : (D.v p : H) + (D.u p : H) = r • x₂ := by
    have := congrArg Subtype.val hr
    rwa [coe_nsmul_addOf x₁ x₂ r ⟨x₂, hx₂T⟩] at this
  have hr'H : (D.v (bsucc p) : H) + (D.u (bsucc p) : H) = r' • x₂ := by
    have := congrArg Subtype.val hr'
    rwa [coe_nsmul_addOf x₁ x₂ r' ⟨x₂, hx₂T⟩] at this
  refine ⟨(c : H) + (D.u (bsucc p) : H) + (D.v p : H), r' + r, ?_⟩
  rw [KMonoid.cmul_natCast, add_nsmul, ← hr'H, ← hrH]
  calc x₁ + ((c : H) + (D.u (bsucc p) : H) + (D.v p : H))
      = (x₁ + (c : H)) + (D.u (bsucc p) : H) + (D.v p : H) := by abel
    _ = ((D.v (bsucc p) : H) + (D.u p : H)) + (D.u (bsucc p) : H) + (D.v p : H) := by rw [hcH]
    _ = ((D.v (bsucc p) : H) + (D.u (bsucc p) : H)) + ((D.v p : H) + (D.u p : H)) := by abel

/-- Condition (i) of Theorem 5.3 holds as soon as `H` is braided over `add (x₁ + x₂)`: the
counting step gives `x₁ ∈ add x₂`, and then `ℵ₀ x₂` absorbs `ℵ₀ x₁`. -/
theorem cond1_of_braidedOver
    (hbr : letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
      IsBraidedOver ℵ₀ ℵ₀ ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) H le_rfl (fun y => (y : H))) :
    Cond1 x₁ x₂ := by
  intro n hn
  have heval : eval x₁ x₂ ((n : ℕ∞), ⊤) = eval x₁ x₂ ((⊤ : ℕ∞), ⊤) := by
    show ecmul ((n : ℕ) : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂ = ecmul (⊤ : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂
    rw [ecmul_natCast, ecmul_top, ecmul_top, ← KMonoid.cmul_natCast x₁ n]
    exact hn
  have hmem : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂ :=
    mem_addOf_of_braidedForms_top x₁ x₂ n (familyOfForm_mem x₁ x₂ _) (familyOfForm_mem x₁ x₂ _)
      (braidedForms_of_braidedOver x₁ x₂ hbr _ _ heval _ _)
  refine ⟨?_, hmem⟩
  have habs := cmul_top_absorb x₁ x₂ hmem ⊤
  rw [ecmul_top] at habs
  exact habs.symm.trans (add_comm _ _)

/-- **Theorem 5.3, forward direction**: if `H ≅ V^{ℵ₀}(R)` for a ring whose projectives are direct
sums of finitely generated modules, then the three conditions hold for both orderings of the
generators.

Lemma 5.1 supplies the braiding over `add (x₁ + x₂)`; (iii) is then Lemma 5.2(1), (ii) is Lemma
5.2(4), and (i) is `cond1_of_braidedOver`. -/
theorem theorem_5_3_forward (R : Type u) [Ring R] (hfg : EveryProjectiveIsSumOfFG R)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H))
    (e : (projClass R ℵ₀ le_rfl).carrier → H)
    (hhom : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl; KMonoid.IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) :
    Cond1 x₁ x₂ ∧ Cond1 x₂ x₁ ∧ Cond2 x₁ x₂ ∧ Cond2 x₂ x₁ ∧ NoMixedForms x₁ x₂ := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  -- invert the isomorphism and feed Lemma 5.1
  obtain ⟨e', hleft, hright⟩ : ∃ g : H → (projClass R ℵ₀ le_rfl).carrier,
      Function.LeftInverse g e ∧ Function.RightInverse g e :=
    ⟨(Equiv.ofBijective e hbij).symm, (Equiv.ofBijective e hbij).left_inv,
      (Equiv.ofBijective e hbij).right_inv⟩
  have hbrH := lemma_5_1 R hfg x₁ x₂ hgen hnoncyclic e' (hhom.inv hbij hright)
    ⟨hright.injective, hleft.surjective⟩
  have hgen' : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₂, x₁} : Set H) := by
    rwa [Set.pair_comm]
  have hbrH' := IsBraidedOver.of_set_eq Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₂ + x₁))
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)) (addOf_add_swap x₁ x₂) hbrH
  have hne := ne_zero_of_not_cyclic x₁ x₂ hgen hnoncyclic
  -- (iii): a finite and an infinite form of the same element would be braided
  have hmix : NoMixedForms x₁ x₂ := by
    rintro y ⟨⟨F, hF, hFe⟩, ⟨G, hG, hGe⟩⟩
    exact lemma_5_2_one x₁ x₂ G F hG hF hne.1 hne.2
      (familyOfForm_mem x₁ x₂ G) (familyOfForm_mem x₁ x₂ F)
      (braidedForms_of_braidedOver x₁ x₂ hbrH G F (hGe.trans hFe.symm) _ _)
  refine ⟨cond1_of_braidedOver x₁ x₂ hbrH, cond1_of_braidedOver x₂ x₁ hbrH',
    fun hnotmem m n heq => ?_, fun hnotmem m n heq => ?_, hmix⟩
  · exact lemma_5_2_four x₁ x₂ hnotmem hmix hgen m n
      (familyOfForm_mem x₁ x₂ _) (familyOfForm_mem x₁ x₂ _)
      (braidedForms_of_braidedOver x₁ x₂ hbrH _ _ heq
        (familyOfForm_mem x₁ x₂ _) (familyOfForm_mem x₁ x₂ _))
  · exact lemma_5_2_four x₂ x₁ hnotmem (noMixedForms_swap x₁ x₂ hmix) hgen' m n
      (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _)
      (braidedForms_of_braidedOver x₂ x₁ hbrH' _ _ heq
        (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _))

/-! ### The four cases of Theorem 5.3's backward direction -/

/-- Braidedness of two families over a `λ⁻`-closed subset depends only on the subset: two proofs
that the same set is closed give definitionally equal monoid structures (trap 13). -/
theorem isBraided_base_eq {S T : Set H} (hS : IsLSubset (ℵ₀ : Cardinal.{u}) le_rfl S)
    (hT : IsLSubset (ℵ₀ : Cardinal.{u}) le_rfl T) (hST : S = T) {ι : Type u} (f g : ι → H)
    (hfS : ∀ i, f i ∈ S) (hgS : ∀ i, g i ∈ S) (hfT : ∀ i, f i ∈ T) (hgT : ∀ i, g i ∈ T)
    (h : letI := hS.lmonoid Cardinal.isRegular_aleph0
      IsBraided ℵ₀ (fun i => (⟨f i, hfS i⟩ : ↥S)) (fun i => (⟨g i, hgS i⟩ : ↥S))) :
    letI := hT.lmonoid Cardinal.isRegular_aleph0
    IsBraided ℵ₀ (fun i => (⟨f i, hfT i⟩ : ↥T)) (fun i => (⟨g i, hgT i⟩ : ↥T)) := by
  subst hST
  exact h

/-- Swapping the generators swaps the two halves of `FormIdx` and the two coefficients. -/
theorem braidedForms_swap {F G : Form}
    (hFm : ∀ i, familyOfForm x₂ x₁ F i ∈ KMonoid.addOf (κ := ℵ₀) (x₂ + x₁))
    (hGm : ∀ i, familyOfForm x₂ x₁ G i ∈ KMonoid.addOf (κ := ℵ₀) (x₂ + x₁))
    (h : BraidedForms x₂ x₁ F G hFm hGm)
    (hFm' : ∀ i, familyOfForm x₁ x₂ (F.2, F.1) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm' : ∀ i, familyOfForm x₁ x₂ (G.2, G.1) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ (F.2, F.1) (G.2, G.1) hFm' hGm' := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  have hmemF : ∀ i, familyOfForm x₂ x₁ F i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) := by
    intro i
    rw [← addOf_add_swap x₁ x₂]
    exact hFm i
  have hmemG : ∀ i, familyOfForm x₂ x₁ G i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) := by
    intro i
    rw [← addOf_add_swap x₁ x₂]
    exact hGm i
  have hbase : IsBraided (ℵ₀ : Cardinal.{u})
      (fun i => (⟨familyOfForm x₂ x₁ F i, hmemF i⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
      (fun i => (⟨familyOfForm x₂ x₁ G i, hmemG i⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) :=
    isBraided_base_eq (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₂ + x₁))
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)) (addOf_add_swap x₁ x₂)
      (familyOfForm x₂ x₁ F) (familyOfForm x₂ x₁ G) hFm hGm hmemF hmemG h
  have h' := hbase.comp_equiv (Equiv.sumComm Nats.{u} Nats.{u})
  have hEq : ∀ (K : Form) (hK : ∀ i, familyOfForm x₂ x₁ K i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
      (hK' : ∀ i, familyOfForm x₁ x₂ (K.2, K.1) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)),
      (fun i => (⟨familyOfForm x₂ x₁ K ((Equiv.sumComm Nats.{u} Nats.{u}) i), hK _⟩ :
          ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
        = (fun i => (⟨familyOfForm x₁ x₂ (K.2, K.1) i, hK' i⟩ :
          ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) := by
    intro K hK hK'
    funext i
    refine Subtype.ext ?_
    rcases i with j | j <;> rfl
  rw [hEq F hmemF hFm', hEq G hmemG hGm'] at h'
  exact h'

/-- **A finite relation gives a braiding of the two infinite forms**: if
`m x₁ + k x₂ = m' x₁ + k' x₂` with all four finite, then `m X₁ + ℵ₀ X₂` and `m' X₁ + ℵ₀ X₂` are
braided.  Block `0` holds the `m` copies of `x₁` and the first `k` copies of `x₂` against the `m'`
copies and the first `k'`; every later block matches one copy of `x₂` against one copy of `x₂`.
This is the paper's "from this we can easily construct a braiding". -/
theorem braidedForms_of_finite_relation (m k m' k' : ℕ)
    (hrel : eval x₁ x₂ ((m : ℕ∞), (k : ℕ∞)) = eval x₁ x₂ ((m' : ℕ∞), (k' : ℕ∞)))
    (hFm : ∀ i, familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ i, familyOfForm x₁ x₂ ((m' : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ ((m : ℕ∞), ⊤) ((m' : ℕ∞), ⊤) hFm hGm := by
  classical
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  have hx₁T : x₁ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  have hbase : (m • x₁ + k • x₂) ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    addOf_add_mem (addOf_nsmul_mem hx₁T m) (addOf_nsmul_mem hx₂T k)
  -- the two level functions: the finite parts on level `0`, then one copy of `x₂` per level
  have hfin : ∀ (c : ℕ) (l : ℕ),
      {j : Nats.{u} | (if j.down < c then 0 else (j.down - c) + 1) = l}.Finite := by
    intro c l
    rcases l with _ | L
    · rw [levelA_fiber_zero]; exact finite_nats_lt c
    · rw [levelA_fiber_succ]; exact finite_nats_eq (c + L)
  refine IsBraided.of_levels (Sum.inl (ULift.up 0))
    (Sum.elim (fun j => if j.down < m then 0 else (j.down - m) + 1)
      (fun j => if j.down < k then 0 else (j.down - k) + 1))
    (Sum.elim (fun j => if j.down < m' then 0 else (j.down - m') + 1)
      (fun j => if j.down < k' then 0 else (j.down - k') + 1))
    (fun l => finite_fiber_elim (hfin m l) (hfin k l))
    (fun l => finite_fiber_elim (hfin m' l) (hfin k' l))
    (fun l => if l = 0 then ⟨m • x₁ + k • x₂, hbase⟩ else ⟨x₂, hx₂T⟩) (fun _ => 0) rfl
    (fun l => ?_) (fun l => ?_)
  · refine Subtype.ext ?_
    rw [coe_finsum_mem x₁ x₂ (finite_fiber_elim (hfin m l) (hfin k l)) _ hFm]
    rcases l with _ | L
    · rw [finsum_fiber_const (a := x₁) (b := x₂) (hfin m 0) (hfin k 0) _
        (fun j hj => by
          rw [levelA_fiber_zero] at hj
          rw [familyOfForm_inl]
          refine if_pos ?_
          show ((j.down : ℕ) : ℕ∞) < ((m : ℕ) : ℕ∞)
          exact_mod_cast (hj : (j.down : ℕ) < m))
        (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        show ({j : Nats.{u} | (if j.down < m then 0 else (j.down - m) + 1) = 0}).ncard = m by
          rw [levelA_fiber_zero]; exact ncard_nats_lt m,
        show ({j : Nats.{u} | (if j.down < k then 0 else (j.down - k) + 1) = 0}).ncard = k by
          rw [levelA_fiber_zero]; exact ncard_nats_lt k]
      exact (zero_add _).symm
    · rw [finsum_fiber_const (a := (0 : H)) (b := x₂) (hfin m (L + 1)) (hfin k (L + 1)) _
        (fun j hj => by
          rw [levelA_fiber_succ] at hj
          rw [familyOfForm_inl]
          refine if_neg ?_
          show ¬ (((j.down : ℕ) : ℕ∞) < ((m : ℕ) : ℕ∞))
          have hja : (j.down : ℕ) = m + L := hj
          rw [hja]
          exact_mod_cast Nat.not_lt.mpr (Nat.le_add_right m L))
        (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        show ({j : Nats.{u} | (if j.down < k then 0 else (j.down - k) + 1) = L + 1}).ncard = 1 by
          rw [levelA_fiber_succ]; exact ncard_nats_eq (k + L),
        smul_zero, zero_add, one_smul]
      exact (zero_add _).symm
  · refine Subtype.ext ?_
    rw [coe_finsum_mem x₁ x₂ (finite_fiber_elim (hfin m' l) (hfin k' l)) _ hGm]
    rcases l with _ | L
    · rw [finsum_fiber_const (a := x₁) (b := x₂) (hfin m' 0) (hfin k' 0) _
        (fun j hj => by
          rw [levelA_fiber_zero] at hj
          rw [familyOfForm_inl]
          refine if_pos ?_
          show ((j.down : ℕ) : ℕ∞) < ((m' : ℕ) : ℕ∞)
          exact_mod_cast (hj : (j.down : ℕ) < m'))
        (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        show ({j : Nats.{u} | (if j.down < m' then 0 else (j.down - m') + 1) = 0}).ncard = m' by
          rw [levelA_fiber_zero]; exact ncard_nats_lt m',
        show ({j : Nats.{u} | (if j.down < k' then 0 else (j.down - k') + 1) = 0}).ncard = k' by
          rw [levelA_fiber_zero]; exact ncard_nats_lt k']
      have hrel' : m • x₁ + k • x₂ = m' • x₁ + k' • x₂ := by
        have h0 := hrel
        rwa [eval, eval, ecmul_natCast, ecmul_natCast, ecmul_natCast, ecmul_natCast] at h0
      exact hrel'.symm.trans (zero_add _).symm
    · rw [finsum_fiber_const (a := (0 : H)) (b := x₂) (hfin m' (L + 1)) (hfin k' (L + 1)) _
        (fun j hj => by
          rw [levelA_fiber_succ] at hj
          rw [familyOfForm_inl]
          refine if_neg ?_
          show ¬ (((j.down : ℕ) : ℕ∞) < ((m' : ℕ) : ℕ∞))
          have hja : (j.down : ℕ) = m' + L := hj
          rw [hja]
          exact_mod_cast Nat.not_lt.mpr (Nat.le_add_right m' L))
        (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        show ({j : Nats.{u} | (if j.down < k' then 0 else (j.down - k') + 1) = L + 1}).ncard = 1 by
          rw [levelA_fiber_succ]; exact ncard_nats_eq (k' + L),
        smul_zero, zero_add, one_smul]
      exact (zero_add _).symm

/-- `ℵ₀` copies of `x` absorb any smaller number of copies. -/
theorem ecmul_add_cmul_top (a : ℕ∞) (x : H) :
    ecmul a x + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x := by
  obtain ⟨w, hw⟩ : ecmul a x ≼ KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x :=
    KMonoid.cmul_le_cmul (Cardinal.ofENat_le_aleph0 a) le_rfl (Cardinal.ofENat_le_aleph0 a) x
  exact KMonoid.add_cmul_top_eq hw

/-- `ℵ₀ x + ℵ₀ x = ℵ₀ x`. -/
theorem cmul_top_add_self (x : H) :
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x
      = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x :=
  KMonoid.add_cmul_top_eq (add_zero _)

/-- **The case `β = β' = ℵ₀` of Theorem 5.3's backward direction.**  If `x₁ ∈ add x₂` this is
Lemma 5.2(3).  Otherwise both `X₁`-coefficients must be finite — an infinite one against a finite
one would make condition (i) produce `x₁ ∈ add x₂` — and condition (ii) supplies the finite
relation that `braidedForms_of_finite_relation` turns into a braiding. -/
theorem braidedForms_of_snd_top (hc1 : Cond1 x₁ x₂) (hc2 : Cond2 x₁ x₂)
    (hmix : NoMixedForms x₁ x₂) (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (α β : ℕ∞) (heq : eval x₁ x₂ (α, ⊤) = eval x₁ x₂ (β, ⊤))
    (hFm : ∀ i, familyOfForm x₁ x₂ (α, ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ i, familyOfForm x₁ x₂ (β, ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ (α, ⊤) (β, ⊤) hFm hGm := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  by_cases hmem : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂
  · exact lemma_5_2_three x₁ x₂ hmem hmix hgen α β hFm hGm
  -- an infinite coefficient against a finite one would force `x₁ ∈ add x₂`
  have hkey : ∀ (d : ℕ), eval x₁ x₂ ((⊤ : ℕ∞), ⊤) = eval x₁ x₂ ((d : ℕ∞), ⊤) → False := by
    intro d hd
    refine hmem (hc1 d ?_).2
    have h0 : ecmul ((d : ℕ) : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂
        = ecmul (⊤ : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂ := hd.symm
    rwa [ecmul_natCast, ecmul_top, ecmul_top, ← KMonoid.cmul_natCast x₁ d] at h0
  rcases eq_or_ne α ⊤ with rfl | hα
  · rcases eq_or_ne β ⊤ with rfl | hβ
    · exact IsBraided.refl _
    · obtain ⟨d, rfl⟩ : ∃ d : ℕ, β = (d : ℕ∞) := ⟨β.toNat, (ENat.natCast_toNat hβ).symm⟩
      exact absurd heq (fun h => hkey d h)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, α = (m : ℕ∞) := ⟨α.toNat, (ENat.natCast_toNat hα).symm⟩
    rcases eq_or_ne β ⊤ with rfl | hβ
    · exact absurd heq.symm (fun h => hkey m h)
    · obtain ⟨m', rfl⟩ : ∃ m' : ℕ, β = (m' : ℕ∞) := ⟨β.toNat, (ENat.natCast_toNat hβ).symm⟩
      obtain ⟨k, k', hrel⟩ := hc2 hmem m m' heq
      exact braidedForms_of_finite_relation x₁ x₂ m k m' k' hrel hFm hGm

/-- **The mixed case of Theorem 5.3's backward direction**: `α X₁ + ℵ₀ X₂` against
`ℵ₀ X₁ + n X₂`.  Adding `ℵ₀ x₁` to both sides puts condition (i) for the pair `(x₂, x₁)` in
force, giving `x₂ ∈ add x₁`; adding `ℵ₀ x₂` instead gives `x₁ ∈ add x₂` when `α` is finite.  Both
forms are then braided with `ℵ₀ X₁ + ℵ₀ X₂` by Lemma 5.2(3), and the paper's "transitivity and
symmetry" finishes. -/
theorem braidedForms_of_mixed (hc1 : Cond1 x₁ x₂) (hc1' : Cond1 x₂ x₁)
    (hmix : NoMixedForms x₁ x₂) (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (α : ℕ∞) (n : ℕ) (heq : eval x₁ x₂ (α, ⊤) = eval x₁ x₂ ((⊤ : ℕ∞), (n : ℕ∞)))
    (hFm : ∀ i, familyOfForm x₁ x₂ (α, ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ i, familyOfForm x₁ x₂ ((⊤ : ℕ∞), (n : ℕ∞)) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ (α, ⊤) ((⊤ : ℕ∞), (n : ℕ∞)) hFm hGm := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  have hgen' : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₂, x₁} : Set H) := by
    rwa [Set.pair_comm]
  have hmix' := noMixedForms_swap x₁ x₂ hmix
  have heval : ecmul α x₁ + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂
      = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ + ecmul ((n : ℕ) : ℕ∞) x₂ := by
    have h0 := heq
    rwa [eval, eval, ecmul_top, ecmul_top] at h0
  -- `x₂ ∈ add x₁`, by adding `ℵ₀ x₁` to both sides
  have hx₂ : x₂ ∈ KMonoid.addOf (κ := ℵ₀) x₁ := by
    refine (hc1' n ?_).2
    have h1 : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ + (ecmul α x₁
          + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂)
        = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ + (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁
          + ecmul ((n : ℕ) : ℕ∞) x₂) := by rw [heval]
    rw [← add_assoc, add_comm (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁) (ecmul α x₁),
      ecmul_add_cmul_top, ← add_assoc, cmul_top_add_self] at h1
    rw [ecmul_natCast] at h1
    rw [KMonoid.cmul_natCast x₂ n, add_comm (n • x₂), ← h1, add_comm]
  -- the second form is braided with `ℵ₀ X₁ + ℵ₀ X₂`
  have hG : BraidedForms x₁ x₂ ((⊤ : ℕ∞), (n : ℕ∞)) ((⊤ : ℕ∞), (⊤ : ℕ∞))
      hGm (familyOfForm_mem x₁ x₂ _) :=
    braidedForms_swap x₁ x₂ (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _)
      (lemma_5_2_three x₂ x₁ hx₂ hmix' hgen' ((n : ℕ) : ℕ∞) (⊤ : ℕ∞)
        (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _)) hGm (familyOfForm_mem x₁ x₂ _)
  -- and so is the first
  have hF : BraidedForms x₁ x₂ (α, ⊤) ((⊤ : ℕ∞), (⊤ : ℕ∞)) hFm (familyOfForm_mem x₁ x₂ _) := by
    rcases eq_or_ne α ⊤ with rfl | hα
    · exact IsBraided.refl _
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, α = (m : ℕ∞) := ⟨α.toNat, (ENat.natCast_toNat hα).symm⟩
    refine lemma_5_2_three x₁ x₂ ?_ hmix hgen _ _ _ _
    refine (hc1 m ?_).2
    have h1 : (ecmul ((m : ℕ) : ℕ∞) x₁ + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂)
        = (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ + ecmul ((n : ℕ) : ℕ∞) x₂)
          + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ := by
      rw [← heval, add_assoc, cmul_top_add_self]
    rw [add_assoc, ecmul_add_cmul_top, ecmul_natCast, ← KMonoid.cmul_natCast x₁ m] at h1
    exact h1
  exact IsBraided.trans_aleph0 hF (IsBraided.symm hG)

/-- **Theorem 5.3's backward direction, at the level of forms**: under conditions (i)–(iii), two
forms representing the same element are braided.  This is the paper's four-case split. -/
theorem braidedForms_of_conditions (hc1 : Cond1 x₁ x₂) (hc1' : Cond1 x₂ x₁)
    (hc2 : Cond2 x₁ x₂) (hc2' : Cond2 x₂ x₁) (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (F G : Form) (heq : eval x₁ x₂ F = eval x₁ x₂ G)
    (hFm : ∀ i, familyOfForm x₁ x₂ F i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ i, familyOfForm x₁ x₂ G i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ F G hFm hGm := by
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  have hgen' : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₂, x₁} : Set H) := by
    rwa [Set.pair_comm]
  have hmix' := noMixedForms_swap x₁ x₂ hmix
  -- by condition (iii) the two forms are finite or infinite together
  by_cases hFfin : F.IsFinite
  · have hGfin : G.IsFinite := by
      by_contra hG
      have hGinf : G.IsInfinite := by
        by_contra h
        exact hG ((Form.not_isInfinite_iff G).mp h)
      exact hmix (eval x₁ x₂ F) ⟨⟨F, hFfin, rfl⟩, ⟨G, hGinf, heq.symm⟩⟩
    exact lemma_5_2_two x₁ x₂ F G hFfin hGfin heq hFm hGm
  have hFinf : F.IsInfinite := by
    by_contra h
    exact hFfin ((Form.not_isInfinite_iff F).mp h)
  have hGinf : G.IsInfinite := by
    by_contra h
    have hGfin : G.IsFinite := (Form.not_isInfinite_iff G).mp h
    exact hmix (eval x₁ x₂ G) ⟨⟨G, hGfin, rfl⟩, ⟨F, hFinf, heq⟩⟩
  obtain ⟨a, b⟩ := F
  obtain ⟨c, d⟩ := G
  rcases eq_or_ne b ⊤ with rfl | hb
  · rcases eq_or_ne d ⊤ with rfl | hd
    · exact braidedForms_of_snd_top x₁ x₂ hc1 hc2 hmix hgen a c heq hFm hGm
    · -- `d` finite, so `c = ⊤`
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = (n : ℕ∞) := ⟨d.toNat, (ENat.natCast_toNat hd).symm⟩
      have hc : c = ⊤ := by rcases hGinf with h | h; exacts [h, absurd h (by simp)]
      subst hc
      exact braidedForms_of_mixed x₁ x₂ hc1 hc1' hmix hgen a n heq hFm hGm
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = (n : ℕ∞) := ⟨b.toNat, (ENat.natCast_toNat hb).symm⟩
    have ha : a = ⊤ := by rcases hFinf with h | h; exacts [h, absurd h (by simp)]
    subst ha
    rcases eq_or_ne d ⊤ with rfl | hd
    · exact IsBraided.symm (braidedForms_of_mixed x₁ x₂ hc1 hc1' hmix hgen c n heq.symm hGm hFm)
    · -- both `X₂`-coefficients finite, so both `X₁`-coefficients are `⊤`: the swapped case
      obtain ⟨n', rfl⟩ : ∃ n' : ℕ, d = (n' : ℕ∞) := ⟨d.toNat, (ENat.natCast_toNat hd).symm⟩
      have hc : c = ⊤ := by rcases hGinf with h | h; exacts [h, absurd h (by simp)]
      subst hc
      refine braidedForms_swap x₁ x₂ (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _)
        (braidedForms_of_snd_top x₂ x₁ hc1' hc2' hmix' hgen' ((n : ℕ) : ℕ∞) ((n' : ℕ) : ℕ∞)
          ?_ (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _)) hFm hGm
      rw [eval_swap x₂ x₁, eval_swap x₂ x₁]
      exact heq

/-! ### Cutting the slots of a form into the blocks of a sequence of partial sums

The backward direction of Theorem 5.3 must braid an *arbitrary* family over `add (x₁ + x₂)` with a
family of generators — the step the paper compresses into "hence `add (x₁ + x₂) = ⟨x₁, x₂⟩`".  Each
member of the family is a finite form `c k · x₁ + d k · x₂`, and the slots of the total form have to
be cut into consecutive blocks of `c k` copies of `x₁` and `d k` copies of `x₂`.  `blockIdx` is that
cut: for the partial sums `s` of `c`, it sends `j` to the `k` with `s k ≤ j < s (k+1)`. -/

section Blocks

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
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ico, blockIdx]
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

theorem blockIdx_fibre_finite {s : ℕ → ℕ} (hs : Monotone s) (hs0 : s 0 = 0) (k : ℕ) :
    {j : ℕ | blockIdx s j = k}.Finite := by
  rw [blockIdx_fibre hs hs0]
  exact (Set.finite_Ico _ _).union ((Set.finite_singleton k).subset fun j hj => hj.2)

/-- A `finsum` over the fibre of a level function on `FormIdx` splits into its two halves. -/
theorem finsum_fiber_elim_split {M : Type v} [AddCommMonoid M] {f g : Nats.{u} → ℕ} {k : ℕ}
    (hf : {j : Nats.{u} | f j = k}.Finite) (hg : {j : Nats.{u} | g j = k}.Finite)
    (F : FormIdx.{u} → M) :
    ∑ᶠ i ∈ {i : FormIdx.{u} | Sum.elim f g i = k}, F i
      = (∑ᶠ j ∈ {j : Nats.{u} | f j = k}, F (Sum.inl j))
        + (∑ᶠ j ∈ {j : Nats.{u} | g j = k}, F (Sum.inr j)) := by
  classical
  have hdisj : Disjoint (Sum.inl '' {j : Nats.{u} | f j = k})
      (Sum.inr '' {j : Nats.{u} | g j = k}) := by
    refine Set.disjoint_left.mpr ?_
    rintro i ⟨j, -, rfl⟩ ⟨j', -, hj'⟩
    exact Sum.inl_ne_inr hj'.symm
  rw [fiber_elim, finsum_mem_union hdisj (hf.image _) (hg.image _),
    finsum_mem_image Sum.inl_injective.injOn, finsum_mem_image Sum.inr_injective.injOn]

/-- **The block sum of a form's slots.**  On the fibre of `blockIdx` at `k` the family of a form
with `A` copies of `v` takes the value `v` exactly on `[s k, s (k+1))` — the leftover slot carries
`0`, since it lies beyond every `s l` — so the block sums to `s (k+1) - s k` copies of `v`. -/
theorem finsum_blockIdx_fibre {s : ℕ → ℕ} (hs : Monotone s) (hs0 : s 0 = 0) {A : ℕ∞}
    (hA : ∀ j : ℕ, ((j : ℕ) : ℕ∞) < A ↔ ∃ l, j < s l) (v : H) (k : ℕ) :
    (∑ᶠ j ∈ {j : Nats.{u} | blockIdx s j.down = k},
        (if ((j.down : ℕ) : ℕ∞) < A then v else 0)) = (s (k + 1) - s k) • v := by
  classical
  have hset : {j : Nats.{u} | blockIdx s j.down = k}
      = {j : Nats.{u} | j.down ∈ Set.Ico (s k) (s (k + 1))}
        ∪ {j : Nats.{u} | j.down ∈ {j | (¬ ∃ l, j < s l) ∧ j = k}} := by
    ext j
    show blockIdx s j.down = k ↔ _
    rw [show (blockIdx s j.down = k) ↔ j.down ∈ {j : ℕ | blockIdx s j = k} from Iff.rfl,
      blockIdx_fibre hs hs0]
    exact Iff.rfl
  have hfin₁ : {j : Nats.{u} | j.down ∈ Set.Ico (s k) (s (k + 1))}.Finite :=
    finite_nats_setOf (Set.finite_Ico _ _)
  have hfin₂ : {j : Nats.{u} | j.down ∈ {j | (¬ ∃ l, j < s l) ∧ j = k}}.Finite :=
    finite_nats_setOf ((Set.finite_singleton k).subset fun j hj => hj.2)
  have hdisj : Disjoint {j : Nats.{u} | j.down ∈ Set.Ico (s k) (s (k + 1))}
      {j : Nats.{u} | j.down ∈ {j | (¬ ∃ l, j < s l) ∧ j = k}} := by
    refine Set.disjoint_left.mpr fun j hj hj' => ?_
    exact hj'.1 ⟨k + 1, hj.2⟩
  rw [hset, finsum_mem_union hdisj hfin₁ hfin₂,
    finsum_mem_congr rfl (fun j hj => if_pos ((hA j.down).mpr ⟨k + 1, hj.2⟩) :
      ∀ j ∈ {j : Nats.{u} | j.down ∈ Set.Ico (s k) (s (k + 1))},
        (if ((j.down : ℕ) : ℕ∞) < A then v else 0) = v),
    finsum_mem_congr rfl (fun j hj => if_neg (fun hlt => hj.1 ((hA j.down).mp hlt)) :
      ∀ j ∈ {j : Nats.{u} | j.down ∈ {j | (¬ ∃ l, j < s l) ∧ j = k}},
        (if ((j.down : ℕ) : ℕ∞) < A then v else 0) = 0),
    finsum_mem_const_finite hfin₁, finsum_mem_zero, add_zero, ncard_nats_setOf,
    Set.ncard_Ico_nat]

end Blocks

/-- A fixed identification of the index type of an `ℵ₀`-sum with `ℕ`. -/
noncomputable def idxEquivNats : Idx (ℵ₀ : Cardinal.{u}) ≃ Nats.{u} :=
  (Cardinal.eq.mp ((mk_Idx (ℵ₀ : Cardinal.{u})).trans mk_nats.{u}.symm)).some

/-- **Every element of `add (x₁ + x₂)` has a finite form**, given condition (iii).

It is a summand of some `n (x₁ + x₂)`, which has the finite form `(n, n)`; a form of the sum is the
sum of forms of the parts, so an infinite form of the summand would give `n (x₁ + x₂)` an infinite
form alongside its finite one.  This is the paper's "elements of `add (x₁ + x₂)` can only have
finite forms". -/
theorem exists_finite_form_of_mem (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    {y : H} (hy : y ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    ∃ F : Form, F.IsFinite ∧ eval x₁ x₂ F = y := by
  obtain ⟨z, n, hzn⟩ := hy
  obtain ⟨F, hF⟩ := exists_form x₁ x₂ hgen y
  obtain ⟨G, hG⟩ := exists_form x₁ x₂ hgen z
  refine ⟨F, ?_, hF⟩
  by_contra hFfin
  have hFinf : F.IsInfinite := by
    by_contra h
    exact hFfin ((Form.not_isInfinite_iff F).mp h)
  -- the sum of the two forms evaluates to `n (x₁ + x₂)`, which also has the finite form `(n, n)`
  have hsum : eval x₁ x₂ (F.1 + G.1, F.2 + G.2) = n • x₁ + n • x₂ := by
    have h0 : y + z = n • x₁ + n • x₂ := by
      rw [hzn, KMonoid.cmul_natCast, smul_add]
    rw [eval, ecmul_add, ecmul_add, ← h0, ← hF, ← hG, eval, eval]
    abel
  have hfinite : HasFiniteForm x₁ x₂ (n • x₁ + n • x₂) := by
    refine ⟨(((n : ℕ) : ℕ∞), ((n : ℕ) : ℕ∞)), ⟨ENat.coe_ne_top n, ENat.coe_ne_top n⟩, ?_⟩
    rw [eval, ecmul_natCast, ecmul_natCast]
  have hinfinite : HasInfiniteForm x₁ x₂ (n • x₁ + n • x₂) := by
    refine ⟨(F.1 + G.1, F.2 + G.2), ?_, hsum⟩
    rcases hFinf with h | h
    · exact Or.inl (by rw [show (F.1 + G.1 : ℕ∞) = ⊤ + G.1 from by rw [h]]; exact top_add G.1)
    · exact Or.inr (by rw [show (F.2 + G.2 : ℕ∞) = ⊤ + G.2 from by rw [h]]; exact top_add G.2)
  exact hmix _ ⟨hfinite, hinfinite⟩

/-- **The refinement step of Theorem 5.3's backward direction.**

Every family over `add (x₁ + x₂)` is braided with the family of a single form: each member is a
finite form `c k · x₁ + d k · x₂`, and the slots of the total form `(A, B)` — where `A`, `B` are the
suprema of the partial sums — are cut into consecutive blocks of `c k` copies of `x₁` and `d k`
copies of `x₂` by `blockIdx`.  The family itself is cut into singletons, so the two block sums agree
and `IsBraided.of_levels` applies with `v ≡ 0`.

This is the step the paper compresses into "hence `add (x₁ + x₂) = ⟨x₁, x₂⟩`". -/
theorem exists_braided_form (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (a : Idx (ℵ₀ : Cardinal.{u}) → ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))) :
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
    ∃ A B : ℕ∞, IsBraided ℵ₀ a
      (fun i => (⟨familyOfForm x₁ x₂ (A, B) (formIdxEquiv.{u}.symm i),
        familyOfForm_mem x₁ x₂ _ _⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) := by
  classical
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  -- a finite form for each member
  choose F hFfin hFeq using fun μ => exists_finite_form_of_mem x₁ x₂ hmix hgen (a μ).2
  set μof : ℕ → Idx (ℵ₀ : Cardinal.{u}) := fun k => idxEquivNats.{u}.symm (ULift.up k) with hμof
  set c : ℕ → ℕ := fun k => (F (μof k)).1.toNat with hc
  set d : ℕ → ℕ := fun k => (F (μof k)).2.toNat with hd
  set s : ℕ → ℕ := fun k => ∑ l ∈ Finset.range k, c l with hs
  set t : ℕ → ℕ := fun k => ∑ l ∈ Finset.range k, d l with ht
  have hsmono : Monotone s := by
    intro p q hpq
    exact Finset.sum_le_sum_of_subset
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hpq))
  have htmono : Monotone t := by
    intro p q hpq
    exact Finset.sum_le_sum_of_subset
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hpq))
  have hs0 : s 0 = 0 := by simp [hs]
  have ht0 : t 0 = 0 := by simp [ht]
  have hsstep : ∀ k, s (k + 1) - s k = c k := by
    intro k; rw [hs]; simp [Finset.sum_range_succ]
  have htstep : ∀ k, t (k + 1) - t k = d k := by
    intro k; rw [ht]; simp [Finset.sum_range_succ]
  set A : ℕ∞ := ⨆ l, ((s l : ℕ) : ℕ∞) with hAdef
  set B : ℕ∞ := ⨆ l, ((t l : ℕ) : ℕ∞) with hBdef
  have hA : ∀ j : ℕ, ((j : ℕ) : ℕ∞) < A ↔ ∃ l, j < s l := by
    intro j
    rw [hAdef, lt_iSup_iff]
    exact ⟨fun ⟨l, hl⟩ => ⟨l, by exact_mod_cast hl⟩, fun ⟨l, hl⟩ => ⟨l, by exact_mod_cast hl⟩⟩
  have hB : ∀ j : ℕ, ((j : ℕ) : ℕ∞) < B ↔ ∃ l, j < t l := by
    intro j
    rw [hBdef, lt_iSup_iff]
    exact ⟨fun ⟨l, hl⟩ => ⟨l, by exact_mod_cast hl⟩, fun ⟨l, hl⟩ => ⟨l, by exact_mod_cast hl⟩⟩
  refine ⟨A, B, ?_⟩
  set ψ : FormIdx.{u} → ℕ :=
    Sum.elim (fun j : Nats.{u} => blockIdx s j.down) (fun j : Nats.{u} => blockIdx t j.down) with hψ
  have hψfin : ∀ k, {p : FormIdx.{u} | ψ p = k}.Finite := fun k =>
    finite_fiber_elim (finite_nats_setOf (blockIdx_fibre_finite hsmono hs0 k))
      (finite_nats_setOf (blockIdx_fibre_finite htmono ht0 k))
  have hIfib : ∀ k : ℕ, {i : Idx (ℵ₀ : Cardinal.{u}) | (idxEquivNats.{u} i).down = k}
      = {μof k} := by
    intro k
    ext i
    show (idxEquivNats.{u} i).down = k ↔ i = μof k
    constructor
    · intro h
      show i = idxEquivNats.{u}.symm (ULift.up k)
      rw [← h]
      exact (idxEquivNats.{u}.symm_apply_apply i).symm
    · rintro rfl
      show (idxEquivNats.{u} (idxEquivNats.{u}.symm (ULift.up k))).down = k
      rw [Equiv.apply_symm_apply]
  have hJfib : ∀ k : ℕ,
      {i : Idx (ℵ₀ : Cardinal.{u}) | ψ (formIdxEquiv.{u}.symm i) = k}
        = formIdxEquiv.{u} '' {p : FormIdx.{u} | ψ p = k} := by
    intro k
    ext i
    constructor
    · intro h
      exact ⟨formIdxEquiv.{u}.symm i, h, formIdxEquiv.{u}.apply_symm_apply i⟩
    · rintro ⟨p, hp, rfl⟩
      show ψ (formIdxEquiv.{u}.symm (formIdxEquiv.{u} p)) = k
      rwa [formIdxEquiv.{u}.symm_apply_apply]
  refine IsBraided.of_levels (idxEquivNats.{u}.symm (ULift.up 0))
    (fun i => (idxEquivNats.{u} i).down) (fun i => ψ (formIdxEquiv.{u}.symm i))
    (fun k => by rw [hIfib k]; exact Set.finite_singleton _)
    (fun k => by rw [hJfib k]; exact (hψfin k).image _)
    (fun k => a (μof k)) (fun _ => 0) rfl (fun k => ?_) (fun k => ?_)
  · rw [hIfib k, finsum_mem_singleton]
    exact (zero_add _).symm
  · have hcongr : ∀ p ∈ {p : FormIdx.{u} | ψ p = k},
        (⟨familyOfForm x₁ x₂ (A, B) (formIdxEquiv.{u}.symm (formIdxEquiv.{u} p)),
            familyOfForm_mem x₁ x₂ _ _⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))
          = ⟨familyOfForm x₁ x₂ (A, B) p, familyOfForm_mem x₁ x₂ _ _⟩ :=
      fun p _ => Subtype.ext (by rw [Equiv.symm_apply_apply])
    rw [hJfib k, finsum_mem_image (Set.injOn_of_injective formIdxEquiv.{u}.injective),
      finsum_mem_congr rfl hcongr]
    refine Subtype.ext ?_
    have h1 : (∑ᶠ j ∈ {j : Nats.{u} | blockIdx s j.down = k},
        familyOfForm x₁ x₂ (A, B) (Sum.inl j)) = c k • x₁ := by
      rw [← hsstep k]
      exact finsum_blockIdx_fibre hsmono hs0 hA x₁ k
    have h2 : (∑ᶠ j ∈ {j : Nats.{u} | blockIdx t j.down = k},
        familyOfForm x₁ x₂ (A, B) (Sum.inr j)) = d k • x₂ := by
      rw [← htstep k]
      exact finsum_blockIdx_fibre htmono ht0 hB x₂ k
    rw [coe_finsum_mem x₁ x₂ (hψfin k) _ (familyOfForm_mem x₁ x₂ _), hψ,
      finsum_fiber_elim_split (finite_nats_setOf (blockIdx_fibre_finite hsmono hs0 k))
        (finite_nats_setOf (blockIdx_fibre_finite htmono ht0 k)), h1, h2]
    show c k • x₁ + d k • x₂ = (0 : H) + (a (μof k) : H)
    rw [zero_add, ← hFeq (μof k), eval,
      show (F (μof k)).1 = ((c k : ℕ) : ℕ∞) from (ENat.natCast_toNat (hFfin (μof k)).1).symm,
      show (F (μof k)).2 = ((d k : ℕ) : ℕ∞) from (ENat.natCast_toNat (hFfin (μof k)).2).symm,
      ecmul_natCast, ecmul_natCast]

/-- **Theorem 5.3, backward direction**: under the three conditions `H` is braided over
`add (x₁ + x₂)`, and Corollary 4.7(1) then realises it.

`exists_braided_form` replaces an arbitrary pair of families over `add (x₁ + x₂)` by a pair of
form families; Lemma 3.2 turns the hypothesis on their sums into an equality of the two forms'
values; and `braidedForms_of_conditions` braids those.  Transitivity finishes. -/
theorem theorem_5_3_backward (k : Type u) [Field k]
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hc1 : Cond1 x₁ x₂) (hc1' : Cond1 x₂ x₁) (hc2 : Cond2 x₁ x₂) (hc2' : Cond2 x₂ x₁)
    (hmix : NoMixedForms x₁ x₂) :
    ∃ (R : Type u) (_ : Ring R) (_ : Algebra k R) (_ : ∀ I : Ideal R, Module.Projective R I),
      EveryProjectiveIsSumOfFG R ∧
      letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
        KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e := by
  classical
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  letI := KMonoid.toLMonoidOfLE H Cardinal.isRegular_aleph0 (le_refl (ℵ₀ : Cardinal.{u}))
  refine corollary_4_7_one_forward le_rfl k (x₁ + x₂) ?_
  -- `add (x₁ + x₂)` contains both generators, hence generates `H`
  have hx₁T : x₁ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  have hTgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) (KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hgen]
    refine KMonoid.kclosure_le ?_ (KMonoid.isKSubmonoid_kclosure _ _)
    rintro w (rfl | rfl)
    · exact KMonoid.subset_kclosure hx₁T
    · exact KMonoid.subset_kclosure hx₂T
  -- the inclusion is a homomorphism of `ℵ₀⁻`-monoids, so braided families keep their sums
  have hcoehom : IsLMonoidHom (ℵ₀ : Cardinal.{u})
      (fun y : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) => (y : H)) := fun {ι} h x => rfl
  have hksum : ∀ (y : Idx (ℵ₀ : Cardinal.{u}) → ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))
      (C D : ℕ∞), IsBraided ℵ₀ y (fun i => (⟨familyOfForm x₁ x₂ (C, D) (formIdxEquiv.{u}.symm i),
        familyOfForm_mem x₁ x₂ _ _⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)))) →
      KMonoid.ksum (κ := ℵ₀) (fun i => (y i : H)) = eval x₁ x₂ (C, D) := by
    intro y C D hy
    rw [← ksum_familyOfForm x₁ x₂ (C, D), ← KMonoid.sumOf_Idx, ← KMonoid.sumOf_Idx]
    exact sumOf_eq_of_isBraided Cardinal.isRegular_aleph0 (le_refl (ℵ₀ : Cardinal.{u}))
      (le_of_eq (mk_Idx _)) _ _ (hy.map_lmonoidHom hcoehom)
  refine ⟨⟨rfl, fun {ι} h x => rfl⟩, Subtype.val_injective, fun h => ?_, fun a b hab => ?_⟩
  · obtain ⟨z, hzT, rfl⟩ := (KMonoid.mem_kclosure_iff
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)).zero_mem h).mp
      (KMonoid.kGenerates_iff.mp hTgen h)
    exact ⟨fun i => ⟨z i, hzT i⟩, rfl⟩
  · -- refine both families to form families, braid the forms, and compose
    obtain ⟨A, B, hA⟩ := exists_braided_form x₁ x₂ hmix hgen a
    obtain ⟨A', B', hB⟩ := exists_braided_form x₁ x₂ hmix hgen b
    have heval : eval x₁ x₂ (A, B) = eval x₁ x₂ (A', B') := by
      rw [← hksum a A B hA, ← hksum b A' B' hB]
      exact hab
    have hform := (braidedForms_of_conditions x₁ x₂ hc1 hc1' hc2 hc2' hmix hgen (A, B) (A', B')
      heval (familyOfForm_mem x₁ x₂ _) (familyOfForm_mem x₁ x₂ _)).comp_equiv formIdxEquiv.{u}.symm
    exact hA.trans_aleph0 (hform.trans_aleph0 hB.symm)

/-- **Theorem 5.3**: a non-cyclic `ℵ₀`-monoid on two generators is `V^{ℵ₀}(R)` for a hereditary
ring exactly when conditions (i), (ii) and (iii) hold for both orderings of the generators.

The paper's `1 ≤ i ≠ j ≤ 2` is rendered as a conjunction over the two orderings rather than as
`Fin 2` bookkeeping, which would cost more than it saves.

**The statement carries `EveryProjectiveIsSumOfFG R` alongside hereditariness.**  The paper gets
that from Corollary 4.6, which in this development is a *quoted* result (Albrecht; Bergman) with no
counterpart in Mathlib — it is bundled into the Bergman–Dicks data of axiom A5 rather than derived,
so it cannot be recovered from `∀ I : Ideal R, Module.Projective R I` inside the formalisation.
Adding it to both sides of the equivalence keeps the statement faithful: for a hereditary ring the
extra conjunct is automatic.

Forward: Lemma 5.1 gives braidedness, then (iii) is 5.2(1), (ii) is 5.2(4), and (i) is the counting
argument.  Backward: `exists_braided_form` reduces arbitrary families to forms and
`braidedForms_of_conditions` runs the paper's four-case split; Corollary 4.7(1) then realises `H`,
which is where axiom A5 enters. -/
theorem theorem_5_3 (k : Type u) [Field k]
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (∃ (R : Type u) (_ : Ring R) (_ : Algebra k R) (_ : ∀ I : Ideal R, Module.Projective R I),
        EveryProjectiveIsSumOfFG R ∧
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) ↔
      (Cond1 x₁ x₂ ∧ Cond1 x₂ x₁ ∧ Cond2 x₁ x₂ ∧ Cond2 x₂ x₁ ∧ NoMixedForms x₁ x₂) := by
  constructor
  · rintro ⟨R, _, _, -, hfg, e, hhom, hbij⟩
    exact theorem_5_3_forward x₁ x₂ R hfg hgen hnoncyclic e hhom hbij
  · rintro ⟨hc1, hc1', hc2, hc2', hmix⟩
    exact theorem_5_3_backward x₁ x₂ k hgen hc1 hc1' hc2 hc2' hmix

end Theorem53

/-! ## Trace ideals and Proposition 5.4

Mathlib has no trace ideal — `Module.trace` is the trace of an endomorphism, unrelated — so the
definition and the two facts Proposition 5.4 rests on are developed here.  Both are elementary,
which is why they are proved rather than assumed. -/

section Trace

variable (R : Type u) [Ring R] (P : Type u) [AddCommGroup P] [Module R P]

/-- The **trace ideal** `Tr(P) = Σ_{f ∈ Hom(P,R)} im f`. -/
noncomputable def traceIdeal : Ideal R := ⨆ f : P →ₗ[R] R, LinearMap.range f

theorem le_traceIdeal (f : P →ₗ[R] R) : LinearMap.range f ≤ traceIdeal R P :=
  le_iSup (fun f : P →ₗ[R] R => LinearMap.range f) f

/-- **The trace ideal is two-sided**, so `Ideal R` (= left ideals) is not the wrong home for it:
right multiplication by `r` is a left-`R`-linear endomorphism of `R`, so `f (·) * r` is again a
functional on `P`.

This is needed because `I • (⊤ : Submodule R R) ≤ I` is *false* for a one-sided ideal, and that
inclusion is what `traceIdeal_le_of_smul_eq` and `traceIdeal_mul_self` rest on. -/
instance traceIdeal_isTwoSided : (traceIdeal R P).IsTwoSided where
  mul_mem_of_left := by
    intro a r ha
    -- `a` lies in a sum of ranges; push the whole sum through `· * r`
    have hle : traceIdeal R P ≤ Submodule.comap (LinearMap.mulRight R r) (traceIdeal R P) := by
      refine iSup_le fun f => ?_
      rintro x ⟨p, rfl⟩
      exact le_traceIdeal R P ((LinearMap.mulRight R r).comp f) ⟨p, rfl⟩
    exact hle ha

/-- `P = Tr(P) · P` for projective `P`.

Proof: `Module.projective_def` gives `s : P →ₗ[R] P →₀ R` splitting `linearCombination R id`, so
`x = Σ_{p ∈ supp (s x)} (s x) p • p`.  Each coefficient map `x ↦ (s x) p` is the linear functional
`Finsupp.lapply p ∘ₗ s`, hence lands in `Tr(P)`; so `x ∈ Tr(P) • ⊤`. -/
theorem smul_traceIdeal_eq [Module.Projective R P] :
    traceIdeal R P • (⊤ : Submodule R P) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨s, hs⟩ := (Module.projective_def (R := R) (P := P)).mp inferInstance
  have hx : (Finsupp.linearCombination R id) (s x) = x := hs x
  rw [← hx, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  have hcoef : (s x) p ∈ traceIdeal R P :=
    le_traceIdeal R P ((Finsupp.lapply p).comp s) ⟨x, rfl⟩
  exact Submodule.smul_mem_smul hcoef Submodule.mem_top

/-- `Tr(P)` is the least *two-sided* ideal `I` with `P = I · P`.

Proof: if `I • ⊤ = ⊤` then for any `f : P →ₗ[R] R`, `im f = f (I • ⊤) = I * im f ⊆ I`, the last
step by two-sidedness. -/
theorem traceIdeal_le_of_smul_eq {I : Ideal R} [I.IsTwoSided]
    (h : I • (⊤ : Submodule R P) = ⊤) : traceIdeal R P ≤ I := by
  refine iSup_le fun f => ?_
  rw [LinearMap.range_eq_map, ← h, Submodule.map_smul'']
  exact Submodule.smul_le.2 fun a ha x _ => Ideal.IsTwoSided.mul_mem_of_left x ha

/-- `Tr(P)` is idempotent.

Proof: `Tr(P) • ⊤ = ⊤` gives `im f = f (Tr(P) • ⊤) = Tr(P) * im f ⊆ Tr(P) * Tr(P)` for every `f`,
so `Tr(P) ≤ Tr(P) * Tr(P)`; the reverse inclusion is `Ideal.mul_le_left`. -/
theorem traceIdeal_mul_self [Module.Projective R P] :
    traceIdeal R P * traceIdeal R P = traceIdeal R P := by
  refine le_antisymm Ideal.mul_le_left (iSup_le fun f => ?_)
  rw [LinearMap.range_eq_map, ← smul_traceIdeal_eq R P, Submodule.map_smul'']
  refine Submodule.smul_le.2 fun a ha x hx => ?_
  exact Ideal.mul_mem_mul ha (le_traceIdeal R P f ((LinearMap.range_eq_map f) ▸ hx))


/-! ### The trace ideal as an invariant

Proposition 5.4 needs three more facts, all elementary: the trace ideal only depends on the
isomorphism class, `Tr(R) = R`, and the trace ideal of a direct sum is the supremum of the trace
ideals of the summands (only `≤` is used, together with the reverse inclusion for a single
summand). -/

/-- The trace ideal is an isomorphism invariant. -/
theorem traceIdeal_of_iso {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (e : M ≃ₗ[R] N) : traceIdeal R M = traceIdeal R N := by
  refine le_antisymm (iSup_le fun f => ?_) (iSup_le fun f => ?_)
  · rintro y ⟨m, rfl⟩
    exact le_traceIdeal R N (f.comp (e.symm : N →ₗ[R] M)) ⟨e m, by simp⟩
  · rintro y ⟨n, rfl⟩
    exact le_traceIdeal R M (f.comp (e : M →ₗ[R] N)) ⟨e.symm n, by simp⟩

/-- `Tr(R) = R`: the identity is a functional with full image. -/
theorem traceIdeal_self : traceIdeal R R = ⊤ :=
  eq_top_iff.mpr fun x _ => le_traceIdeal R R LinearMap.id ⟨x, rfl⟩

/-- A direct summand has a smaller trace ideal: compose a functional with the projection. -/
theorem traceIdeal_le_of_prod {M N K : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup K] [Module R K] (e : M ≃ₗ[R] N × K) :
    traceIdeal R N ≤ traceIdeal R M := by
  refine iSup_le fun f => ?_
  rintro y ⟨n, rfl⟩
  refine le_traceIdeal R M (f.comp ((LinearMap.fst R N K).comp (e : M →ₗ[R] N × K))) ?_
  exact ⟨e.symm (n, 0), by simp⟩

/-- The trace ideal of a direct sum is contained in the supremum of the trace ideals: a functional
on the sum restricts to each summand, and every element is a finite sum of its components. -/
theorem traceIdeal_dsum_le {ι : Type u} (M : ι → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] :
    traceIdeal R (DirectSum ι M) ≤ ⨆ i, traceIdeal R (M i) := by
  classical
  refine iSup_le fun f => ?_
  rintro y ⟨x, rfl⟩
  have hx : (∑ i ∈ x.support, DirectSum.of (fun i => M i) i (x i)) = x := DFinsupp.sum_single
  rw [← hx, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine Submodule.mem_iSup_of_mem i ?_
  exact le_traceIdeal R (M i) (f.comp (DirectSum.lof R ι M i)) ⟨x i, rfl⟩


/-- **If the trace ideal is everything, finitely many functionals already witness `1`.**  This is
the paper's "let `1_R ∈ im(f₁) + ⋯ + im(f_k)`". -/
theorem exists_sum_eq_one_of_traceIdeal_eq_top (h : traceIdeal R P = ⊤) :
    ∃ (n : ℕ) (f : Fin n → (P →ₗ[R] R)) (x : Fin n → P), ∑ j, f j (x j) = 1 := by
  classical
  let N : Ideal R :=
    { carrier := {r | ∃ (n : ℕ) (f : Fin n → (P →ₗ[R] R)) (x : Fin n → P), ∑ j, f j (x j) = r}
      zero_mem' := ⟨0, Fin.elim0, Fin.elim0, by simp⟩
      add_mem' := by
        rintro a b ⟨n, f, x, rfl⟩ ⟨m, g, y, rfl⟩
        exact ⟨n + m, Fin.append f g, Fin.append x y, by rw [Fin.sum_univ_add]; simp⟩
      smul_mem' := by
        rintro c a ⟨n, f, x, rfl⟩
        refine ⟨n, f, fun j => c • x j, ?_⟩
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => map_smul (f j) c (x j) }
  have hle : traceIdeal R P ≤ N := by
    refine iSup_le fun f => ?_
    rintro y ⟨p, rfl⟩
    exact ⟨1, fun _ => f, fun _ => p, by simp⟩
  exact hle (by rw [h]; trivial)

end Trace

section Prop54

variable (R : Type u) [Ring R]

/-- `ℵ₀` copies of a class are represented by the countable direct sum of its representative. -/
theorem rep_cmul_top_dsum (p : (projClass R ℵ₀ le_rfl).carrier) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    Nonempty ((projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)
      ≃ₗ[R] DirectSum (Idx (ℵ₀ : Cardinal.{u})) (fun _ => (projClass R ℵ₀ le_rfl).rep p)) := by
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  rw [show KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p
      = KMonoid.sumOf (κ := ℵ₀) (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u})))
        (fun _ : Idx (ℵ₀ : Cardinal.{u}) => p) from
    (KMonoid.cmul_congr (mk_Idx (ℵ₀ : Cardinal.{u})).symm le_rfl
        (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u}))) p).trans
      (KMonoid.cmul_eq_sumOf (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u}))) p)]
  exact (projClass R ℵ₀ le_rfl).rep_sumOf le_rfl (le_of_eq (mk_Idx _))
    (fun _ : Idx (ℵ₀ : Cardinal.{u}) => p)

/-- **`Tr(P₁) = R` makes `R` a direct summand of a finite power of `P₁`**, hence `[R] ≼ n [P₁]`
in `V^{ℵ₀}(R)`.

The finitely many functionals of `exists_sum_eq_one_of_traceIdeal_eq_top` assemble into an
epimorphism `P₁ⁿ ↠ R`; it splits because `R` is projective, and the resulting idempotent cuts
`P₁ⁿ` into `R` and a complement, both of which are again classes because `V^{ℵ₀}(R)` is closed
under direct summands. -/
theorem addLe_cmul_of_traceIdeal_eq_top (p₁ : (projClass R ℵ₀ le_rfl).carrier)
    (k : Idx (ℵ₀ : Cardinal.{u}))
    (h : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    ∃ n : ℕ, Projective.unitClass R ℵ₀ le_rfl k
      ≼ KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u})
          (le_of_lt Cardinal.natCast_lt_aleph0) p₁ := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  set P := (projClass R ℵ₀ le_rfl).rep p₁ with hP
  obtain ⟨n, f, x, hfx⟩ := exists_sum_eq_one_of_traceIdeal_eq_top R P h
  refine ⟨n, ?_⟩
  -- the epimorphism `P₁ⁿ ↠ R`
  set Φ : DirectSum (ULift.{u} (Fin n)) (fun _ => P) →ₗ[R] R :=
    DirectSum.toModule R _ _ (fun j => f j.down) with hΦ
  have hone : (1 : R) ∈ LinearMap.range Φ := by
    refine ⟨∑ j : ULift.{u} (Fin n), DirectSum.lof R _ (fun _ => P) j (x j.down), ?_⟩
    rw [map_sum, ← hfx]
    exact Fintype.sum_equiv Equiv.ulift _ _
      (fun j => DirectSum.toModule_lof R (M := fun _ => P) j (x j.down))
  have hsurj : Function.Surjective Φ :=
    LinearMap.range_eq_top.mp (Ideal.eq_top_iff_one _ |>.mpr hone)
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property Φ LinearMap.id hsurj
  have hψinv : ∀ r : R, Φ (ψ r) = r := fun r => congrFun (congrArg DFunLike.coe hψ) r
  -- the idempotent `ψ ∘ Φ` splits `P₁ⁿ`
  set π : DirectSum (ULift.{u} (Fin n)) (fun _ => P) →ₗ[R]
      DirectSum (ULift.{u} (Fin n)) (fun _ => P) := ψ.comp Φ with hπ
  have hidem : IsIdempotentElem π := by
    refine LinearMap.ext fun y => ?_
    show ψ (Φ (ψ (Φ y))) = ψ (Φ y)
    rw [hψinv]
  have hcompl : IsCompl (LinearMap.range π) (LinearMap.ker π) := LinearMap.IsIdempotentElem.isCompl hidem
  have hrange : LinearMap.range π = LinearMap.range ψ := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨z, rfl⟩
      exact ⟨Φ z, rfl⟩
    · rintro y ⟨r, rfl⟩
      exact ⟨ψ r, by show ψ (Φ (ψ r)) = ψ r; rw [hψinv]⟩
  have hRiso : R ≃ₗ[R] ↥(LinearMap.range π) :=
    (LinearEquiv.ofInjective ψ (Function.LeftInverse.injective hψinv)).trans
      (LinearEquiv.ofEq _ _ hrange.symm)
  -- `P₁ⁿ` is the representative of `n · p₁`
  have hcard : #(ULift.{u} (Fin n)) = ((n : ℕ) : Cardinal.{u}) := by simp
  have hle : #(ULift.{u} (Fin n)) ≤ (ℵ₀ : Cardinal.{u}) :=
    le_of_eq_of_le hcard (le_of_lt Cardinal.natCast_lt_aleph0)
  have hAeq : KMonoid.cmul (κ := ℵ₀) #(ULift.{u} (Fin n)) hle p₁
      = KMonoid.sumOf (κ := ℵ₀) hle (fun _ : ULift.{u} (Fin n) => p₁) :=
    KMonoid.cmul_eq_sumOf hle p₁
  have e : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) #(ULift.{u} (Fin n)) hle p₁)
      ≃ₗ[R] DirectSum (ULift.{u} (Fin n)) (fun _ => P) := by
    rw [hAeq]
    exact ((projClass R ℵ₀ le_rfl).rep_sumOf le_rfl hle (fun _ : ULift.{u} (Fin n) => p₁)).some
  -- both pieces are classes, and they add up
  obtain ⟨b, hb⟩ := (projClass R ℵ₀ le_rfl).exists_class_of_summand _ e hcompl
  obtain ⟨c, hc⟩ := (projClass R ℵ₀ le_rfl).exists_class_of_summand _ e hcompl.symm
  have hbunit : b = Projective.unitClass R ℵ₀ le_rfl k :=
    (projClass R ℵ₀ le_rfl).eq_of_iso
      (hb.some.trans (hRiso.symm.trans (Projective.rep_unitClass R ℵ₀ le_rfl k).some.symm))
  have hsum := (projClass R ℵ₀ le_rfl).add_eq_of_relCompl le_rfl hcompl.disjoint
    (codisjoint_iff.mp hcompl.codisjoint) hb hc ⟨e.trans Submodule.topEquiv.symm⟩
  refine ⟨c, ?_⟩
  rw [← hbunit, hsum]
  exact KMonoid.cmul_congr hcard hle (le_of_lt Cardinal.natCast_lt_aleph0) p₁


/-- **If both generators have trace ideal inside `I`, then `I = R`.**

The class of `R` is an `ℵ₀`-sum of copies of the two generators, and the trace ideal of a direct
sum is contained in the supremum of the trace ideals of the summands; `Tr(R) = R` finishes.  This
is the paper's "if `J ⊆ I` then `P₂ I = P₂`, and hence `I = R`". -/
theorem eq_top_of_traceIdeal_generators (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier))
    {I : Ideal R}
    (h₁ : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) ≤ I)
    (h₂ : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) ≤ I) : I = ⊤ := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  -- the classes whose trace ideal fits inside `I` form a `κ`-submonoid
  have hsub : KMonoid.IsKSubmonoid (ℵ₀ : Cardinal.{u})
      {a : (projClass R ℵ₀ le_rfl).carrier |
        traceIdeal R ((projClass R ℵ₀ le_rfl).rep a) ≤ I} := by
    constructor
    · show traceIdeal R ((projClass R ℵ₀ le_rfl).rep 0) ≤ I
      haveI := (projClass R ℵ₀ le_rfl).subsingleton_rep_of_eq_zero
        ((projClass R ℵ₀ le_rfl).instKMonoid_zero le_rfl)
      refine iSup_le fun f => ?_
      rintro y ⟨m, rfl⟩
      rw [Subsingleton.elim m 0, map_zero]
      exact Submodule.zero_mem I
    · intro z hz
      show traceIdeal R ((projClass R ℵ₀ le_rfl).rep
        (KMonoid.sumOf (κ := ℵ₀) (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u}))) z)) ≤ I
      rw [traceIdeal_of_iso R
        ((projClass R ℵ₀ le_rfl).rep_sumOf le_rfl (le_of_eq (mk_Idx _)) z).some]
      exact le_trans (traceIdeal_dsum_le R _) (iSup_le fun i => hz i)
  have hmem : traceIdeal R ((projClass R ℵ₀ le_rfl).rep (Projective.unitClass R ℵ₀ le_rfl k))
      ≤ I := by
    refine KMonoid.kclosure_le ?_ hsub (KMonoid.kGenerates_iff.mp hgen _)
    rintro w (rfl | rfl)
    · exact h₁
    · exact h₂
  refine top_le_iff.mp ?_
  rw [← traceIdeal_self R, ← traceIdeal_of_iso R (Projective.rep_unitClass R ℵ₀ le_rfl k).some]
  exact hmem

/-- **`Tr(P) = R` makes `ℵ₀ [R]` a summand of `ℵ₀ [P]`.**  Scale `[R] ≼ n [P]` by `ℵ₀`, using
`ℵ₀ · (n+1) = ℵ₀`. -/
theorem cmul_top_unitClass_addLe (p : (projClass R ℵ₀ le_rfl).carrier)
    (k : Idx (ℵ₀ : Cardinal.{u})) (h : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p) = ⊤) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (Projective.unitClass R ℵ₀ le_rfl k)
      ≼ KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p := by
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  obtain ⟨n, c, hc⟩ := addLe_cmul_of_traceIdeal_eq_top R p k h
  obtain ⟨t, ht⟩ : Projective.unitClass R ℵ₀ le_rfl k
      ≼ KMonoid.cmul (κ := ℵ₀) (((n + 1 : ℕ)) : Cardinal.{u})
          (le_of_lt Cardinal.natCast_lt_aleph0) p :=
    AddLe.trans ⟨c, hc⟩ (KMonoid.cmul_le_cmul _ _ (by exact_mod_cast Nat.le_succ n) p)
  have hmul : (ℵ₀ : Cardinal.{u}) * (((n + 1 : ℕ)) : Cardinal.{u}) = ℵ₀ :=
    Cardinal.mul_eq_left le_rfl (le_of_lt Cardinal.natCast_lt_aleph0)
      (by exact_mod_cast Nat.succ_ne_zero n)
  refine ⟨KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl t, ?_⟩
  rw [← KMonoid.cmul_top_distrib, ht, KMonoid.cmul_cmul le_rfl
    (le_of_lt Cardinal.natCast_lt_aleph0) (le_of_eq hmul)]
  exact KMonoid.cmul_congr hmul (le_of_eq hmul) le_rfl p

/-- **Proposition 5.4**: for a ring with non-cyclic `V^{ℵ₀}(R)` generated by `[P₁]` and `[P₂]`,
`Tr(P₂) ⊆ Tr(P₁)`, `Tr(P₁) = R` and `P₂ | P₁^{(ℵ₀)}` are equivalent.

The two classes are given as carrier elements `p₁ p₂` and their modules as `rep p₁`, `rep p₂` —
`ModuleClass` has no constructor taking a module to its class, only `rep` going the other way.

(i) ⇒ (ii) is `eq_top_of_traceIdeal_generators`, which replaces the paper's `P₂ Tr(P₁) = P₂` by
the trace ideal of a direct sum.  (ii) ⇒ (iii) is the paper's "`1 ∈ im f₁ + ⋯ + im f_k`", giving
`[R] ≼ n [P₁]` (`addLe_cmul_of_traceIdeal_eq_top`); scaling by `ℵ₀` and using that `[R]` is an
order-unit puts `[P₂]` below `ℵ₀ [P₁]`.  (iii) ⇒ (i) is the trace ideal of a summand. -/
theorem prop_5_4 (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier))
    (_hnoncyclic : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      ∀ x : (projClass R ℵ₀ le_rfl).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set (projClass R ℵ₀ le_rfl).carrier)) :
    (traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) ≤ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁)
        ↔ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤) ∧
      (traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤ ↔
        ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
          Nonempty (DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) ≃ₗ[R]
            (projClass R ℵ₀ le_rfl).rep p₂ × Q)) := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  -- the free module on `ℕ` and on `Idx ℵ₀` agree
  have hIdxNat : Idx (ℵ₀ : Cardinal.{u}) ≃ ℕ := idxEquivNats.{u}.trans Equiv.ulift
  have hfirst : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂)
      ≤ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁)
      ↔ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤ := by
    refine ⟨fun h => eq_top_of_traceIdeal_generators R p₁ p₂ hgen le_rfl h, fun h => ?_⟩
    rw [h]
    exact le_top
  refine ⟨hfirst, ⟨fun h => ?_, fun h => ?_⟩⟩
  · -- `Tr(P₁) = R` gives `ℵ₀ [R] ≼ ℵ₀ [P₁]`, hence `[P₂] ≼ ℵ₀ [P₁]`
    obtain ⟨d, hd⟩ := AddLe.trans (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k p₂)
      (cmul_top_unitClass_addLe R p₁ k h)
    -- read the relation as an isomorphism of modules
    refine ⟨(projClass R ℵ₀ le_rfl).rep d, inferInstance, inferInstance, ?_⟩
    have e1 : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p₁)
        ≃ₗ[R] DirectSum (Idx (ℵ₀ : Cardinal.{u}))
          (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) := by
      exact (rep_cmul_top_dsum R p₁).some
    have e2 : DirectSum (Idx (ℵ₀ : Cardinal.{u}))
        (fun _ => (projClass R ℵ₀ le_rfl).rep p₁)
        ≃ₗ[R] DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) :=
      DirectSum.lequivCongrLeft R hIdxNat
    have e3 : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p₁)
        ≃ₗ[R] (projClass R ℵ₀ le_rfl).rep p₂ × (projClass R ℵ₀ le_rfl).rep d := by
      rw [← hd]
      exact ((projClass R ℵ₀ le_rfl).rep_add le_rfl p₂ d).some
    exact ⟨(e2.symm.trans e1.symm).trans e3⟩
  · -- a summand of `P₁^{(ℕ)}` has a smaller trace ideal
    obtain ⟨Q, hQ₁, hQ₂, e⟩ := h
    letI := hQ₁
    letI := hQ₂
    obtain ⟨e'⟩ := e
    have s1 : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂)
        ≤ traceIdeal R (DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁)) :=
      traceIdeal_le_of_prod R
        (M := DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁))
        (N := (projClass R ℵ₀ le_rfl).rep p₂) (K := Q) e'
    have hlift : DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁)
        ≃ₗ[R] DirectSum (ULift.{u} ℕ) (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) :=
      DirectSum.lequivCongrLeft R Equiv.ulift.symm
    have s2 : traceIdeal R (DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁))
        ≤ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) := by
      rw [traceIdeal_of_iso R hlift]
      exact le_trans
        (traceIdeal_dsum_le R (fun _ : ULift.{u} ℕ => (projClass R ℵ₀ le_rfl).rep p₁))
        (iSup_le fun _ => le_rfl)
    exact hfirst.mp (le_trans s1 s2)

/-- **`ℵ₀` copies of a nonzero class are never finitely generated.**

If `rep (ℵ₀ p)` were finitely generated it would be `ℵ₀⁻`-small, so in its decomposition as
`⨁_{Idx ℵ₀} rep p` only finitely many components could ever be nonzero; but every component is
hit, so `rep p` is trivial.  This is what makes `ℵ₀ [P₁]` an admissible input to the "every
countably but not finitely generated projective is free" hypothesis. -/
theorem eq_zero_of_finite_cmul_top {p : (projClass R ℵ₀ le_rfl).carrier}
    (h : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      Module.Finite R ((projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p))) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    p = 0 := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  -- the decomposition of `ℵ₀ p`
  have e : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)
      ≃ₗ[R] DirectSum (Idx (ℵ₀ : Cardinal.{u})) (fun _ => (projClass R ℵ₀ le_rfl).rep p) := by
    exact (rep_cmul_top_dsum R p).some
  obtain ⟨s, hs, hzero⟩ := isLambdaSmall_aleph0_of_fg R _ h
    (fun _ : Idx (ℵ₀ : Cardinal.{u}) => (projClass R ℵ₀ le_rfl).rep p)
    (fun _ => inferInstance) (fun _ => inferInstance) (e : _ →ₗ[R] _)
  -- some index escapes the finite support
  have hsfin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.mp hs
  haveI : Infinite (Idx (ℵ₀ : Cardinal.{u})) :=
    Cardinal.infinite_iff.mpr (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u})).symm)
  obtain ⟨i₀, hi₀⟩ := hsfin.infinite_compl.nonempty
  -- so that component of `rep p` vanishes identically
  refine (projClass R ℵ₀ le_rfl).eq_zero_of_subsingleton ⟨fun y z => ?_⟩
  have hval : ∀ w : (projClass R ℵ₀ le_rfl).rep p, w = 0 := by
    intro w
    have := hzero (e.symm (DirectSum.lof R _
      (fun _ : Idx (ℵ₀ : Cardinal.{u}) => (projClass R ℵ₀ le_rfl).rep p) i₀ w)) i₀ hi₀
    rwa [show (e : _ →ₗ[R] _) (e.symm (DirectSum.lof R _ _ i₀ w))
        = DirectSum.lof R _ (fun _ : Idx (ℵ₀ : Cardinal.{u}) =>
          (projClass R ℵ₀ le_rfl).rep p) i₀ w from e.apply_symm_apply _,
      DirectSum.component.lof_self] at this
  rw [hval y, hval z]

/-- **Proposition 5.4**, final statement: `Tr(P₁) = Tr(P₂)` exactly when every countably but not
finitely generated projective module is free.

**This corrects the scaffold twice.**  The quantifier ranged over *all* projective modules, which
makes the right-hand side false as soon as `R ≠ 0` — `R^{(ℵ₁)}` is projective and not finitely
generated, but is not free on a countable basis (axiom A1).  The paper says "any countably (non
finitely) generated projective module", so the statement is over the classes of `V^{ℵ₀}(R)`, which
are exactly those.  And, as in Theorem 5.3, hereditariness is replaced by
`EveryProjectiveIsSumOfFG R`: the proof needs `P₁` and `P₂` finitely generated, which the paper
gets from Lemma 5.1 through the quoted Corollary 4.6.

Forward: both traces are `R`, so `ℵ₀ [P₁] = ℵ₀ [R] = ℵ₀ [P₂]` by Lemma 2.14.  A class that is not
finitely generated cannot have a finite form — `P₁` and `P₂` are finitely generated by
`mem_of_divisorClosed_of_generates` — so its form has an infinite coefficient, and Lemma 2.14
collapses it to `ℵ₀ [R]`, which is free.  Backward: `ℵ₀ [P₁]` is never finitely generated
(`eq_zero_of_finite_cmul_top`), so it is free, and a free module on a nonempty basis has trace
ideal `R`. -/
theorem prop_5_4_hereditary (hfg : EveryProjectiveIsSumOfFG R)
    (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier))
    (hnoncyclic : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      ∀ x : (projClass R ℵ₀ le_rfl).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set (projClass R ℵ₀ le_rfl).carrier)) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁)
        = traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) ↔
      ∀ q : (projClass R ℵ₀ le_rfl).carrier, ¬ Module.Finite R ((projClass R ℵ₀ le_rfl).rep q) →
        ∃ ι : Type u, #ι ≤ ℵ₀ ∧
          Nonempty ((projClass R ℵ₀ le_rfl).rep q ≃ₗ[R] DirectSum ι (fun _ => R)) := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    ((projClass R ℵ₀ le_rfl).lambdaSmallPart_isLSubset le_rfl ℵ₀ Cardinal.isRegular_aleph0 le_rfl)
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  have hgen' : KMonoid.KGenerates (ℵ₀ : Cardinal.{u})
      ({p₂, p₁} : Set (projClass R ℵ₀ le_rfl).carrier) := by rwa [Set.pair_comm]
  have hWsub := (projClass R ℵ₀ le_rfl).lambdaSmallPart_isLSubset le_rfl ℵ₀
    Cardinal.isRegular_aleph0 le_rfl
  -- both generators are finitely generated, by the paper's parenthetical
  have hWsat : ∀ a ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀,
      ∀ b c : (projClass R ℵ₀ le_rfl).carrier, a = b + c →
      b ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ :=
    fun a ha b c habc =>
      (projClass R ℵ₀ le_rfl).lambdaSmallPart_summand le_rfl ℵ₀ a ha b ⟨c, habc.symm⟩
  obtain ⟨hp₁W, hp₂W⟩ := mem_of_divisorClosed_of_generates p₁ p₂ hWsat
    ((corollary_4_5_three R ℵ₀ le_rfl hfg).1.kGenerates_coe) hgen hnoncyclic
  -- `V(R)` is closed under binary sums and finite multiples
  have hWadd : ∀ a ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀,
      ∀ b ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀,
      a + b ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ := by
    intro a ha b hb
    have hUB : #(ULift.{u} Bool) < (ℵ₀ : Cardinal.{u}) :=
      Cardinal.lt_aleph0_iff_finite.mpr inferInstance
    have hmem : KMonoid.sumOf (κ := ℵ₀) (hUB.le.trans le_rfl)
        (fun t : ULift.{u} Bool => if t.down then a else b)
          ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ :=
      hWsub.sumOf_mem hUB _ (by rintro ⟨(_ | _)⟩ <;> simpa)
    rwa [KMonoid.sumOf_two a b (hUB.le.trans le_rfl)] at hmem
  have hWnsmul : ∀ (m : ℕ) (a : (projClass R ℵ₀ le_rfl).carrier),
      a ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ →
      m • a ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ := by
    intro m a ha
    induction m with
    | zero => rw [zero_nsmul]; exact hWsub.zero_mem
    | succ t ht => rw [succ_nsmul]; exact hWadd _ ht _ ha
  constructor
  · -- `Tr(P₁) = Tr(P₂)` forces both to be `R`, and every infinite form to be `ℵ₀ [R]`
    intro h
    have htop₁ : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤ :=
      (prop_5_4 R p₁ p₂ hgen hnoncyclic).1.mp (le_of_eq h.symm)
    have htop₂ : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) = ⊤ :=
      (prop_5_4 R p₂ p₁ hgen' hnoncyclic).1.mp (le_of_eq h)
    have hcollapse : ∀ p : (projClass R ℵ₀ le_rfl).carrier,
        traceIdeal R ((projClass R ℵ₀ le_rfl).rep p) = ⊤ →
        KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p
          = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (Projective.unitClass R ℵ₀ le_rfl k) := by
      intro p hp
      obtain ⟨w, hw⟩ := cmul_top_unitClass_addLe R p k hp
      exact KMonoid.eq_cmul_top_of_add (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k) w hw.symm
    have hR₁ := hcollapse p₁ htop₁
    have hR₂ := hcollapse p₂ htop₂
    intro q hq
    obtain ⟨F, hF⟩ := exists_form p₁ p₂ hgen q
    -- a finite form would make `q` finitely generated
    have hinf : F.1 = ⊤ ∨ F.2 = ⊤ := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨a, ha⟩ : ∃ a : ℕ, F.1 = (a : ℕ∞) := ⟨F.1.toNat, (ENat.natCast_toNat hcon.1).symm⟩
      obtain ⟨b, hb⟩ : ∃ b : ℕ, F.2 = (b : ℕ∞) := ⟨F.2.toNat, (ENat.natCast_toNat hcon.2).symm⟩
      refine hq (finite_of_isLambdaSmall_aleph0 R ℵ₀ q.out
        ((projClass R ℵ₀ le_rfl).isLambdaSmall_of_mem ?_))
      rw [← hF, eval, ha, hb, ecmul_natCast, ecmul_natCast]
      exact hWadd _ (hWnsmul a p₁ hp₁W) _ (hWnsmul b p₂ hp₂W)
    -- an infinite form collapses to `ℵ₀ [R]`
    have hq' : q = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (Projective.unitClass R ℵ₀ le_rfl k) := by
      rcases hinf with hc | hc
      · refine KMonoid.eq_cmul_top_of_add (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k)
          (ecmul F.2 p₂) ?_
        rw [← hF, eval, hc, ecmul_top, hR₁]
      · refine KMonoid.eq_cmul_top_of_add (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k)
          (ecmul F.1 p₁) ?_
        rw [← hF, eval, hc, ecmul_top, hR₂, add_comm]
    refine ⟨Idx (ℵ₀ : Cardinal.{u}), le_of_eq (mk_Idx _), ?_⟩
    rw [hq']
    exact ⟨(Projective.rep_cmul_unitClass R ℵ₀ le_rfl le_rfl k).some⟩
  · -- freeness of `ℵ₀ [P₁]` and `ℵ₀ [P₂]` makes both trace ideals `R`
    intro h
    obtain ⟨hne₁, hne₂⟩ := ne_zero_of_not_cyclic p₁ p₂ hgen hnoncyclic
    have key : ∀ p : (projClass R ℵ₀ le_rfl).carrier, p ≠ 0 →
        traceIdeal R ((projClass R ℵ₀ le_rfl).rep p) = ⊤ := by
      intro p hp
      obtain ⟨ι, hι, e⟩ := h (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)
        (fun hfin => hp (eq_zero_of_finite_cmul_top R hfin))
      -- the basis is nonempty, since `ℵ₀ p ≠ 0`
      have hιne : Nonempty ι := by
        by_contra hcon
        rw [not_nonempty_iff] at hcon
        refine hp ?_
        have hsub : Subsingleton ((projClass R ℵ₀ le_rfl).rep
            (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)) := Equiv.subsingleton e.some.toEquiv
        have hzero : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p = 0 :=
          ((projClass R ℵ₀ le_rfl).eq_zero_of_subsingleton hsub).trans
            ((projClass R ℵ₀ le_rfl).instKMonoid_zero le_rfl).symm
        obtain ⟨w, hw⟩ : p ≼ KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p := by
          refine ⟨KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p, ?_⟩
          exact KMonoid.add_cmul_top_self (ℵ₀ : Cardinal.{u}) _ p
        rw [hzero] at hw
        exact (KMonoid.isConical (ℵ₀ : Cardinal.{u}) _ p w hw).1
      obtain ⟨i₀⟩ := hιne
      -- a free module on a nonempty basis has trace ideal `R`
      have hfree : traceIdeal R (DirectSum ι (fun _ => R)) = ⊤ := by
        refine eq_top_iff.mpr fun y _ => ?_
        refine le_traceIdeal R _ (DirectSum.component R ι (fun _ => R) i₀) ?_
        exact ⟨DirectSum.lof R ι (fun _ => R) i₀ y, by rw [DirectSum.component.lof_self]⟩
      have hcm : traceIdeal R ((projClass R ℵ₀ le_rfl).rep
          (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)) = ⊤ := by
        rw [traceIdeal_of_iso R e.some]
        exact hfree
      have hdec : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)
          ≃ₗ[R] DirectSum (Idx (ℵ₀ : Cardinal.{u}))
            (fun _ => (projClass R ℵ₀ le_rfl).rep p) := by
          exact (rep_cmul_top_dsum R p).some
      refine top_le_iff.mp ?_
      rw [← hcm, traceIdeal_of_iso R hdec]
      exact le_trans (traceIdeal_dsum_le R (fun _ : Idx (ℵ₀ : Cardinal.{u}) =>
        (projClass R ℵ₀ le_rfl).rep p)) (iSup_le fun _ => le_rfl)
    rw [key p₁ hne₁, key p₂ hne₂]

/-- **`[P₂] ≼ ℵ₀ [P₁]` forces `Tr(P₁) = R`**, by the second half of Proposition 5.4. -/
theorem traceIdeal_eq_top_of_addLe (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier))
    (hnoncyclic : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      ∀ x : (projClass R ℵ₀ le_rfl).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set (projClass R ℵ₀ le_rfl).carrier))
    (h : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      p₂ ≼ KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p₁) :
    traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤ := by
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  obtain ⟨c, hc⟩ := h
  refine (prop_5_4 R p₁ p₂ hgen hnoncyclic).2.mpr
    ⟨(projClass R ℵ₀ le_rfl).rep c, inferInstance, inferInstance, ?_⟩
  have e1 := (rep_cmul_top_dsum R p₁).some
  have e2 : DirectSum (Idx (ℵ₀ : Cardinal.{u})) (fun _ => (projClass R ℵ₀ le_rfl).rep p₁)
      ≃ₗ[R] DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) :=
    DirectSum.lequivCongrLeft R (idxEquivNats.{u}.trans Equiv.ulift)
  have e3 : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p₁)
      ≃ₗ[R] (projClass R ℵ₀ le_rfl).rep p₂ × (projClass R ℵ₀ le_rfl).rep c := by
    rw [← hc]
    exact ((projClass R ℵ₀ le_rfl).rep_add le_rfl p₂ c).some
  exact ⟨(e2.symm.trans e1.symm).trans e3⟩

/-- **If every countably but not finitely generated projective is free, `ℵ₀ [P] = ℵ₀ [R]`** for
every nonzero class `[P]`: `ℵ₀ [P]` is never finitely generated, so it is free on a basis that
cannot be finite, hence on a countably infinite one. -/
theorem cmul_top_eq_unitClass_of_free (k : Idx (ℵ₀ : Cardinal.{u}))
    (p : (projClass R ℵ₀ le_rfl).carrier)
    (hp : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl; p ≠ 0)
    (hfree : ∀ q : (projClass R ℵ₀ le_rfl).carrier, ¬ Module.Finite R ((projClass R ℵ₀ le_rfl).rep q)
      → ∃ ι : Type u, #ι ≤ ℵ₀ ∧
        Nonempty ((projClass R ℵ₀ le_rfl).rep q ≃ₗ[R] DirectSum ι (fun _ => R))) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p
      = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (Projective.unitClass R ℵ₀ le_rfl k) := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  have hnf : ¬ Module.Finite R ((projClass R ℵ₀ le_rfl).rep
      (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)) := fun hfin => hp (eq_zero_of_finite_cmul_top R hfin)
  obtain ⟨ι, hι, e⟩ := hfree _ hnf
  -- the basis cannot be finite
  haveI : Infinite ι := by
    by_contra hcon
    rw [not_infinite_iff_finite] at hcon
    haveI := hcon
    haveI := Fintype.ofFinite ι
    refine hnf (Module.Finite.equiv (e.some.trans (DirectSum.linearEquivFunOnFintype R ι
      (fun _ => R))).symm)
  have hmk : #ι = (ℵ₀ : Cardinal.{u}) :=
    le_antisymm hι (Cardinal.infinite_iff.mp inferInstance)
  obtain ⟨ε⟩ : Nonempty (ι ≃ Idx (ℵ₀ : Cardinal.{u})) :=
    Cardinal.eq.mp (hmk.trans (mk_Idx (ℵ₀ : Cardinal.{u})).symm)
  have efin : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)
      ≃ₗ[R] (projClass R ℵ₀ le_rfl).rep
        (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (Projective.unitClass R ℵ₀ le_rfl k)) :=
    e.some.trans ((DirectSum.lequivCongrLeft R ε).trans
      (Projective.rep_cmul_unitClass R ℵ₀ le_rfl le_rfl k).some.symm)
  exact (projClass R ℵ₀ le_rfl).eq_of_iso efin

end Prop54

/-! ## Corollary 5.5 (`hereditarycase`)

Case analysis on how `add x₁` and `add x₂` compare.  All three parts are bookkeeping on top of
Theorem 5.3, with Proposition 5.4 for part (3)'s trace formulation. -/

section Cor55

variable (x₁ x₂ : H)

/-- **Corollary 5.5(1)**: for incomparable generators, realizability is equivalent to an explicit
condition on the relations of `H`.

**This corrects the scaffold.**  The paper's condition is quantified over `1 ≤ i ≠ j ≤ 2`, so each
of its two clauses has two instances; the scaffold kept only one of each, and both instances of
each are needed.  Without the `X₂`-half of the first clause a finite and an infinite form could
share a value, so condition (iii) of Theorem 5.3 would not follow; and the two halves of the second
clause are exactly condition (ii) of Theorem 5.3 for the two orderings.

(i) ⇒ (ii): adding `ℵ₀ x_j` to a relation with one infinite and one finite `X_i`-coefficient turns
it into the hypothesis of Theorem 5.3(i), whose conclusion `x_i ∈ add x_j` is excluded; the second
clause is Theorem 5.3(ii).  (ii) ⇒ (i): Theorem 5.3(i) holds vacuously — its hypothesis would make
an infinite coefficient equal a finite one — (ii) is the assumption, and (iii) follows from the
first clause. -/
theorem corollary_5_5_one (h₁ : x₁ ∉ KMonoid.addOf (κ := ℵ₀) x₂)
    (h₂ : x₂ ∉ KMonoid.addOf (κ := ℵ₀) x₁)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (∃ (R : Type u) (_ : Ring R), EveryProjectiveIsSumOfFG R ∧
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) ↔
      ((∀ F G : Form, eval x₁ x₂ F = eval x₁ x₂ G → (F.1 = ⊤ ↔ G.1 = ⊤) ∧ (F.2 = ⊤ ↔ G.2 = ⊤)) ∧
        (∀ F G : Form, F.1 = ⊤ → G.1 = ⊤ → eval x₁ x₂ F = eval x₁ x₂ G →
          ∃ m₁ m₂ : ℕ, eval x₁ x₂ ((m₁ : ℕ∞), F.2) = eval x₁ x₂ ((m₂ : ℕ∞), G.2)) ∧
        (∀ F G : Form, F.2 = ⊤ → G.2 = ⊤ → eval x₁ x₂ F = eval x₁ x₂ G →
          ∃ n₁ n₂ : ℕ, eval x₁ x₂ (F.1, (n₁ : ℕ∞)) = eval x₁ x₂ (G.1, (n₂ : ℕ∞)))) := by
  constructor
  · rintro ⟨R, _, hfg, e, hhom, hbij⟩
    obtain ⟨hc1, hc1', hc2, hc2', hmix⟩ :=
      theorem_5_3_forward x₁ x₂ R hfg hgen hnoncyclic e hhom hbij
    -- an infinite `X₁`-coefficient against a finite one would give `x₁ ∈ add x₂`
    have key1 : ∀ F G : Form, eval x₁ x₂ F = eval x₁ x₂ G → F.1 = ⊤ → G.1 ≠ ⊤ → False := by
      intro F G hFG hF hG
      obtain ⟨m, hm⟩ : ∃ m : ℕ, G.1 = (m : ℕ∞) := ⟨G.1.toNat, (ENat.natCast_toNat hG).symm⟩
      refine h₁ (hc1 m ?_).2
      have hadd : eval x₁ x₂ F + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂
          = eval x₁ x₂ G + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ := by rw [hFG]
      rw [eval, eval, hF, hm, add_assoc, add_assoc, ecmul_add_cmul_top, ecmul_add_cmul_top,
        ecmul_top, ecmul_natCast, ← KMonoid.cmul_natCast x₁ m] at hadd
      exact hadd.symm
    -- and symmetrically for the `X₂`-coefficient
    have key2 : ∀ F G : Form, eval x₁ x₂ F = eval x₁ x₂ G → F.2 = ⊤ → G.2 ≠ ⊤ → False := by
      intro F G hFG hF hG
      obtain ⟨n, hn⟩ : ∃ n : ℕ, G.2 = (n : ℕ∞) := ⟨G.2.toNat, (ENat.natCast_toNat hG).symm⟩
      refine h₂ (hc1' n ?_).2
      have hadd : eval x₁ x₂ F + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁
          = eval x₁ x₂ G + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ := by rw [hFG]
      have hL : eval x₁ x₂ F + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁
          = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ := by
        rw [eval, hF]
        calc ecmul F.1 x₁ + ecmul (⊤ : ℕ∞) x₂ + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁
            = (ecmul F.1 x₁ + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁) + ecmul (⊤ : ℕ∞) x₂ := by abel
          _ = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ := by
              rw [ecmul_add_cmul_top, ecmul_top, add_comm]
      have hR : eval x₁ x₂ G + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁
          = KMonoid.cmul (κ := ℵ₀) (n : Cardinal.{u})
              (le_trans (le_of_lt Cardinal.natCast_lt_aleph0) le_rfl) x₂
            + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ := by
        rw [eval, hn]
        calc ecmul G.1 x₁ + ecmul ((n : ℕ) : ℕ∞) x₂ + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁
            = (ecmul G.1 x₁ + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁)
              + ecmul ((n : ℕ) : ℕ∞) x₂ := by abel
          _ = _ := by
              rw [ecmul_add_cmul_top, ecmul_natCast, ← KMonoid.cmul_natCast x₂ n, add_comm]
      rw [hL, hR] at hadd
      exact hadd.symm
    have hcl1 : ∀ F G : Form, eval x₁ x₂ F = eval x₁ x₂ G →
        (F.1 = ⊤ ↔ G.1 = ⊤) ∧ (F.2 = ⊤ ↔ G.2 = ⊤) := by
      intro F G hFG
      exact ⟨⟨fun h => not_not.mp fun hc => key1 F G hFG h hc,
          fun h => not_not.mp fun hc => key1 G F hFG.symm h hc⟩,
        ⟨fun h => not_not.mp fun hc => key2 F G hFG h hc,
          fun h => not_not.mp fun hc => key2 G F hFG.symm h hc⟩⟩
    refine ⟨hcl1, fun F G hF hG hFG => ?_, fun F G hF hG hFG => ?_⟩
    · -- both `X₁`-coefficients infinite: Theorem 5.3(ii) for the ordering `(x₂, x₁)`
      by_cases hF2 : F.2 = ⊤
      · exact ⟨0, 0, by rw [hF2, ((hcl1 F G hFG).2).mp hF2]⟩
      obtain ⟨a, ha⟩ : ∃ a : ℕ, F.2 = (a : ℕ∞) := ⟨F.2.toNat, (ENat.natCast_toNat hF2).symm⟩
      have hG2 : G.2 ≠ ⊤ := fun h => hF2 (((hcl1 F G hFG).2).mpr h)
      obtain ⟨b, hb⟩ : ∃ b : ℕ, G.2 = (b : ℕ∞) := ⟨G.2.toNat, (ENat.natCast_toNat hG2).symm⟩
      have e1 : F = ((⊤ : ℕ∞), ((a : ℕ) : ℕ∞)) := by rw [← hF, ← ha]
      have e2 : G = ((⊤ : ℕ∞), ((b : ℕ) : ℕ∞)) := by rw [← hG, ← hb]
      obtain ⟨k, k', hkk'⟩ := hc2' h₂ a b (by
        rw [eval_swap x₂ x₁, eval_swap x₂ x₁]
        show eval x₁ x₂ ((⊤ : ℕ∞), ((a : ℕ) : ℕ∞)) = eval x₁ x₂ ((⊤ : ℕ∞), ((b : ℕ) : ℕ∞))
        rw [← e1, ← e2]
        exact hFG)
      refine ⟨k, k', ?_⟩
      rw [ha, hb]
      rw [eval_swap x₂ x₁, eval_swap x₂ x₁] at hkk'
      exact hkk'
    · -- both `X₂`-coefficients infinite: Theorem 5.3(ii) for the ordering `(x₁, x₂)`
      by_cases hF1 : F.1 = ⊤
      · exact ⟨0, 0, by rw [hF1, ((hcl1 F G hFG).1).mp hF1]⟩
      obtain ⟨a, ha⟩ : ∃ a : ℕ, F.1 = (a : ℕ∞) := ⟨F.1.toNat, (ENat.natCast_toNat hF1).symm⟩
      have hG1 : G.1 ≠ ⊤ := fun h => hF1 (((hcl1 F G hFG).1).mpr h)
      obtain ⟨b, hb⟩ : ∃ b : ℕ, G.1 = (b : ℕ∞) := ⟨G.1.toNat, (ENat.natCast_toNat hG1).symm⟩
      have e1 : F = (((a : ℕ) : ℕ∞), (⊤ : ℕ∞)) := by rw [← hF, ← ha]
      have e2 : G = (((b : ℕ) : ℕ∞), (⊤ : ℕ∞)) := by rw [← hG, ← hb]
      obtain ⟨k, k', hkk'⟩ := hc2 h₁ a b (by rw [← e1, ← e2]; exact hFG)
      exact ⟨k, k', by rw [ha, hb]; exact hkk'⟩
  · rintro ⟨hcl1, hcl2, hcl3⟩
    -- the three conditions of Theorem 5.3
    have hc1 : Cond1 x₁ x₂ := by
      intro n hn
      refine absurd ((hcl1 (((n : ℕ) : ℕ∞), ⊤) ((⊤ : ℕ∞), ⊤) ?_).1.mpr rfl) (ENat.coe_ne_top n)
      show ecmul ((n : ℕ) : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂
        = ecmul (⊤ : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂
      rw [ecmul_natCast, ecmul_top, ecmul_top, ← KMonoid.cmul_natCast x₁ n]
      exact hn
    have hc1' : Cond1 x₂ x₁ := by
      intro n hn
      refine absurd ((hcl1 ((⊤ : ℕ∞), ((n : ℕ) : ℕ∞)) ((⊤ : ℕ∞), ⊤) ?_).2.mpr rfl)
        (ENat.coe_ne_top n)
      show ecmul (⊤ : ℕ∞) x₁ + ecmul ((n : ℕ) : ℕ∞) x₂
        = ecmul (⊤ : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂
      rw [ecmul_natCast, ecmul_top, ecmul_top, ← KMonoid.cmul_natCast x₂ n,
        add_comm (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁)
          (KMonoid.cmul (κ := ℵ₀) (n : Cardinal.{u})
            (le_trans (le_of_lt Cardinal.natCast_lt_aleph0) le_rfl) x₂),
        add_comm (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁) (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂)]
      exact hn
    have hmix : NoMixedForms x₁ x₂ := by
      rintro y ⟨⟨F, hF, hFe⟩, ⟨G, hG, hGe⟩⟩
      rcases hG with h | h
      · exact hF.1 (((hcl1 F G (hFe.trans hGe.symm)).1).mpr h)
      · exact hF.2 (((hcl1 F G (hFe.trans hGe.symm)).2).mpr h)
    obtain ⟨R, hring, -, -, hfg, e, hhom, hbij⟩ :=
      theorem_5_3_backward x₁ x₂ (ULift.{u} ℚ) hgen hc1 hc1'
        (fun _ m n hmn => hcl3 (((m : ℕ) : ℕ∞), ⊤) (((n : ℕ) : ℕ∞), ⊤) rfl rfl hmn)
        (fun _ m n hmn => by
          obtain ⟨k, k', hkk'⟩ := hcl2 ((⊤ : ℕ∞), ((m : ℕ) : ℕ∞)) ((⊤ : ℕ∞), ((n : ℕ) : ℕ∞))
            rfl rfl (by rw [eval_swap x₂ x₁, eval_swap x₂ x₁] at hmn; exact hmn)
          exact ⟨k, k', by rw [eval_swap x₂ x₁, eval_swap x₂ x₁]; exact hkk'⟩)
        hmix
    exact ⟨R, hring, hfg, e, hhom, hbij⟩

/-- **Corollary 5.5(2)**, first claim: if `add x₁ = add x₂` then `H` has exactly one element with
an infinite form, namely `ℵ₀ x₁ = ℵ₀ x₂`.

Each generator absorbs the other by `cmul_top_absorb`, which both identifies `ℵ₀ x₁` with `ℵ₀ x₂`
and collapses every infinite form to it. -/
theorem corollary_5_5_two_unique (h : KMonoid.addOf (κ := ℵ₀) x₁ = KMonoid.addOf (κ := ℵ₀) x₂)
    (_hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H)) :
    ∀ F G : Form, F.IsInfinite → G.IsInfinite → eval x₁ x₂ F = eval x₁ x₂ G := by
  have h₁ : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂ := by rw [← h]; exact KMonoid.self_mem_addOf x₁
  have h₂ : x₂ ∈ KMonoid.addOf (κ := ℵ₀) x₁ := by rw [h]; exact KMonoid.self_mem_addOf x₂
  have habs₁ := cmul_top_absorb x₁ x₂ h₁
  have habs₂ := cmul_top_absorb x₂ x₁ h₂
  -- the two infinite multiples agree, both being `ℵ₀ x₁ + ℵ₀ x₂`
  have heq : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ := by
    have e₁ := habs₁ ⊤
    have e₂ := habs₂ ⊤
    rw [ecmul_top] at e₁ e₂
    rw [← e₂, add_comm, e₁]
  -- every infinite form evaluates to `ℵ₀ x₁`
  have key : ∀ F : Form, F.IsInfinite → eval x₁ x₂ F = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ := by
    intro F hF
    rcases hF with hc | hc
    · rw [eval, hc, ecmul_top]
      exact habs₂ F.2
    · rw [eval, hc, ecmul_top, add_comm, habs₁ F.1, heq]
  exact fun F G hF hG => (key F hF).trans (key G hG).symm

/-- **Corollary 5.5(2)**, equivalence: `add x₁ = add x₂` with no mixed forms is exactly
realizability by a ring whose countably (non finitely) generated projectives are all free.

**This corrects the scaffold**, in the same two ways as `prop_5_4_hereditary` and
`corollary_5_5_one`: the freeness clause is over the classes of `V^{ℵ₀}(R)` — the countably
generated projectives — rather than over all projective modules, for which it is false; and
`EveryProjectiveIsSumOfFG R` is carried explicitly, since the paper reaches it from Theorem 5.3
through the quoted Corollary 4.6.

(i) ⇒ (ii): each generator lies in `add` of the other, so conditions (i) and (ii) of Theorem 5.3
hold — the first because `ℵ₀ x_j` absorbs `ℵ₀ x_i`, the second vacuously — and (iii) is assumed;
Theorem 5.3 then realises `H`, and `[P₂] ≼ ℵ₀ [P₁]` in both directions makes both trace ideals `R`,
so Proposition 5.4's hereditary half gives freeness.  (ii) ⇒ (i): freeness makes `ℵ₀ [P₁]` and
`ℵ₀ [P₂]` both equal to `ℵ₀ [R]`, which is the hypothesis of Theorem 5.3(i) with `n = 0`. -/
theorem corollary_5_5_two (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (KMonoid.addOf (κ := ℵ₀) x₁ = KMonoid.addOf (κ := ℵ₀) x₂ ∧ NoMixedForms x₁ x₂) ↔
      (∃ (R : Type u) (_ : Ring R), EveryProjectiveIsSumOfFG R ∧
        (∀ q : (projClass R ℵ₀ le_rfl).carrier,
            ¬ Module.Finite R ((projClass R ℵ₀ le_rfl).rep q) →
            ∃ ι : Type u, #ι ≤ ℵ₀ ∧
              Nonempty ((projClass R ℵ₀ le_rfl).rep q ≃ₗ[R] DirectSum ι (fun _ => R))) ∧
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) := by
  classical
  constructor
  · rintro ⟨heq, hmix⟩
    have hx₁ : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂ := by
      rw [← heq]; exact KMonoid.self_mem_addOf x₁
    have hx₂ : x₂ ∈ KMonoid.addOf (κ := ℵ₀) x₁ := by
      rw [heq]; exact KMonoid.self_mem_addOf x₂
    -- the conditions of Theorem 5.3
    have hc1 : Cond1 x₁ x₂ := by
      intro n _
      refine ⟨?_, hx₁⟩
      have habs := cmul_top_absorb x₁ x₂ hx₁ ⊤
      rw [ecmul_top] at habs
      exact habs.symm.trans (add_comm _ _)
    have hc1' : Cond1 x₂ x₁ := by
      intro n _
      refine ⟨?_, hx₂⟩
      have habs := cmul_top_absorb x₂ x₁ hx₂ ⊤
      rw [ecmul_top] at habs
      exact habs.symm.trans (add_comm _ _)
    obtain ⟨R, hring, -, -, hfg, e, hhom, hbij⟩ :=
      theorem_5_3_backward x₁ x₂ (ULift.{u} ℚ) hgen hc1 hc1'
        (fun hnot => absurd hx₁ hnot) (fun hnot => absurd hx₂ hnot) hmix
    refine ⟨R, hring, hfg, ?_, e, hhom, hbij⟩
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    -- transport the generators back along the isomorphism
    obtain ⟨e', hleft, hright⟩ : ∃ g : H → (projClass R ℵ₀ le_rfl).carrier,
        Function.LeftInverse g e ∧ Function.RightInverse g e :=
      ⟨(Equiv.ofBijective e hbij).symm, (Equiv.ofBijective e hbij).left_inv,
        (Equiv.ofBijective e hbij).right_inv⟩
    have he' : KMonoid.IsKHom (ℵ₀ : Cardinal.{u}) e' := hhom.inv hbij hright
    have he'surj : Function.Surjective e' := hleft.surjective
    have hgenp : KMonoid.KGenerates (ℵ₀ : Cardinal.{u})
        ({e' x₁, e' x₂} : Set (projClass R ℵ₀ le_rfl).carrier) := by
      have := KMonoid.KGenerates.map he' he'surj hgen
      rwa [Set.image_pair] at this
    have hncp : ∀ x : (projClass R ℵ₀ le_rfl).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set (projClass R ℵ₀ le_rfl).carrier) := by
      intro x hx
      refine hnoncyclic (e x) ?_
      have := KMonoid.KGenerates.map hhom hbij.2 hx
      rwa [Set.image_singleton] at this
    -- both trace ideals are `R`
    have hkey : ∀ a b : H, b ∈ KMonoid.addOf (κ := ℵ₀) a →
        e' b ≼ KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (e' a) := by
      intro a b hab
      obtain ⟨z, n, hzn⟩ := hab
      obtain ⟨w, hw⟩ : b ≼ KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl a :=
        AddLe.trans ⟨z, hzn⟩ (KMonoid.cmul_le_cmul _ _
          (le_of_lt Cardinal.natCast_lt_aleph0) a)
      refine ⟨e' w, ?_⟩
      rw [← KMonoid.IsKHom.map_add he', hw, map_cmul_of_isKHom he']
    have ht₁ : traceIdeal R ((projClass R ℵ₀ le_rfl).rep (e' x₁)) = ⊤ :=
      traceIdeal_eq_top_of_addLe R (e' x₁) (e' x₂) hgenp hncp (hkey x₁ x₂ hx₂)
    have ht₂ : traceIdeal R ((projClass R ℵ₀ le_rfl).rep (e' x₂)) = ⊤ :=
      traceIdeal_eq_top_of_addLe R (e' x₂) (e' x₁) (by rwa [Set.pair_comm]) hncp
        (hkey x₂ x₁ hx₁)
    exact (prop_5_4_hereditary R hfg (e' x₁) (e' x₂) hgenp hncp).mp (ht₁.trans ht₂.symm)
  · rintro ⟨R, hring, hfg, hfree, e, hhom, hbij⟩
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
    obtain ⟨e', hleft, hright⟩ : ∃ g : H → (projClass R ℵ₀ le_rfl).carrier,
        Function.LeftInverse g e ∧ Function.RightInverse g e :=
      ⟨(Equiv.ofBijective e hbij).symm, (Equiv.ofBijective e hbij).left_inv,
        (Equiv.ofBijective e hbij).right_inv⟩
    have he' : KMonoid.IsKHom (ℵ₀ : Cardinal.{u}) e' := hhom.inv hbij hright
    have hgenp : KMonoid.KGenerates (ℵ₀ : Cardinal.{u})
        ({e' x₁, e' x₂} : Set (projClass R ℵ₀ le_rfl).carrier) := by
      have := KMonoid.KGenerates.map he' hleft.surjective hgen
      rwa [Set.image_pair] at this
    have hncp : ∀ x : (projClass R ℵ₀ le_rfl).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set (projClass R ℵ₀ le_rfl).carrier) := by
      intro x hx
      refine hnoncyclic (e x) ?_
      have := KMonoid.KGenerates.map hhom hbij.2 hx
      rwa [Set.image_singleton] at this
    obtain ⟨hne₁, hne₂⟩ := ne_zero_of_not_cyclic (e' x₁) (e' x₂) hgenp hncp
    -- both `ℵ₀ [P_i]` are `ℵ₀ [R]`, hence equal
    have hcm : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₁ = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ := by
      have h₁ := cmul_top_eq_unitClass_of_free R k (e' x₁) hne₁ hfree
      have h₂ := cmul_top_eq_unitClass_of_free R k (e' x₂) hne₂ hfree
      have hstep : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (e' x₁)
          = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (e' x₂) := h₁.trans h₂.symm
      have := congrArg e hstep
      rwa [map_cmul_of_isKHom hhom, map_cmul_of_isKHom hhom, hright x₁, hright x₂] at this
    -- Theorem 5.3(i) with `n = 0`
    obtain ⟨hc1, hc1', -, -, hmix⟩ :=
      theorem_5_3_forward x₁ x₂ R hfg hgen hnoncyclic e hhom hbij
    have habs : ∀ a b : H, KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl a
        = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b →
        KMonoid.cmul (κ := ℵ₀) (0 : ℕ) (le_trans (le_of_lt Cardinal.natCast_lt_aleph0) le_rfl) a
          + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b
        = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl a + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b := by
      intro a b hab
      rw [KMonoid.cmul_natCast, zero_nsmul, zero_add, hab, cmul_top_add_self]
    refine ⟨le_antisymm (addOf_subset_of_mem ((hc1 0 (habs x₁ x₂ hcm)).2))
      (addOf_subset_of_mem ((hc1' 0 (habs x₂ x₁ hcm.symm)).2)), hmix⟩

/-- **Corollary 5.5(3)**, first claim: `x₁ ∈ add x₂` forces `ℵ₀ x₂ + β x₁ = ℵ₀ x₂` for every `β`.
Generation is not needed — this is `cmul_top_absorb`. -/
theorem corollary_5_5_three_absorb (h : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂)
    (_hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H)) (β : ℕ∞) :
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ + ecmul β x₁ = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ :=
  cmul_top_absorb x₁ x₂ h β

/-- **Corollary 5.5(3)**, equivalence: for `add x₁ ⊊ add x₂`, realizability with a non-free
`P^{(ℵ₀)}` is equivalent to an explicit relation condition, and to a strict trace inclusion. -/
theorem corollary_5_5_three (h₁ : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂)
    (h₂ : x₂ ∉ KMonoid.addOf (κ := ℵ₀) x₁)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (∀ (n : ℕ) (β : ℕ∞), eval x₁ x₂ (⊤, (n : ℕ∞)) = eval x₁ x₂ (⊤, β) →
        β ≠ ⊤ ∧ ∃ m m' : ℕ, eval x₁ x₂ ((m : ℕ∞), β) = eval x₁ x₂ ((m' : ℕ∞), (n : ℕ∞)))
      ∧ NoMixedForms x₁ x₂ ↔
      (∃ (R : Type u) (_ : Ring R), EveryProjectiveIsSumOfFG R ∧
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) := by
  sorry

end Cor55

/-! ## The counterexample `ℕ₀² ∪ {∞}`

Corollary 5.5(2) and 5.5(3) each assert "the converse is not true", both witnessed by the trivial
`ℵ₀`-extension of `ℕ₀²` with `x₁ = (1,0)`, `x₂ = (0,1)`.  That is Example 2.3(1), already
formalised in `KappaMonoid/Examples.lean`, so both are cheap — and worth doing early as a check on
the encoding above. -/

section Counterexample

/-- The underlying monoid `ℕ₀²` of the counterexample, lifted into `Type u`. -/
abbrev NatSq : Type u := ULift.{u} (ℕ × ℕ)

theorem isConical_natSq : IsConical NatSq.{u} := by
  rintro ⟨a⟩ ⟨b⟩ hab
  have h : a + b = (0 : ℕ × ℕ) := congrArg ULift.down hab
  have h1 : a.1 + b.1 = 0 := congrArg Prod.fst h
  have h2 : a.2 + b.2 = 0 := congrArg Prod.snd h
  have ha : a = (0, 0) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
  have hb : b = (0, 0) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
  exact ⟨congrArg ULift.up ha, congrArg ULift.up hb⟩

/-- `n` copies of `(a, b)` are `(n·a, n·b)`. -/
theorem nsmul_natSq (n a b : ℕ) : n • (⟨(a, b)⟩ : NatSq.{u}) = ⟨(n * a, n * b)⟩ := by
  induction n with
  | zero =>
      rw [zero_nsmul]
      show (0 : NatSq.{u}) = ⟨(0 * a, 0 * b)⟩
      rw [Nat.zero_mul, Nat.zero_mul]
      rfl
  | succ p hp =>
      rw [succ_nsmul, hp]
      show (⟨(p * a + a, p * b + b)⟩ : NatSq.{u}) = ⟨((p + 1) * a, (p + 1) * b)⟩
      rw [Nat.succ_mul, Nat.succ_mul]

/-- The counterexample `H := ℕ₀² ∪ {∞}`, the trivial `ℵ₀`-extension of `ℕ₀²`. -/
noncomputable instance : KMonoid (ℵ₀ : Cardinal.{u}) (WithTop NatSq.{u}) :=
  TrivExt.instKMonoid isConical_natSq le_rfl

/-- `x₁ = (1,0)`. -/
def cex₁ : WithTop NatSq.{u} := ((⟨(1, 0)⟩ : NatSq.{u}) : WithTop NatSq.{u})

/-- `x₂ = (0,1)`. -/
def cex₂ : WithTop NatSq.{u} := ((⟨(0, 1)⟩ : NatSq.{u}) : WithTop NatSq.{u})

/-- A nonzero element of `ℕ₀²` stays nonzero in `ℕ₀² ∪ {∞}`. -/
theorem coe_natSq_ne_zero {a b : ℕ} (h : a ≠ 0 ∨ b ≠ 0) :
    ((⟨(a, b)⟩ : NatSq.{u}) : WithTop NatSq.{u}) ≠ 0 := by
  intro hz
  have h0 : (⟨(a, b)⟩ : NatSq.{u}) = 0 := WithTop.coe_eq_zero.mp hz
  rcases h with h | h
  · exact h (congrArg (fun x : NatSq.{u} => x.down.1) h0)
  · exact h (congrArg (fun x : NatSq.{u} => x.down.2) h0)

theorem cex₁_ne_zero : cex₁.{u} ≠ 0 := coe_natSq_ne_zero (Or.inl one_ne_zero)

theorem cex₂_ne_zero : cex₂.{u} ≠ 0 := coe_natSq_ne_zero (Or.inr one_ne_zero)

/-- `n` copies of `x₁ = (1,0)` are `(n,0)`. -/
theorem cmul_cex₁ (n : ℕ) (h : ((n : ℕ) : Cardinal.{u}) ≤ ℵ₀) :
    KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u}) h cex₁.{u}
      = ((⟨(n, 0)⟩ : NatSq.{u}) : WithTop NatSq.{u}) := by
  have h1 : KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u}) h cex₁.{u} = n • cex₁.{u} :=
    KMonoid.cmul_natCast cex₁.{u} n
  rw [h1, cex₁, ← TrivExt.coe_nsmul, nsmul_natSq]
  norm_num

/-- `n` copies of `x₂ = (0,1)` are `(0,n)`. -/
theorem cmul_cex₂ (n : ℕ) (h : ((n : ℕ) : Cardinal.{u}) ≤ ℵ₀) :
    KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u}) h cex₂.{u}
      = ((⟨(0, n)⟩ : NatSq.{u}) : WithTop NatSq.{u}) := by
  have h1 : KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u}) h cex₂.{u} = n • cex₂.{u} :=
    KMonoid.cmul_natCast cex₂.{u} n
  rw [h1, cex₂, ← TrivExt.coe_nsmul, nsmul_natSq]
  norm_num

/-- In `ℕ₀² ∪ {∞}` a finite element divides another only coordinatewise. -/
theorem le_of_add_eq_coe (z : WithTop NatSq.{u}) (p q : ℕ × ℕ)
    (hz : ((⟨p⟩ : NatSq.{u}) : WithTop NatSq.{u}) + z = ((⟨q⟩ : NatSq.{u}) : WithTop NatSq.{u})) :
    p.1 ≤ q.1 ∧ p.2 ≤ q.2 := by
  have hzt : z ≠ ⊤ := by
    intro h
    rw [h, WithTop.add_top] at hz
    exact WithTop.top_ne_coe hz
  lift z to NatSq.{u} using hzt with z'
  rw [← WithTop.coe_add] at hz
  have h' : (⟨p⟩ : NatSq.{u}) + z' = ⟨q⟩ := WithTop.coe_injective hz
  have h1 : p.1 + z'.down.1 = q.1 := congrArg (fun x : NatSq.{u} => x.down.1) h'
  have h2 : p.2 + z'.down.2 = q.2 := congrArg (fun x : NatSq.{u} => x.down.2) h'
  omega

/-- In `ℕ₀² ∪ {∞}` the two generators have incomparable `add` sets. -/
theorem cex_incomparable :
    cex₁.{u} ∉ KMonoid.addOf (κ := ℵ₀) cex₂.{u} ∧
      cex₂.{u} ∉ KMonoid.addOf (κ := ℵ₀) cex₁.{u} := by
  constructor
  · rintro ⟨z, n, hzn⟩
    have hzn' : cex₁.{u} + z = ((⟨(0, n)⟩ : NatSq.{u}) : WithTop NatSq.{u}) :=
      hzn.trans (cmul_cex₂ n _)
    exact absurd (le_of_add_eq_coe z (1, 0) (0, n) hzn').1 (by omega)
  · rintro ⟨z, n, hzn⟩
    have hzn' : cex₂.{u} + z = ((⟨(n, 0)⟩ : NatSq.{u}) : WithTop NatSq.{u}) :=
      hzn.trans (cmul_cex₁ n _)
    exact absurd (le_of_add_eq_coe z (0, 1) (n, 0) hzn').2 (by omega)

/-- `ℵ₀` copies of either generator are `∞`. -/
theorem cmul_top_cex₁ : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₁.{u} = (⊤ : WithTop NatSq.{u}) :=
  TrivExt.cmul_top_eq_top isConical_natSq le_rfl cex₁_ne_zero

theorem cmul_top_cex₂ : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} = (⊤ : WithTop NatSq.{u}) :=
  TrivExt.cmul_top_eq_top isConical_natSq le_rfl cex₂_ne_zero

/-- Yet `ℵ₀ x₂ + β x₁ = ℵ₀ x₂` for every `β`, both sides being `∞`.  With `cex_incomparable`
this refutes the converse asserted in Corollary 5.5(3). -/
theorem cex_absorb (β : ℕ∞) :
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} + ecmul β cex₁.{u}
      = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} :=
  calc KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} + ecmul β cex₁.{u}
      = (⊤ : WithTop NatSq.{u}) + ecmul β cex₁.{u} := by rw [cmul_top_cex₂]
    _ = (⊤ : WithTop NatSq.{u}) := WithTop.top_add _
    _ = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} := cmul_top_cex₂.symm

/-- And `∞` is the only element with an infinite form, although `add x₁ ≠ add x₂`.  With
`cex_incomparable` this refutes the converse asserted in Corollary 5.5(2). -/
theorem cex_unique_infinite :
    (∀ F G : Form, F.IsInfinite → G.IsInfinite →
        eval cex₁.{u} cex₂.{u} F = eval cex₁.{u} cex₂.{u} G) ∧
      KMonoid.addOf (κ := ℵ₀) cex₁.{u} ≠ KMonoid.addOf (κ := ℵ₀) cex₂.{u} := by
  have htop : ∀ F : Form, F.IsInfinite → eval cex₁.{u} cex₂.{u} F = (⊤ : WithTop NatSq.{u}) := by
    intro F hF
    rcases hF with h | h
    · rw [eval, h, ecmul_top, cmul_top_cex₁, WithTop.top_add]
    · rw [eval, h, ecmul_top, cmul_top_cex₂, WithTop.add_top]
  refine ⟨fun F G hF hG => (htop F hF).trans (htop G hG).symm, fun hset => ?_⟩
  -- `x₁ ∈ add x₁`, so equality of the two sets would contradict incomparability
  exact cex_incomparable.1 (hset ▸ KMonoid.self_mem_addOf cex₁.{u})

end Counterexample

end TwoGen

end KappaMonoid
