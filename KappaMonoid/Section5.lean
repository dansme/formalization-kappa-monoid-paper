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

universe u

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
  have hx₁S : x₁ ∈ S := key x₁ x₂ hgen
  have hx₂S : x₂ ∈ S := key x₂ x₁ (by rwa [Set.pair_comm])
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

/-- **Theorem 5.3**: a non-cyclic `ℵ₀`-monoid on two generators is `V^{ℵ₀}(R)` for a hereditary
ring exactly when conditions (i), (ii) and (iii) hold for both orderings of the generators.

The paper's `1 ≤ i ≠ j ≤ 2` is rendered as a conjunction over the two orderings rather than as
`Fin 2` bookkeeping, which would cost more than it saves.

Forward: Lemma 5.1 gives braidedness, then (iii) is 5.2(1), (ii) is 5.2(4), and (i) is the
counting argument — cofinitely many blocks sum to `|I_μ| x_j`, so `x_i ∈ add x_j`, then 5.2(3).

Backward: verify braidedness over `add (x₁ + x₂)` by the four-case split of the paper
(`fin/fin`; `m,ℵ₀` vs `m',ℵ₀`; `ℵ₀,n` vs `m,ℵ₀`; `m,ℵ₀` vs `ℵ₀,ℵ₀`), then apply Corollary 4.7(1)
— `corollary_4_7_one_forward`, which is where axiom A5 enters. -/
theorem theorem_5_3 (k : Type u) [Field k]
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (∃ (R : Type u) (_ : Ring R) (_ : Algebra k R) (_ : ∀ I : Ideal R, Module.Projective R I),
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) ↔
      (Cond1 x₁ x₂ ∧ Cond1 x₂ x₁ ∧ Cond2 x₁ x₂ ∧ Cond2 x₂ x₁ ∧ NoMixedForms x₁ x₂) := by
  sorry

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

end Trace

section Prop54

variable (R : Type u) [Ring R]

/-- **Proposition 5.4**: for a ring with non-cyclic `V^{ℵ₀}(R)` generated by `[P₁]` and `[P₂]`,
the four conditions `Tr(P₂) ⊆ Tr(P₁)`, `Tr(P₁) = R`, `P₂ | P₁^{(ℵ₀)}` and `P₁^{(ℵ₀)}` free are
equivalent.

The two classes are given as carrier elements `p₁ p₂` and their modules as `rep p₁`, `rep p₂` —
`ModuleClass` has no constructor taking a module to its class, only `rep` going the other way.

(i) ⇒ (ii) is `P₂ · Tr(P₁) = P₂`; (ii) ⇒ (iii) writes `1 ∈ im f₁ + ⋯ + im f_k` to split `R` off
`P₁^k`; (iii) ⇒ (iv) is Lemma 2.14 (`eq_cmul_top_of_add`, proved); (iv) ⇒ (i) is immediate. -/
theorem prop_5_4 (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier))
    (hnoncyclic : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      ∀ x : (projClass R ℵ₀ le_rfl).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set (projClass R ℵ₀ le_rfl).carrier)) :
    (traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) ≤ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁)
        ↔ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤) ∧
      (traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤ ↔
        ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
          Nonempty (DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) ≃ₗ[R]
            (projClass R ℵ₀ le_rfl).rep p₂ × Q)) := by
  sorry

/-- **Proposition 5.4**, final statement: over a hereditary ring, `Tr(P₁) = Tr(P₂)` exactly when
every countably (non finitely) generated projective is free. -/
theorem prop_5_4_hereditary (hR : ∀ I : Ideal R, Module.Projective R I)
    (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier)) :
    traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁)
        = traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) ↔
      ∀ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q), Module.Projective R Q →
        ¬ Module.Finite R Q →
          (∃ ι : Type u, #ι ≤ ℵ₀ ∧ Nonempty (Q ≃ₗ[R] DirectSum ι (fun _ => R))) := by
  sorry

end Prop54

/-! ## Corollary 5.5 (`hereditarycase`)

Case analysis on how `add x₁` and `add x₂` compare.  All three parts are bookkeeping on top of
Theorem 5.3, with Proposition 5.4 for part (3)'s trace formulation. -/

section Cor55

variable (x₁ x₂ : H)

/-- **Corollary 5.5(1)**: for incomparable generators, realizability is equivalent to an explicit
condition on the relations of `H`.

(i) ⇒ (ii) adds `ℵ₀ x_j` to reduce to Theorem 5.3(i); (ii) ⇒ (i) verifies the three conditions of
Theorem 5.3, of which (i) holds vacuously. -/
theorem corollary_5_5_one (h₁ : x₁ ∉ KMonoid.addOf (κ := ℵ₀) x₂)
    (h₂ : x₂ ∉ KMonoid.addOf (κ := ℵ₀) x₁)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (∃ (R : Type u) (_ : Ring R), EveryProjectiveIsSumOfFG R ∧
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) ↔
      (∀ F G : Form, eval x₁ x₂ F = eval x₁ x₂ G → (F.1 = ⊤ ↔ G.1 = ⊤)) ∧
        (∀ F G : Form, F.1 = ⊤ → G.1 = ⊤ → eval x₁ x₂ F = eval x₁ x₂ G →
          ∃ m₁ m₂ : ℕ, eval x₁ x₂ ((m₁ : ℕ∞), F.2) = eval x₁ x₂ ((m₂ : ℕ∞), G.2)) := by
  sorry

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
realizability by a ring whose countably (non finitely) generated projectives are all free. -/
theorem corollary_5_5_two (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (KMonoid.addOf (κ := ℵ₀) x₁ = KMonoid.addOf (κ := ℵ₀) x₂ ∧ NoMixedForms x₁ x₂) ↔
      (∃ (R : Type u) (_ : Ring R),
        (∀ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q), Module.Projective R Q →
          ¬ Module.Finite R Q → (∃ ι : Type u, #ι ≤ ℵ₀ ∧ Nonempty (Q ≃ₗ[R] DirectSum ι (fun _ => R)))) ∧
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) := by
  sorry

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
