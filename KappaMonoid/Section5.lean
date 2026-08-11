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

/-- A **form** `α X₁ + β X₂`: a pair of coefficients in `{0, 1, 2, …, ℵ₀}`. -/
abbrev Form : Type := ℕ∞ × ℕ∞

/-- `a` copies of `x`, where `a = ⊤` means `ℵ₀` copies. -/
noncomputable def ecmul (a : ℕ∞) (x : H) : H :=
  KMonoid.cmul (κ := ℵ₀) (Cardinal.ofENat a) (Cardinal.ofENat_le_aleph0 a) x

@[simp] theorem ecmul_top (x : H) : ecmul (⊤ : ℕ∞) x = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x := by
  simp [ecmul]

/-- The element of `H` represented by a form. -/
noncomputable def eval (x₁ x₂ : H) (F : Form) : H := ecmul F.1 x₁ + ecmul F.2 x₂

/-- A form is *infinite* if at least one coefficient is. -/
def Form.IsInfinite (F : Form) : Prop := F.1 = ⊤ ∨ F.2 = ⊤

/-- A form is *finite* otherwise. -/
def Form.IsFinite (F : Form) : Prop := F.1 ≠ ⊤ ∧ F.2 ≠ ⊤

theorem Form.not_isInfinite_iff (F : Form) : ¬ F.IsInfinite ↔ F.IsFinite := by
  simp [Form.IsInfinite, Form.IsFinite, not_or]

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
  sorry

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

/-- **Lemma 5.2(3)**: if `x₁ ∈ add x₂` and no element has both a finite and an infinite form, then
`α X₁ + ℵ₀ X₂` and `β X₁ + ℵ₀ X₂` are braided, for all `α, β ≤ ℵ₀`.

The paper gives the partitions outright.  With `n x₂ = t + α x₁`:

    I₀ = {0, …, α-1},   I_k = {α + n(k-1), …, α + n(k-1) + n - 1}  (k ≥ 1),
    J_k = {nk, …, nk + n - 1}  (k ≥ 0),   u_k = α x₁,   v_0 = 0,  v_k = t  (k ≥ 1).

Build the `BraidingData` with `BraidingData.mk_finsum` (Braiding.lean), which takes finite
partitions and `finsum` equations.  The proof splits on `α` finite versus `α = ⊤`; the second case
first re-derives `m x₂ = (m'+1) x₁ + n' x₂` and then builds its own partitions.

Expect this to be the longest proof in the section. -/
theorem lemma_5_2_three (hmem : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂) (hmix : NoMixedForms x₁ x₂)
    (α β : ℕ∞)
    (hFm : ∀ n, familyOfForm x₁ x₂ (α, ⊤) n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ n, familyOfForm x₁ x₂ (β, ⊤) n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ (α, ⊤) (β, ⊤) hFm hGm := by
  sorry

/-- **Lemma 5.2(4)**: for incomparable generators, a braiding of `m X₁ + ℵ₀ X₂` with
`n X₁ + ℵ₀ X₂` forces a finite relation `m x₁ + k x₂ = n x₁ + k' x₂`. -/
theorem lemma_5_2_four (hmem : x₁ ∉ KMonoid.addOf (κ := ℵ₀) x₂) (hmix : NoMixedForms x₁ x₂)
    (m n : ℕ)
    (hFm : ∀ i, familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ i, familyOfForm x₁ x₂ ((n : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hbr : BraidedForms x₁ x₂ ((m : ℕ∞), ⊤) ((n : ℕ∞), ⊤) hFm hGm) :
    ∃ k k' : ℕ, eval x₁ x₂ ((m : ℕ∞), (k : ℕ∞)) = eval x₁ x₂ ((n : ℕ∞), (k' : ℕ∞)) := by
  sorry

/-- **Lemma 5.2(5)**: if `H` is braided over `add (x₁ + x₂)`, then `x₁ ∈ add x₂` exactly when
`ℵ₀ (x₁ + x₂) = ℵ₀ x₂`.

Uses Lemma 2.14, `eq_cmul_top_of_add` in `OrderUnit.lean`, which is proved. -/
theorem lemma_5_2_five
    (hbr : letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
      IsBraidedOver ℵ₀ ℵ₀ ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) H le_rfl (fun y => (y : H))) :
    x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂ ↔
      KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (x₁ + x₂) = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ := by
  sorry

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
