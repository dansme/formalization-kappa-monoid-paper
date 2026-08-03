/-
A Lean 4 / Mathlib formalisation of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

Part 1 — Section 2: infinite summation, `κ`-monoids and `λ⁻`-monoids.

Design notes (see also `README.md`):

* Index sets.  The paper indexes by the von Neumann cardinal `κ` itself.  We let the
  summation operation act on families indexed by an *arbitrary* type of the right size:
  `λ⁻`-monoids sum families indexed by any `ι` with `#ι < λ`.  Nothing has to be transported
  along a chosen bijection, and the reindexing law is an axiom rather than a theorem.

* One theory, not two.  A `κ`-monoid is exactly a `λ⁻`-monoid for `λ = κ⁺` (Remark 2.19;
  `#ι ≤ κ ↔ #ι < κ⁺`, and `κ⁺` is regular).  So `LMonoid` is developed once and `KMonoid`
  extends it; the `κ`-level names (`sumOf`, `ksum`, …) are a thin layer on top.

* Underlying additive monoid.  By Lemma 2.5 a `λ⁻`-monoid carries a canonical commutative
  monoid structure with `a + b = Σ²(a, b)`.  Following Mathlib's forgetful-inheritance
  convention, `LMonoid` *extends* `AddCommMonoid` and adds the compatibility axiom
  `add_eq_lsumOf`; this prevents a second, propositionally-equal `+` from appearing on types
  that already have one.  Nothing is lost: `SumData.toLMonoid` builds the additive structure
  from the summation alone (Lemma 2.5).

* (A1).  The paper states (A1) for the distinguished element `0 ∈ κ`.  Here it is the
  statement that a sum over a one-point index type is its unique entry, which needs no
  distinguished element and no `0`.
-/
import Mathlib

universe u v w

open Cardinal Function Set

namespace KappaMonoid

/-! ## Preliminaries on cardinals and index types -/

/-- `Idx κ` is a fixed type of cardinality `κ`, playing the role of the von Neumann cardinal
`κ` used as an index set in the paper.  It no longer occurs in the axioms; it is kept for the
constructions of Sections 3 and 4, which produce `κ`-indexed data. -/
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

theorem mk_lt_of_injective {lam : Cardinal.{u}} {α β : Type u} (hβ : #β < lam) (f : α → β)
    (hf : Function.Injective f) : #α < lam :=
  (Cardinal.mk_le_of_injective hf).trans_lt hβ

/-! ### Two-element index types

Binary addition is a sum over a two-element index type; these are the equivalences used to
recognise it as such. -/

/-- A pair of families, viewed as one dependent family over `ULift Bool`. -/
def boolFam {α β : Type u} {X : Type v} (f : α → X) (g : β → X) :
    ∀ p : ULift.{u} Bool, (bif p.down then β else α) → X
  | ⟨true⟩ => g
  | ⟨false⟩ => f

/-- `Σ p : ULift Bool, (bif p.down then β else α) ≃ α ⊕ β`. -/
def sigmaBoolEquiv (α β : Type u) :
    ((p : ULift.{u} Bool) × (bif p.down then β else α)) ≃ α ⊕ β :=
  (Equiv.sigmaCongrLeft' (Equiv.ulift (α := Bool))).trans (Equiv.sumEquivSigmaBool α β).symm

/-- `ULift Bool ≃ PUnit ⊕ PUnit`, sending `false` to the left and `true` to the right. -/
def uliftBoolEquiv : ULift.{u} Bool ≃ PUnit.{u + 1} ⊕ PUnit.{u + 1} :=
  (Equiv.ulift (α := Bool)).trans Equiv.boolEquivPUnitSumPUnit

/-! ## Bare summation data

`SumData lam X` is a `λ⁻`-monoid structure without its additive monoid: the data of
Definition 2.18 and nothing else.  `SumData.toLMonoid` reconstructs the addition
(Lemma 2.5), so no generality is lost by letting `LMonoid` extend `AddCommMonoid`. -/

/-- The data of a `λ⁻`-monoid: a summation operation for families indexed by an arbitrary
type of cardinality `< lam`, subject to reindexing (A3), the one-point law (A1/B1) and the
associativity law (A2/B2). -/
structure SumData (lam : Cardinal.{u}) (X : Type v) where
  /-- `lam` is regular. -/
  isRegular : lam.IsRegular
  /-- The summation operation. -/
  sum : ∀ {ι : Type u}, #ι < lam → (ι → X) → X
  /-- Sums are invariant under reindexing. -/
  sum_congr : ∀ {ι ι' : Type u} (h : #ι < lam) (h' : #ι' < lam) (e : ι ≃ ι') (x : ι' → X),
      sum h (x ∘ e) = sum h' x
  /-- (A1)/(B1): a sum over a one-point index type is its unique entry. -/
  sum_unique : ∀ {ι : Type u} [Unique ι] (h : #ι < lam) (x : ι → X), sum h x = x default
  /-- (A2)/(B2): a sum may be computed by first summing over the fibres of a partition. -/
  sum_sigma : ∀ {ι : Type u} {ρ : ι → Type u} (h : #ι < lam) (hρ : ∀ i, #(ρ i) < lam)
      (x : ∀ i, ρ i → X) (hσ : #((i : ι) × ρ i) < lam),
      sum h (fun i => sum (hρ i) (x i)) = sum hσ (fun p => x p.1 p.2)

namespace SumData

variable {lam : Cardinal.{u}} {X : Type v} (S : SumData lam X)

include S

theorem small (ι : Type u) [Finite ι] : #ι < lam := mk_lt_of_finite S.isRegular ι

theorem hsum {α β : Type u} (hα : #α < lam) (hβ : #β < lam) : #(α ⊕ β) < lam :=
  mk_sum_lt S.isRegular hα hβ

/-- The neutral element: the empty sum. -/
noncomputable def zero : X := S.sum (S.small PEmpty.{u + 1}) PEmpty.elim

/-- The binary operation: a sum over a two-point index type. -/
noncomputable def add (a b : X) : X :=
  S.sum (S.hsum (S.small PUnit.{u + 1}) (S.small PUnit.{u + 1}))
    (Sum.elim (fun _ => a) (fun _ => b))

theorem sum_punit (a : X) : S.sum (S.small PUnit.{u + 1}) (fun _ => a) = a := S.sum_unique _ _

/-- A sum over `α ⊕ β` splits as a binary sum: the bridge between `sum` and `add`. -/
theorem sum_sumType {α β : Type u} (hα : #α < lam) (hβ : #β < lam) (hαβ : #(α ⊕ β) < lam)
    (f : α → X) (g : β → X) :
    S.sum hαβ (Sum.elim f g) = S.add (S.sum hα f) (S.sum hβ g) := by
  have hρ : ∀ p : ULift.{u} Bool, #(bif p.down then β else α) < lam := by
    rintro ⟨(_ | _)⟩; exacts [hα, hβ]
  have hσ := mk_sigma_lt S.isRegular (S.small (ULift.{u} Bool)) hρ
  calc S.sum hαβ (Sum.elim f g)
      = S.sum hσ (Sum.elim f g ∘ sigmaBoolEquiv α β) := (S.sum_congr hσ _ _ _).symm
    _ = S.sum hσ (fun p => boolFam f g p.1 p.2) := by
        congr 1; funext p; obtain ⟨⟨(_ | _)⟩, y⟩ := p <;> rfl
    _ = S.sum (S.small (ULift.{u} Bool)) (fun p => S.sum (hρ p) (boolFam f g p)) :=
        (S.sum_sigma (S.small (ULift.{u} Bool)) hρ (boolFam f g) hσ).symm
    _ = S.sum (S.small (ULift.{u} Bool))
          (Sum.elim (fun _ => S.sum hα f) (fun _ => S.sum hβ g) ∘ uliftBoolEquiv) := by
        congr 1; funext p; obtain ⟨(_ | _)⟩ := p <;> rfl
    _ = S.add (S.sum hα f) (S.sum hβ g) := S.sum_congr _ _ uliftBoolEquiv _

theorem add_comm' (a b : X) : S.add a b = S.add b a := by
  have hu := S.small PUnit.{u + 1}
  calc S.add a b = S.sum (S.hsum hu hu) (Sum.elim (fun _ => a) (fun _ => b)) := rfl
    _ = S.sum (S.hsum hu hu)
          (Sum.elim (fun _ => b) (fun _ => a) ∘ Equiv.sumComm PUnit.{u + 1} PUnit.{u + 1}) := by
        congr 1; funext p; rcases p with p | p <;> rfl
    _ = S.add b a := S.sum_congr _ _ _ _

theorem add_assoc' (a b c : X) : S.add (S.add a b) c = S.add a (S.add b c) := by
  have hu := S.small PUnit.{u + 1}
  have hab := S.sum_sumType (S.hsum hu hu) hu (S.hsum (S.hsum hu hu) hu)
    (Sum.elim (fun _ => a) (fun _ => b)) (fun _ => c)
  have hbc := S.sum_sumType hu (S.hsum hu hu) (S.hsum hu (S.hsum hu hu))
    (fun _ => a) (Sum.elim (fun _ => b) (fun _ => c))
  have hadd : ∀ x y : X, S.sum (S.hsum hu hu) (Sum.elim (fun _ => x) (fun _ => y)) = S.add x y :=
    fun _ _ => rfl
  rw [S.sum_punit, hadd] at hab hbc
  rw [← hab, ← hbc, ← S.sum_congr (S.hsum (S.hsum hu hu) hu) (S.hsum hu (S.hsum hu hu))
    (Equiv.sumAssoc PUnit.{u + 1} PUnit.{u + 1} PUnit.{u + 1})]
  congr 1
  funext p
  rcases p with (p | p) | p <;> rfl

theorem zero_add' (a : X) : S.add S.zero a = a := by
  have hu := S.small PUnit.{u + 1}
  have he := S.small PEmpty.{u + 1}
  have h := S.sum_sumType he hu (S.hsum he hu) PEmpty.elim (fun _ => a)
  rw [S.sum_punit] at h
  rw [show S.sum he PEmpty.elim = S.zero from rfl] at h
  rw [← h, ← S.sum_congr hu (S.hsum he hu) (Equiv.emptySum PEmpty.{u + 1} PUnit.{u + 1}).symm,
    show (Sum.elim PEmpty.elim fun _ : PUnit.{u + 1} => a) ∘
      (Equiv.emptySum PEmpty.{u + 1} PUnit.{u + 1}).symm = fun _ => a from rfl, S.sum_punit]

/-- **Lemma 2.5**: the commutative monoid determined by the summation. -/
@[instance_reducible]
noncomputable def addCommMonoid : AddCommMonoid X :=
  letI : Add X := ⟨S.add⟩
  letI : Zero X := ⟨S.zero⟩
  { add := S.add
    zero := S.zero
    nsmul := nsmulRec
    nsmul_zero := fun _ => rfl
    nsmul_succ := fun _ _ => rfl
    add_assoc := S.add_assoc'
    add_comm := S.add_comm'
    zero_add := S.zero_add'
    add_zero := fun a => (S.add_comm' a S.zero).trans (S.zero_add' a) }

end SumData

/-! ## `λ⁻`-monoids (Definition 2.18) and `κ`-monoids (Definition 2.1) -/

/-- A `λ⁻`-monoid for a regular cardinal `λ`: a commutative monoid together with a summation
operation for families indexed by any type of cardinality `< λ`, compatible with `+`.

For `λ = κ⁺` this is Definition 2.1 of a `κ`-monoid, see `KMonoid`; for `λ = ℵ₀` it is just a
commutative monoid, see `LMonoid.ofAddCommMonoid`. -/
class LMonoid (lam : Cardinal.{u}) (X : Type v) extends AddCommMonoid X where
  /-- `lam` is regular. -/
  isRegular : lam.IsRegular
  /-- The summation operation for families indexed by a type of cardinality `< lam`. -/
  lsumOf : ∀ {ι : Type u}, #ι < lam → (ι → X) → X
  /-- Sums are invariant under reindexing. -/
  lsumOf_congr : ∀ {ι ι' : Type u} (h : #ι < lam) (h' : #ι' < lam) (e : ι ≃ ι') (x : ι' → X),
      lsumOf h (x ∘ e) = lsumOf h' x
  /-- (B1): a sum over a one-point index type is its unique entry. -/
  lsumOf_unique : ∀ {ι : Type u} [Unique ι] (h : #ι < lam) (x : ι → X), lsumOf h x = x default
  /-- (B2): a sum may be computed by first summing over the fibres of a partition. -/
  lsumOf_sigma : ∀ {ι : Type u} {ρ : ι → Type u} (h : #ι < lam) (hρ : ∀ i, #(ρ i) < lam)
      (x : ∀ i, ρ i → X) (hσ : #((i : ι) × ρ i) < lam),
      lsumOf h (fun i => lsumOf (hρ i) (x i)) = lsumOf hσ (fun p => x p.1 p.2)
  /-- Compatibility of `+` with the summation.  This is not an extra assumption: by
  Lemma 2.5 the binary sum *is* an addition, see `SumData.toLMonoid`. -/
  add_eq_lsumOf : ∀ (h : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) < lam) (a b : X),
      a + b = lsumOf h (Sum.elim (fun _ => a) (fun _ => b))

namespace SumData

variable {lam : Cardinal.{u}} {X : Type v} (S : SumData lam X)

/-- The `λ⁻`-monoid determined by bare summation data (Lemma 2.5). -/
@[instance_reducible]
noncomputable def toLMonoid : LMonoid lam X :=
  letI := S.addCommMonoid
  { toAddCommMonoid := S.addCommMonoid
    isRegular := S.isRegular
    lsumOf := S.sum
    lsumOf_congr := S.sum_congr
    lsumOf_unique := S.sum_unique
    lsumOf_sigma := S.sum_sigma
    add_eq_lsumOf := fun _ _ _ => rfl }

/-- The `λ⁻`-monoid determined by summation data on a type that already carries a compatible
commutative monoid structure. -/
@[instance_reducible]
noncomputable def toLMonoid' [AddCommMonoid X]
    (hadd : ∀ (h : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) < lam) (a b : X),
      a + b = S.sum h (Sum.elim (fun _ => a) (fun _ => b))) : LMonoid lam X where
  isRegular := S.isRegular
  lsumOf := S.sum
  lsumOf_congr := S.sum_congr
  lsumOf_unique := S.sum_unique
  lsumOf_sigma := S.sum_sigma
  add_eq_lsumOf := hadd

/-- Variant of `addCommMonoid` for a type that already carries the neutral element. -/
@[instance_reducible]
noncomputable def addCommMonoidOfZero [Zero X] (h0 : S.zero = 0) : AddCommMonoid X :=
  letI : Add X := ⟨S.add⟩
  { add := S.add
    zero := (0 : X)
    nsmul := nsmulRec
    nsmul_zero := fun _ => rfl
    nsmul_succ := fun _ _ => rfl
    add_assoc := S.add_assoc'
    add_comm := S.add_comm'
    zero_add := fun a => h0 ▸ S.zero_add' a
    add_zero := fun a => h0 ▸ (S.add_comm' a S.zero).trans (S.zero_add' a) }

/-- Variant of `toLMonoid` for a type that already carries the neutral element. -/
@[instance_reducible]
noncomputable def toLMonoidOfZero [Zero X] (h0 : S.zero = 0) : LMonoid lam X :=
  { toAddCommMonoid := S.addCommMonoidOfZero h0
    isRegular := S.isRegular
    lsumOf := S.sum
    lsumOf_congr := S.sum_congr
    lsumOf_unique := S.sum_unique
    lsumOf_sigma := S.sum_sigma
    add_eq_lsumOf := fun _ _ _ => rfl }

end SumData

namespace LMonoid

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X]

theorem isRegular' {X : Type v} [inst : LMonoid lam X] : lam.IsRegular := inst.isRegular

theorem aleph0_le {X : Type v} [inst : LMonoid lam X] : ℵ₀ ≤ lam := inst.isRegular.aleph0_le

theorem mk_lt_finite {X : Type v} [LMonoid lam X] (ι : Type u) [Finite ι] : #ι < lam :=
  mk_lt_of_finite (isRegular' (X := X)) ι

theorem mk_uLift_bool_lt {X : Type v} [LMonoid lam X] : #(ULift.{u} Bool) < lam :=
  mk_lt_finite (X := X) _

/-! ### Basic laws -/

/-- Reindexing along an equivalence. -/
theorem lsumOf_equiv {ι ι' : Type u} (h : #ι < lam) (h' : #ι' < lam) (e : ι' ≃ ι) (x : ι → X) :
    lsumOf (lam := lam) h x = lsumOf (lam := lam) h' (x ∘ e) :=
  (lsumOf_congr h' h e x).symm

/-- A sum over `α ⊕ β` splits as a binary sum. -/
theorem lsumOf_sumType {α β : Type u} (hα : #α < lam) (hβ : #β < lam) (hαβ : #(α ⊕ β) < lam)
    (f : α → X) (g : β → X) :
    lsumOf (lam := lam) hαβ (Sum.elim f g)
      = lsumOf (lam := lam) hα f + lsumOf (lam := lam) hβ g := by
  have hρ : ∀ p : ULift.{u} Bool, #(bif p.down then β else α) < lam := by
    rintro ⟨(_ | _)⟩; exacts [hα, hβ]
  have hUB : #(ULift.{u} Bool) < lam := mk_uLift_bool_lt (X := X)
  have hσ := mk_sigma_lt (isRegular' (X := X)) hUB hρ
  have hu : #PUnit.{u + 1} < lam := mk_lt_finite (X := X) _
  have hPP : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) < lam := mk_sum_lt (isRegular' (X := X)) hu hu
  calc lsumOf (lam := lam) hαβ (Sum.elim f g)
      = lsumOf (lam := lam) hσ (Sum.elim f g ∘ sigmaBoolEquiv α β) :=
        lsumOf_equiv hαβ hσ (sigmaBoolEquiv α β) _
    _ = lsumOf (lam := lam) hσ (fun p => boolFam f g p.1 p.2) := by
        congr 1; funext p; obtain ⟨⟨(_ | _)⟩, y⟩ := p <;> rfl
    _ = lsumOf (lam := lam) hUB (fun p => lsumOf (lam := lam) (hρ p) (boolFam f g p)) :=
        (lsumOf_sigma hUB hρ (boolFam f g) hσ).symm
    _ = lsumOf (lam := lam) hPP
          (Sum.elim (fun _ => lsumOf (lam := lam) hα f) (fun _ => lsumOf (lam := lam) hβ g)) := by
        rw [lsumOf_equiv hPP hUB uliftBoolEquiv]
        congr 1; funext p; obtain ⟨(_ | _)⟩ := p <;> rfl
    _ = lsumOf (lam := lam) hα f + lsumOf (lam := lam) hβ g := (add_eq_lsumOf _ _ _).symm

@[simp] theorem lsumOf_isEmpty {ι : Type u} [IsEmpty ι] (h : #ι < lam) (x : ι → X) :
    lsumOf (lam := lam) h x = 0 := by
  have hu : #PUnit.{u + 1} < lam := mk_lt_finite (X := X) _
  have hsum : #(PUnit.{u + 1} ⊕ ι) < lam := mk_sum_lt (isRegular' (X := X)) hu h
  have h1 : lsumOf (lam := lam) hsum (Sum.elim (fun _ => (0 : X)) x) = 0 + lsumOf (lam := lam) h x := by
    have hkey := lsumOf_sumType hu h hsum (fun _ => (0 : X)) x
    rwa [lsumOf_unique hu (fun _ => (0 : X))] at hkey
  have h2 : lsumOf (lam := lam) hsum (Sum.elim (fun _ => (0 : X)) x) = 0 := by
    rw [lsumOf_equiv hsum hu (Equiv.sumEmpty PUnit.{u + 1} ι).symm]
    exact lsumOf_unique hu _
  rw [h2, zero_add] at h1
  exact h1.symm

@[simp] theorem lsumOf_zero {ι : Type u} (h : #ι < lam) :
    lsumOf (lam := lam) (X := X) h (fun _ => 0) = 0 := by
  have hE : ∀ _ : ι, #PEmpty.{u + 1} < lam := fun _ => mk_lt_finite (X := X) _
  have hσ : #((_ : ι) × PEmpty.{u + 1}) < lam :=
    mk_sigma_lt (isRegular' (X := X)) h hE
  have : IsEmpty ((_ : ι) × PEmpty.{u + 1}) := ⟨fun p => p.2.elim⟩
  have key := lsumOf_sigma h hE (fun (_ : ι) (p : PEmpty.{u + 1}) => (0 : X)) hσ
  have hinner : (fun i : ι => lsumOf (lam := lam) (hE i) (fun _ : PEmpty.{u + 1} => (0 : X)))
      = fun _ : ι => (0 : X) := funext fun i => lsumOf_isEmpty (X := X) (hE i) _
  rw [hinner, lsumOf_isEmpty (X := X) hσ] at key
  exact key

theorem lsumOf_eq_zero_of_forall {ι : Type u} (h : #ι < lam) {x : ι → X} (hx : ∀ i, x i = 0) :
    lsumOf (lam := lam) h x = 0 := by
  rw [funext hx, lsumOf_zero]

/-- Zero-padding along an embedding does not change a sum. -/
theorem lsumOf_extend {ι ι' : Type u} (h : #ι < lam) (h' : #ι' < lam) (e : ι ↪ ι') (x : ι → X) :
    lsumOf (lam := lam) h' (Function.extend e x 0) = lsumOf (lam := lam) h x := by
  have hρ : ∀ j : ι', #{i // e i = j} < lam :=
    fun j => mk_lt_of_injective h Subtype.val Subtype.val_injective
  have hσ : #((j : ι') × {i // e i = j}) < lam := mk_sigma_lt (isRegular' (X := X)) h' hρ
  have hfib : ∀ j, lsumOf (lam := lam) (hρ j) (fun p => x p.1)
      = Function.extend e x (0 : ι' → X) j := by
    intro j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      let _ : Unique {i' // e i' = e i} := ⟨⟨⟨i, rfl⟩⟩, fun p => Subtype.ext (e.injective p.2)⟩
      rw [lsumOf_unique, e.injective.extend_apply]
      exact congrArg x (e.injective (default : {i' // e i' = e i}).2)
    · have : IsEmpty {i // e i = j} := ⟨fun p => hj ⟨p.1, p.2⟩⟩
      rw [lsumOf_isEmpty, Function.extend_apply' _ _ _ hj]
      rfl
  calc lsumOf (lam := lam) h' (Function.extend e x 0)
      = lsumOf (lam := lam) h' (fun j => lsumOf (lam := lam) (hρ j) (fun p => x p.1)) := by
        congr 1; funext j; exact (hfib j).symm
    _ = lsumOf (lam := lam) hσ (fun p => x p.2.1) := lsumOf_sigma h' hρ _ hσ
    _ = lsumOf (lam := lam) h x := (lsumOf_equiv h hσ (Equiv.sigmaFiberEquiv (fun i => e i)) x).symm

/-- The binary sum, in the `Bool`-indexed form used throughout Sections 3 and 4. -/
theorem lsumOf_two (a b : X) (hUB : #(ULift.{u} Bool) < lam) :
    lsumOf (lam := lam) hUB (fun p : ULift.{u} Bool => if p.down then a else b) = a + b := by
  have hu : #PUnit.{u + 1} < lam := mk_lt_finite (X := X) _
  have hPP : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) < lam := mk_sum_lt (isRegular' (X := X)) hu hu
  rw [lsumOf_equiv hUB hPP uliftBoolEquiv.symm,
    show (fun p : ULift.{u} Bool => if p.down then a else b) ∘ uliftBoolEquiv.symm
      = Sum.elim (fun _ => b) (fun _ => a) by funext p; rcases p with p | p <;> rfl,
    lsumOf_sumType hu hu hPP, lsumOf_unique, lsumOf_unique]
  exact add_comm b a

/-- Sums are additive. -/
theorem lsumOf_add {ι : Type u} (h : #ι < lam) (f g : ι → X) :
    lsumOf (lam := lam) h (fun i => f i + g i)
      = lsumOf (lam := lam) h f + lsumOf (lam := lam) h g := by
  have hu : #PUnit.{u + 1} < lam := mk_lt_finite (X := X) _
  have hPP : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) < lam := mk_sum_lt (isRegular' (X := X)) hu hu
  have hσ : #((_ : ι) × (PUnit.{u + 1} ⊕ PUnit.{u + 1})) < lam :=
    mk_sigma_lt (isRegular' (X := X)) h fun _ => hPP
  have hιι : #(ι ⊕ ι) < lam := mk_sum_lt (isRegular' (X := X)) h h
  set e : ((_ : ι) × (PUnit.{u + 1} ⊕ PUnit.{u + 1})) ≃ ι ⊕ ι :=
    { toFun := fun p => Sum.elim (fun _ => Sum.inl p.1) (fun _ => Sum.inr p.1) p.2
      invFun := Sum.elim (fun i => ⟨i, Sum.inl PUnit.unit⟩) (fun i => ⟨i, Sum.inr PUnit.unit⟩)
      left_inv := by rintro ⟨i, (p | p)⟩ <;> rfl
      right_inv := by rintro (i | i) <;> rfl } with hedef
  have hinner : (fun i => f i + g i)
      = fun i => lsumOf (lam := lam) hPP (Sum.elim (fun _ => f i) (fun _ => g i)) :=
    funext fun i => add_eq_lsumOf _ _ _
  rw [hinner, lsumOf_sigma h (fun _ => hPP)
    (fun (i : ι) (p : PUnit.{u + 1} ⊕ PUnit.{u + 1}) =>
      Sum.elim (fun _ => f i) (fun _ => g i) p) hσ,
    lsumOf_equiv hσ hιι e.symm, ← lsumOf_sumType h h hιι f g]
  congr 1
  funext p
  rcases p with i | i <;> rfl

/-! ### Sums over subsets -/

/-- Terms with value `0` may be discarded. -/
theorem lsumOf_of_subset {ι : Type u} {S T : Set ι} (hS : #S < lam) (hT : #T < lam)
    (hsub : T ⊆ S) (f : ι → X) (hzero : ∀ i ∈ S, i ∉ T → f i = 0) :
    lsumOf (lam := lam) hS (fun i : S => f i) = lsumOf (lam := lam) hT (fun i : T => f i) := by
  classical
  set e : T ↪ S := ⟨Set.inclusion hsub, Set.inclusion_injective hsub⟩ with hedef
  have hfun : (fun i : S => f i) = Function.extend (⇑e) (fun i : T => f i) 0 := by
    funext s
    by_cases hs : (s : ι) ∈ T
    · have hval : e ⟨(s : ι), hs⟩ = s := rfl
      rw [← hval, e.injective.extend_apply]
      rfl
    · rw [Function.extend_apply' (fun i : T => f i) (0 : S → X) s ?_]
      · exact hzero s s.2 hs
      · rintro ⟨t, ht⟩
        exact hs (ht ▸ t.2)
  rw [hfun, lsumOf_extend hT hS e (fun i : T => f i)]

/-- A sum of zeros over a subset vanishes. -/
theorem lsumOf_eq_zero {ι : Type u} {T : Set ι} (hT : #T < lam) (f : ι → X)
    (hzero : ∀ i ∈ T, f i = 0) :
    lsumOf (lam := lam) hT (fun i : T => f i) = 0 :=
  lsumOf_eq_zero_of_forall hT fun i => hzero i i.2

/-- Additivity over a disjoint union of two small subsets. -/
theorem lsumOf_union {ι : Type u} (S T : Set ι) (hd : Disjoint S T) (hS : #S < lam)
    (hT : #T < lam) (hST : #(↥(S ∪ T)) < lam) (f : ι → X) :
    lsumOf (lam := lam) hST (fun i : ↥(S ∪ T) => f i)
      = lsumOf (lam := lam) hS (fun i : S => f i) + lsumOf (lam := lam) hT (fun i : T => f i) := by
  classical
  have hsum : #(↥S ⊕ ↥T) < lam := mk_sum_lt (isRegular' (X := X)) hS hT
  rw [lsumOf_equiv hST hsum (Equiv.Set.union hd).symm, ← lsumOf_sumType hS hT hsum]
  congr 1
  funext p
  rcases p with p | p <;> rfl

/-- Regrouping a sum over a set along a disjoint indexed cover by `< λ`-sized pieces. -/
theorem lsumOf_biUnion_subset {ι J : Type u} (S : Set ι) (I : J → Set ι) (hIS : ∀ p, I p ⊆ S)
    (hdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q)) (hcover : (⋃ p, I p) = S) (hJ : #J < lam)
    (hS : #S < lam) (hI : ∀ p, #(I p) < lam) (x : ι → X) :
    lsumOf (lam := lam) hJ (fun p => lsumOf (lam := lam) (hI p) (fun i : I p => x i))
      = lsumOf (lam := lam) hS (fun i : S => x i) := by
  set Φ : ((p : J) × I p) ≃ S := Equiv.ofBijective
    (fun q : (p : J) × I p => (⟨(q.2 : ι), hIS q.1 q.2.2⟩ : S))
    ⟨by
      rintro ⟨p1, i1, hi1⟩ ⟨p2, i2, hi2⟩ heq
      have heqι : i1 = i2 := congrArg Subtype.val heq
      by_cases hpp : p1 = p2
      · subst hpp; subst heqι; rfl
      · exact absurd hi2 (heqι ▸ (Set.disjoint_left.mp (hdisj p1 p2 hpp) hi1)),
      by
      rintro ⟨i, hiS⟩
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hcover ▸ hiS)
      exact ⟨⟨p, ⟨i, hp⟩⟩, rfl⟩⟩ with hΦdef
  have hσ : #((p : J) × I p) < lam := by rw [Cardinal.mk_congr Φ]; exact hS
  exact (lsumOf_sigma hJ hI (fun p (i : I p) => x (i : ι)) hσ).trans
    (lsumOf_equiv hS hσ Φ (fun s : S => x (s : ι))).symm

/-- A sum over a two-element subset. -/
theorem lsumOf_pair {ι : Type u} {a b : ι} (hab : a ≠ b) (hp : #(↥({a, b} : Set ι)) < lam)
    (f : ι → X) :
    lsumOf (lam := lam) hp (fun i : ({a, b} : Set ι) => f i) = f a + f b := by
  classical
  have hUB : #(ULift.{u} Bool) < lam := mk_uLift_bool_lt (X := X)
  set e : ULift.{u} Bool ≃ ({a, b} : Set ι) :=
    { toFun := fun p => if p.down then ⟨a, by simp⟩ else ⟨b, by simp⟩
      invFun := fun i => ⟨decide ((i : ι) = a)⟩
      left_inv := by
        rintro ⟨(_ | _)⟩
        · simp [hab.symm]
        · simp
      right_inv := by
        rintro ⟨i, hi⟩
        rcases hi with hi | hi
        · simp [hi]
        · simp only [Set.mem_singleton_iff] at hi
          subst hi
          simp [hab.symm] } with hedef
  rw [lsumOf_equiv hp hUB e, ← lsumOf_two (f a) (f b) hUB]
  congr 1
  funext p
  obtain ⟨(_ | _)⟩ := p <;> rfl

/-! ### Restriction to a smaller cardinal -/

/-- Remark 2.19: a `λ'⁻`-monoid is a `λ⁻`-monoid for every regular `λ ≤ λ'`. -/
@[instance_reducible]
noncomputable def ofLE {lam₁ lam₂ : Cardinal.{u}} {Y : Type v} [LMonoid lam₂ Y]
    (hlam : lam₁.IsRegular) (hle : lam₁ ≤ lam₂) : LMonoid lam₁ Y where
  isRegular := hlam
  lsumOf h x := lsumOf (lam := lam₂) (h.trans_le hle) x
  lsumOf_congr _ _ e x := lsumOf_congr _ _ e x
  lsumOf_unique _ x := lsumOf_unique _ x
  lsumOf_sigma h hρ x hσ :=
    lsumOf_sigma (h.trans_le hle) (fun i => (hρ i).trans_le hle) x (hσ.trans_le hle)
  add_eq_lsumOf _ a b := add_eq_lsumOf _ a b

@[simp] theorem ofLE_lsumOf {lam₁ lam₂ : Cardinal.{u}} {Y : Type v} [LMonoid lam₂ Y]
    (hlam : lam₁.IsRegular) (hle : lam₁ ≤ lam₂) {ι : Type u} (h : #ι < lam₁) (x : ι → Y) :
    letI := ofLE (Y := Y) hlam hle
    lsumOf (lam := lam₁) h x = lsumOf (lam := lam₂) (h.trans_le hle) x := rfl

end LMonoid


/-! ## `κ`-monoids (Definition 2.1)

A `κ`-monoid is a `λ⁻`-monoid for `λ = κ⁺` (Remark 2.19): the families that may be summed
are those indexed by a type of cardinality `< κ⁺`, i.e. of cardinality `≤ κ`. -/

/-- A `κ`-monoid: a commutative monoid with a summation operation for families indexed by a
type of cardinality `≤ κ`, subject to (A1) and (A2) of Definition 2.1. -/
class KMonoid (κ : Cardinal.{u}) (H : Type v) extends LMonoid (Order.succ κ) H where
  /-- `κ` is an infinite cardinal. -/
  aleph0_le : ℵ₀ ≤ κ

namespace KMonoid

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

theorem lt_succ {ι : Type u} {κ : Cardinal.{u}} (h : #ι ≤ κ) : #ι < Order.succ κ :=
  Order.lt_succ_iff.mpr h

theorem le_of_lt_succ {ι : Type u} {κ : Cardinal.{u}} (h : #ι < Order.succ κ) : #ι ≤ κ :=
  Order.lt_succ_iff.mp h

theorem isRegular_succ' {H : Type v} [KMonoid κ H] : (Order.succ κ).IsRegular :=
  Cardinal.isRegular_succ (aleph0_le (κ := κ) (H := H))

/-! ### Cardinal bookkeeping at the `κ`-level -/

theorem mk_le_of_finite {H : Type v} [KMonoid κ H] (ι : Type u) [Finite ι] : #ι ≤ κ :=
  le_of_lt_succ (mk_lt_of_finite (isRegular_succ' (H := H)) ι)

theorem mk_uLift_bool_le (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] : #(ULift.{u} Bool) ≤ κ :=
  mk_le_of_finite (H := H) _

theorem mk_sigma_le {H : Type v} [KMonoid κ H] {ι : Type u} {ρ : ι → Type u} (h : #ι ≤ κ)
    (hρ : ∀ i, #(ρ i) ≤ κ) : #((i : ι) × ρ i) ≤ κ :=
  le_of_lt_succ
    (mk_sigma_lt (isRegular_succ' (H := H)) (lt_succ h) fun i => lt_succ (hρ i))

theorem mk_prod_le {H : Type v} [KMonoid κ H] {α β : Type u} (hα : #α ≤ κ) (hβ : #β ≤ κ) :
    #(α × β) ≤ κ :=
  le_of_lt_succ
    (mk_prod_lt (isRegular_succ' (H := H)) (lt_succ hα) (lt_succ hβ))

theorem mk_sum_le {H : Type v} [KMonoid κ H] {α β : Type u} (hα : #α ≤ κ) (hβ : #β ≤ κ) :
    #(α ⊕ β) ≤ κ :=
  le_of_lt_succ
    (mk_sum_lt (isRegular_succ' (H := H)) (lt_succ hα) (lt_succ hβ))

/-! ### Summation -/

/-- The sum of a family indexed by an arbitrary type of cardinality `≤ κ`. -/
noncomputable def sumOf {ι : Type u} (h : #ι ≤ κ) (x : ι → H) : H :=
  LMonoid.lsumOf (lam := Order.succ κ) (lt_succ h) x

theorem sumOf_equiv {ι ι' : Type u} (h : #ι ≤ κ) (h' : #ι' ≤ κ) (e : ι' ≃ ι) (x : ι → H) :
    sumOf (κ := κ) h x = sumOf (κ := κ) h' (x ∘ e) :=
  LMonoid.lsumOf_equiv _ _ e x

@[simp] theorem sumOf_unique {ι : Type u} [Unique ι] (h : #ι ≤ κ) (x : ι → H) :
    sumOf (κ := κ) h x = x default :=
  LMonoid.lsumOf_unique _ x

@[simp] theorem sumOf_of_isEmpty {ι : Type u} [IsEmpty ι] (h : #ι ≤ κ) (x : ι → H) :
    sumOf (κ := κ) h x = 0 :=
  LMonoid.lsumOf_isEmpty _ x

@[simp] theorem sumOf_zero {ι : Type u} (h : #ι ≤ κ) :
    sumOf (κ := κ) (H := H) h (fun _ => 0) = 0 :=
  LMonoid.lsumOf_zero _

/-- The general associativity law: a `κ`-sum may be computed by first summing over the fibres
of a partition. -/
theorem sumOf_sigma {ι : Type u} {ρ : ι → Type u} (h : #ι ≤ κ) (hρ : ∀ i, #(ρ i) ≤ κ)
    (hσ : #((i : ι) × ρ i) ≤ κ) (x : ∀ i, ρ i → H) :
    sumOf (κ := κ) h (fun i => sumOf (κ := κ) (hρ i) (x i))
      = sumOf (κ := κ) hσ (fun p => x p.1 p.2) :=
  LMonoid.lsumOf_sigma _ (fun i => lt_succ (hρ i)) x _

/-- Zero-padding along an embedding does not change a `κ`-sum. -/
theorem sumOf_extend {ι ι' : Type u} (h : #ι ≤ κ) (h' : #ι' ≤ κ) (e : ι ↪ ι') (x : ι → H) :
    sumOf (κ := κ) h' (Function.extend e x 0) = sumOf (κ := κ) h x :=
  LMonoid.lsumOf_extend _ _ e x

/-- A `κ`-sum indexed by (a universe-lifted) `Bool` recovers the binary operation `+`. -/
theorem sumOf_two (a b : H) (hUB : #(ULift.{u} Bool) ≤ κ) :
    sumOf (κ := κ) hUB (fun p : ULift.{u} Bool => if p.down then a else b) = a + b :=
  LMonoid.lsumOf_two a b _

/-- `κ`-sums are additive. -/
theorem sumOf_add {ι : Type u} (h : #ι ≤ κ) (f g : ι → H) :
    sumOf (κ := κ) h (fun i => f i + g i) = sumOf (κ := κ) h f + sumOf (κ := κ) h g :=
  LMonoid.lsumOf_add _ f g

/-- Terms with value `0` may be discarded. -/
theorem sumOf_subtype_support {ι : Type u} (h : #ι ≤ κ) (x : ι → H)
    (h' : #(Function.support x) ≤ κ) :
    sumOf (κ := κ) h x = sumOf (κ := κ) h' (fun i : Function.support x => x i) := by
  classical
  set e : Function.support x ↪ ι := Function.Embedding.subtype _ with hedef
  have hfun : x = Function.extend (⇑e) (fun i : Function.support x => x i) 0 := by
    funext i
    by_cases hi : i ∈ Function.support x
    · have hval : e ⟨i, hi⟩ = i := rfl
      rw [← hval, e.injective.extend_apply]
      rfl
    · rw [Function.extend_apply' (fun i : Function.support x => x i) (0 : ι → H) i ?_]
      · exact not_not.mp hi
      · rintro ⟨t, ht⟩
        exact hi (ht ▸ t.2)
  conv_lhs => rw [hfun]
  exact sumOf_extend h' h e _

/-- The special case of `sumOf_sigma` for a partition of the index set into subsets. -/
theorem sumOf_biUnion {ι J : Type u} (I : J → Set ι) (hdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q))
    (hcover : (⋃ p, I p) = Set.univ) (hJ : #J ≤ κ) (hι : #ι ≤ κ) (hI : ∀ p, #(I p) ≤ κ)
    (x : ι → H) :
    sumOf (κ := κ) hJ (fun p => sumOf (κ := κ) (hI p) (fun i : I p => x i))
      = sumOf (κ := κ) hι x := by
  have huniv : #(↥(Set.univ : Set ι)) ≤ κ := (Cardinal.mk_congr (Equiv.Set.univ ι)).trans_le hι
  have hkey := LMonoid.lsumOf_biUnion_subset (X := H) (Set.univ : Set ι) I
    (fun p => Set.subset_univ _) hdisj hcover (lt_succ hJ) (lt_succ huniv)
    (fun p => lt_succ (hI p)) x
  calc sumOf (κ := κ) hJ (fun p => sumOf (κ := κ) (hI p) (fun i : I p => x i))
      = sumOf (κ := κ) huniv (fun i : (Set.univ : Set ι) => x i) := hkey
    _ = sumOf (κ := κ) hι x := (sumOf_equiv hι huniv (Equiv.Set.univ ι) x).symm

/-! ### Summation over the canonical index type `Idx κ` -/

/-- The `κ`-indexed summation `Σ : H^κ → H` of the paper. -/
noncomputable def ksum (x : Idx κ → H) : H := sumOf (κ := κ) (le_of_eq (mk_Idx κ)) x

theorem sumOf_Idx (x : Idx κ → H) : sumOf (κ := κ) (le_of_eq (mk_Idx κ)) x = ksum (κ := κ) x := rfl

/-- A `κ`-sum may be computed by padding with zeros along *any* embedding into `Idx κ`. -/
theorem sumOf_eq_extend {ι : Type u} (h : #ι ≤ κ) (e : ι ↪ Idx κ) (x : ι → H) :
    sumOf (κ := κ) h x = ksum (κ := κ) (Function.extend e x 0) :=
  (sumOf_extend h (le_of_eq (mk_Idx κ)) e x).symm

@[simp] theorem ksum_zero : ksum (κ := κ) (fun _ : Idx κ => (0 : H)) = 0 := sumOf_zero _

/-- (A1): a family concentrated in one index sums to its unique possibly nonzero entry. -/
theorem ksum_single (i₀ : Idx κ) (x : Idx κ → H) (hx : ∀ i, i ≠ i₀ → x i = 0) :
    ksum (κ := κ) x = x i₀ := by
  classical
  have hpt : #PUnit.{u + 1} ≤ κ := mk_le_of_finite (H := H) _
  set e : PUnit.{u + 1} ↪ Idx κ := ⟨fun _ => i₀, fun _ _ _ => rfl⟩ with hedef
  have hfun : x = Function.extend (⇑e) (fun _ : PUnit.{u + 1} => x i₀) 0 := by
    funext i
    by_cases hi : i = i₀
    · have hval : e PUnit.unit = i₀ := rfl
      rw [hi, ← hval, e.injective.extend_apply]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨p, hp⟩; exact hi hp.symm)]
      exact hx i hi
  show sumOf (κ := κ) (le_of_eq (mk_Idx κ)) x = x i₀
  conv_lhs => rw [hfun]
  rw [sumOf_extend hpt (le_of_eq (mk_Idx κ)) e, sumOf_unique]

/-- (A2): the associativity law modelled on `⨁ᵢ ⨁ⱼ Mᵢⱼ ≅ ⨁_{(i,j)} Mᵢⱼ`. -/
theorem ksum_sigma (x : Idx κ → Idx κ → H) (π : Idx κ × Idx κ ≃ Idx κ) :
    ksum (κ := κ) (fun i => ksum (κ := κ) (x i))
      = ksum (κ := κ) fun k => x (π.symm k).1 (π.symm k).2 := by
  have hidx : #(Idx κ) ≤ κ := le_of_eq (mk_Idx κ)
  have hσ : #((_ : Idx κ) × Idx κ) ≤ κ := mk_sigma_le (H := H) hidx fun _ => hidx
  have h1 : ksum (κ := κ) (fun i => ksum (κ := κ) (x i))
      = sumOf (κ := κ) hσ (fun p => x p.1 p.2) := sumOf_sigma hidx (fun _ => hidx) hσ x
  have h2 : sumOf (κ := κ) hσ (fun p => x p.1 p.2)
      = ksum (κ := κ) (fun k => x (π.symm k).1 (π.symm k).2) :=
    sumOf_equiv hσ hidx (π.symm.trans (Equiv.sigmaEquivProd (Idx κ) (Idx κ)).symm) _
  exact h1.trans h2

/-- Compatibility of `+` with `Σ`. -/
theorem ksum_two (a b : H) (i₀ i₁ : Idx κ) (hne : i₀ ≠ i₁) :
    ksum (κ := κ) (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b := by
  classical
  have hUB : #(ULift.{u} Bool) ≤ κ := mk_uLift_bool_le κ H
  set e : ULift.{u} Bool ↪ Idx κ := ⟨fun p => if p.down then i₀ else i₁, by
    rintro ⟨(_ | _)⟩ ⟨(_ | _)⟩ h
    · rfl
    · exact absurd h.symm hne
    · exact absurd h hne
    · rfl⟩ with hedef
  have he0 : e ⟨true⟩ = i₀ := rfl
  have he1 : e ⟨false⟩ = i₁ := rfl
  set F : ULift.{u} Bool → H := fun p => if p.down then a else b with hFdef
  have hfun : (fun i => if i = i₀ then a else if i = i₁ then b else 0)
      = Function.extend (⇑e) F 0 := by
    funext i
    by_cases h0 : i = i₀
    · have hval : Function.extend (⇑e) F 0 i = a := by
        rw [h0, ← he0, e.injective.extend_apply]
        simp [hFdef]
      rw [hval, if_pos h0]
    · by_cases h1 : i = i₁
      · have hval : Function.extend (⇑e) F 0 i = b := by
          rw [h1, ← he1, e.injective.extend_apply]
          simp [hFdef]
        rw [hval, if_neg h0, if_pos h1]
      · have hval : Function.extend (⇑e) F 0 i = 0 := by
          apply Function.extend_apply'
          rintro ⟨⟨(_ | _)⟩, hp⟩
          · exact h1 (by rw [← hp, he1])
          · exact h0 (by rw [← hp, he0])
        rw [hval, if_neg h0, if_neg h1]
  show sumOf (κ := κ) (le_of_eq (mk_Idx κ)) _ = a + b
  rw [hfun, sumOf_extend hUB (le_of_eq (mk_Idx κ)) e, sumOf_two a b hUB]

/-- (A3), Lemma 2.5: `Σ` is invariant under permutations of the index set. -/
theorem ksum_perm (x : Idx κ → H) (π : Idx κ ≃ Idx κ) :
    ksum (κ := κ) x = ksum (κ := κ) (x ∘ π) :=
  sumOf_equiv _ _ π x

/-- (A4), Lemma 2.5: iterated sums may be interchanged. -/
theorem ksum_comm (x : Idx κ → Idx κ → H) :
    ksum (κ := κ) (fun i => ksum (κ := κ) (x i))
      = ksum (κ := κ) (fun j => ksum (κ := κ) fun i => x i j) := by
  have hidx : #(Idx κ) ≤ κ := le_of_eq (mk_Idx κ)
  have hσ : #((_ : Idx κ) × Idx κ) ≤ κ := mk_sigma_le (H := H) hidx fun _ => hidx
  have h1 : ksum (κ := κ) (fun i => ksum (κ := κ) (x i))
      = sumOf (κ := κ) hσ (fun p => x p.1 p.2) := sumOf_sigma hidx (fun _ => hidx) hσ x
  have h2 : ksum (κ := κ) (fun j => ksum (κ := κ) fun i => x i j)
      = sumOf (κ := κ) hσ (fun p => x p.2 p.1) :=
    sumOf_sigma hidx (fun _ => hidx) hσ (fun j i => x i j)
  rw [h1, h2]
  exact sumOf_equiv hσ hσ ((Equiv.sigmaEquivProd (Idx κ) (Idx κ)).trans
    ((Equiv.prodComm (Idx κ) (Idx κ)).trans (Equiv.sigmaEquivProd (Idx κ) (Idx κ)).symm)) _

/-- Zero-padding along a self-embedding of `Idx κ` does not change a `κ`-sum. -/
theorem ksum_extend (g : Idx κ ↪ Idx κ) (x : Idx κ → H) :
    ksum (κ := κ) (Function.extend g x 0) = ksum (κ := κ) x :=
  sumOf_extend _ _ g x

end KMonoid

/-! ## Reducedness -/

/-- A commutative monoid is *reduced* (or *conical*) if `a + b = 0` forces `a = b = 0`. -/
def IsConical (X : Type v) [AddCommMonoid X] : Prop :=
  ∀ a b : X, a + b = 0 → a = 0 ∧ b = 0

namespace KMonoid

/-! ### Cardinal scalar multiplication (Definition 2.6, Lemma 2.7) -/

section Cmul

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-- `cmul α x` is the sum of `α` many copies of `x` (Definition 2.6). -/
noncomputable def cmul (α : Cardinal.{u}) (hα : α ≤ κ) (x : H) : H :=
  sumOf (κ := κ) (le_of_eq_of_le (mk_Idx α) hα) fun _ : Idx α => x

@[simp] theorem cmul_zero_cardinal (x : H) : cmul (κ := κ) 0 zero_le x = 0 := by
  have : IsEmpty (Idx (0 : Cardinal.{u})) := Cardinal.mk_eq_zero_iff.mp (mk_Idx 0)
  exact sumOf_of_isEmpty _ _

/-- Lemma 2.7(2). -/
theorem cmul_sumOf_cardinal {I : Type u} (hI : #I ≤ κ) (l : I → Cardinal.{u})
    (hl : ∀ i, l i ≤ κ) (hsum : Cardinal.sum l ≤ κ) (x : H) :
    cmul (κ := κ) (Cardinal.sum l) hsum x = sumOf (κ := κ) hI fun i => cmul (κ := κ) (l i) (hl i) x := by
  have hρ : ∀ i, #(Idx (l i)) ≤ κ := fun i => le_of_eq_of_le (mk_Idx (l i)) (hl i)
  have hmk : #((i : I) × Idx (l i)) = Cardinal.sum l := by
    rw [mk_sigma]; exact congrArg _ (funext fun i => mk_Idx (l i))
  have hσ : #((i : I) × Idx (l i)) ≤ κ := le_of_eq_of_le hmk hsum
  obtain ⟨Ψ⟩ := Cardinal.eq.mp (hmk.trans (mk_Idx (Cardinal.sum l)).symm)
  calc cmul (κ := κ) (Cardinal.sum l) hsum x
      = sumOf (κ := κ) hσ (fun _ : (i : I) × Idx (l i) => x) :=
        sumOf_equiv (le_of_eq_of_le (mk_Idx (Cardinal.sum l)) hsum) hσ Ψ (fun _ => x)
    _ = sumOf (κ := κ) hI (fun i => cmul (κ := κ) (l i) (hl i) x) :=
        (sumOf_sigma hI hρ hσ fun i (_ : Idx (l i)) => x).symm

/-- Lemma 2.7(3). -/
theorem cmul_sumOf {I : Type u} (hI : #I ≤ κ) (α : Cardinal.{u}) (hα : α ≤ κ) (x : I → H) :
    cmul (κ := κ) α hα (sumOf (κ := κ) hI x)
      = sumOf (κ := κ) hI fun i => cmul (κ := κ) α hα (x i) := by
  have hα' : #(Idx α) ≤ κ := le_of_eq_of_le (mk_Idx α) hα
  have hσ1 : #((_ : Idx α) × I) ≤ κ := mk_sigma_le (H := H) hα' fun _ => hI
  have hσ2 : #((_ : I) × Idx α) ≤ κ := mk_sigma_le (H := H) hI fun _ => hα'
  have stepA : cmul (κ := κ) α hα (sumOf (κ := κ) hI x)
      = sumOf (κ := κ) hσ1 (fun p : (_ : Idx α) × I => x p.2) :=
    sumOf_sigma hα' (fun _ => hI) hσ1 fun (_ : Idx α) (i : I) => x i
  have stepB : sumOf (κ := κ) hI (fun i => cmul (κ := κ) α hα (x i))
      = sumOf (κ := κ) hσ2 (fun q : (_ : I) × Idx α => x q.1) :=
    sumOf_sigma hI (fun _ => hα') hσ2 fun (i : I) (_ : Idx α) => x i
  have stepC : sumOf (κ := κ) hσ2 (fun q : (_ : I) × Idx α => x q.1)
      = sumOf (κ := κ) hσ1 (fun p : (_ : Idx α) × I => x p.2) :=
    sumOf_equiv hσ2 hσ1 ((Equiv.sigmaEquivProd (Idx α) I).trans
      ((Equiv.prodComm (Idx α) I).trans (Equiv.sigmaEquivProd I (Idx α)).symm)) _
  rw [stepA, stepB, stepC]

/-! ### Reducedness (Lemma 2.8) -/

/-- `κ`-many copies of `0` sum to `0`. -/
theorem cmul_top_zero (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] :
    cmul (κ := κ) κ le_rfl (0 : H) = 0 := sumOf_zero _

/-- Scaling by `κ` distributes over `+`. -/
theorem cmul_top_distrib (a b : H) :
    cmul (κ := κ) κ le_rfl (a + b) = cmul (κ := κ) κ le_rfl a + cmul (κ := κ) κ le_rfl b := by
  have hUB := mk_uLift_bool_le κ H
  rw [← sumOf_two a b hUB,
    cmul_sumOf hUB κ le_rfl (fun p : ULift.{u} Bool => if p.down then a else b)]
  have hcongr : (fun p : ULift.{u} Bool => cmul (κ := κ) κ le_rfl (if p.down then a else b))
      = fun p : ULift.{u} Bool =>
        if p.down then cmul (κ := κ) κ le_rfl a else cmul (κ := κ) κ le_rfl b := by
    funext p
    cases p.down <;> rfl
  rw [hcongr]
  exact sumOf_two _ _ hUB

/-- Lemma 2.8(2), the key idempotence step of the swindle: adding one more copy of `z` to
`κ`-many copies of `z` does not change the value. -/
theorem add_cmul_top_self (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] (z : H) :
    z + cmul (κ := κ) κ le_rfl z = cmul (κ := κ) κ le_rfl z := by
  have hκ := aleph0_le (κ := κ) (H := H)
  obtain ⟨j0⟩ := nonempty_Idx hκ
  have : Infinite (Idx κ) := infinite_Idx hκ
  have hcompl : #(↥({j0}ᶜ : Set (Idx κ))) = κ :=
    (mk_compl_of_infinite {j0} (by
      rw [mk_singleton]
      exact lt_of_lt_of_le one_lt_aleph0 (by rw [mk_Idx]; exact hκ))).trans (mk_Idx κ)
  set I : ULift.{u} Bool → Set (Idx κ) := fun p => match p with
    | ⟨true⟩ => ({j0} : Set (Idx κ))
    | ⟨false⟩ => {j0}ᶜ with hIdef
  have hdisj : ∀ p q : ULift.{u} Bool, p ≠ q → Disjoint (I p) (I q) := by
    rintro ⟨(_ | _)⟩ ⟨(_ | _)⟩ hpq
    · exact absurd rfl hpq
    · exact disjoint_compl_left
    · exact disjoint_compl_right
    · exact absurd rfl hpq
  have hcover : (⋃ p, I p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    by_cases ha : a = j0
    · exact Set.mem_iUnion.mpr ⟨⟨true⟩, ha⟩
    · exact Set.mem_iUnion.mpr ⟨⟨false⟩, ha⟩
  have hJ := mk_uLift_bool_le κ H
  have hI : ∀ p : ULift.{u} Bool, #(I p) ≤ κ := by
    rintro ⟨(_ | _)⟩
    · exact hcompl.le
    · show #(({j0} : Set (Idx κ))) ≤ κ
      rw [mk_singleton]
      exact one_le_aleph0.trans hκ
  have hmain := sumOf_biUnion I hdisj hcover hJ (le_of_eq (mk_Idx κ)) hI (fun _ : Idx κ => z)
  have hleftcompl : sumOf (κ := κ) (hI (⟨false⟩ : ULift.{u} Bool))
      (fun _ : I (⟨false⟩ : ULift.{u} Bool) => z) = cmul (κ := κ) κ le_rfl z := by
    obtain ⟨Ψ⟩ := Cardinal.eq.mp (hcompl.trans (mk_Idx κ).symm)
    exact (sumOf_equiv (le_of_eq (mk_Idx κ)) (hI (⟨false⟩ : ULift.{u} Bool)) Ψ fun _ => z).symm
  have hleft : (fun p => sumOf (κ := κ) (hI p) (fun _ : I p => z))
      = fun p : ULift.{u} Bool => if p.down then z else cmul (κ := κ) κ le_rfl z := by
    funext p
    match p with
    | ⟨true⟩ => exact sumOf_unique (hI (⟨true⟩ : ULift.{u} Bool)) (fun _ => z)
    | ⟨false⟩ => exact hleftcompl
  rw [hleft, sumOf_two z (cmul (κ := κ) κ le_rfl z) hJ] at hmain
  exact hmain

/-- Lemma 2.8(1): a variant of the Eilenberg–Mazur swindle shows that every `κ`-monoid is
reduced.

Paper proof: if `x + y = 0` then
`x = x + κ·0 = x + κ(x+y) = (x + κx) + κy = κx + κy = κ(x+y) = 0`. -/
theorem isConical (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] : IsConical H := by
  have key : ∀ x y : H, x + y = 0 → x = 0 := by
    intro x y hxy
    have hcz := cmul_top_zero κ H
    calc x = x + (0 : H) := (add_zero x).symm
      _ = x + cmul (κ := κ) κ le_rfl 0 := by rw [hcz]
      _ = x + cmul (κ := κ) κ le_rfl (x + y) := by rw [hxy]
      _ = x + (cmul (κ := κ) κ le_rfl x + cmul (κ := κ) κ le_rfl y) := by rw [cmul_top_distrib]
      _ = (x + cmul (κ := κ) κ le_rfl x) + cmul (κ := κ) κ le_rfl y := (add_assoc _ _ _).symm
      _ = cmul (κ := κ) κ le_rfl x + cmul (κ := κ) κ le_rfl y := by rw [add_cmul_top_self κ H x]
      _ = cmul (κ := κ) κ le_rfl (x + y) := (cmul_top_distrib x y).symm
      _ = 0 := by rw [hxy, hcz]
  exact fun x y hxy => ⟨key x y hxy, key y x (by rw [add_comm]; exact hxy)⟩

/-- Applying `cmul κ` twice is the same as applying it once (since `κ * κ = κ`). -/
theorem cmul_top_idem (z : H) :
    cmul (κ := κ) κ le_rfl (cmul (κ := κ) κ le_rfl z) = cmul (κ := κ) κ le_rfl z := by
  have hκ := aleph0_le (κ := κ) (H := H)
  have hidx : #(Idx κ) ≤ κ := le_of_eq (mk_Idx κ)
  have hσm : #((_ : Idx κ) × Idx κ) = κ := by
    rw [Cardinal.mk_congr (Equiv.sigmaEquivProd (Idx κ) (Idx κ)), Cardinal.mk_prod]
    simp [Cardinal.mul_eq_self hκ]
  obtain ⟨Ψ⟩ := Cardinal.eq.mp (hσm.trans (mk_Idx κ).symm)
  calc cmul (κ := κ) κ le_rfl (cmul (κ := κ) κ le_rfl z)
      = sumOf (κ := κ) (le_of_eq hσm) (fun _ : (_ : Idx κ) × Idx κ => z) :=
        sumOf_sigma hidx (fun _ => hidx) (le_of_eq hσm) fun (_ _ : Idx κ) => z
    _ = cmul (κ := κ) κ le_rfl z := (sumOf_equiv hidx (le_of_eq hσm) Ψ fun _ => z).symm

/-- Lemma 2.8(2). -/
theorem add_cmul_top_eq {t₁ t₂ t₃ : H} (h : t₁ + t₂ = cmul (κ := κ) κ le_rfl t₃) :
    t₁ + cmul (κ := κ) κ le_rfl t₃ = cmul (κ := κ) κ le_rfl t₃ := by
  have hstep : cmul (κ := κ) κ le_rfl (t₁ + t₂) = cmul (κ := κ) κ le_rfl t₃ := by
    rw [h]; exact cmul_top_idem t₃
  calc t₁ + cmul (κ := κ) κ le_rfl t₃ = t₁ + cmul (κ := κ) κ le_rfl (t₁ + t₂) := by rw [← hstep]
    _ = t₁ + (cmul (κ := κ) κ le_rfl t₁ + cmul (κ := κ) κ le_rfl t₂) := by rw [cmul_top_distrib]
    _ = (t₁ + cmul (κ := κ) κ le_rfl t₁) + cmul (κ := κ) κ le_rfl t₂ := (add_assoc _ _ _).symm
    _ = cmul (κ := κ) κ le_rfl t₁ + cmul (κ := κ) κ le_rfl t₂ := by rw [add_cmul_top_self κ H t₁]
    _ = cmul (κ := κ) κ le_rfl (t₁ + t₂) := by rw [cmul_top_distrib]
    _ = cmul (κ := κ) κ le_rfl t₃ := hstep

end Cmul

/-! ### Homomorphisms, submonoids and generation (Section 2.1) -/

section Sub

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-- A homomorphism of `κ`-monoids. -/
def IsKHom (κ : Cardinal.{u}) {H : Type v} {K : Type w} [KMonoid κ H] [KMonoid κ K]
    (f : H → K) : Prop :=
  f 0 = 0 ∧ ∀ x : Idx κ → H, f (ksum (κ := κ) x) = ksum (κ := κ) (f ∘ x)

/-- A `κ`-submonoid of a `κ`-monoid. -/
structure IsKSubmonoid (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) : Prop where
  zero_mem : (0 : H) ∈ S
  ksum_mem : ∀ x : Idx κ → H, (∀ i, x i ∈ S) → ksum (κ := κ) x ∈ S

/-- A `κ`-submonoid is closed under sums over arbitrary small index types. -/
theorem IsKSubmonoid.sumOf_mem {S : Set H} (hS : IsKSubmonoid κ S) {ι : Type u} (h : #ι ≤ κ)
    (x : ι → H) (hx : ∀ i, x i ∈ S) : sumOf (κ := κ) h x ∈ S := by
  classical
  rw [← sumOf_extend h (le_of_eq (mk_Idx κ)) (emb h) x]
  refine hS.ksum_mem _ fun k => ?_
  by_cases hk : ∃ i, emb h i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [(emb h).injective.extend_apply]
    exact hx i
  · rw [Function.extend_apply' _ _ _ hk]
    exact hS.zero_mem

/-- A `κ`-submonoid is closed under `+`. -/
theorem IsKSubmonoid.add_mem {S : Set H} (hS : IsKSubmonoid κ S) {a b : H} (ha : a ∈ S)
    (hb : b ∈ S) : a + b ∈ S := by
  have hUB := mk_uLift_bool_le κ H
  rw [← sumOf_two a b hUB]
  exact hS.sumOf_mem hUB _ (by rintro ⟨(_ | _)⟩ <;> simpa)

/-- The `κ`-submonoid `⟨S⟩_κ` generated by a subset. -/
def kclosure (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) : Set H :=
  ⋂₀ {T | S ⊆ T ∧ IsKSubmonoid κ T}

theorem subset_kclosure {S : Set H} : S ⊆ kclosure κ S := fun _ hx _ hT => hT.1 hx

/-- The `κ`-closure of a set is a `κ`-submonoid: an intersection of `κ`-submonoids is one. -/
theorem isKSubmonoid_kclosure (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) :
    IsKSubmonoid κ (kclosure κ S) where
  zero_mem := fun _ hT => hT.2.zero_mem
  ksum_mem := fun x hx T hT => hT.2.ksum_mem x fun i => hx i T hT

/-- `⟨S⟩_κ` is the smallest `κ`-submonoid containing `S`. -/
theorem kclosure_le {S T : Set H} (hST : S ⊆ T) (hT : IsKSubmonoid κ T) : kclosure κ S ⊆ T :=
  fun _ hx => hx T ⟨hST, hT⟩

theorem kclosure_mono {S S' : Set H} (h : S ⊆ S') : kclosure κ S ⊆ kclosure κ S' :=
  kclosure_le (h.trans subset_kclosure) (isKSubmonoid_kclosure κ S')

/-- Elements of `⟨S⟩_κ` are exactly the `κ`-sums of families in `S`. -/
theorem mem_kclosure_iff {S : Set H} (h0 : (0 : H) ∈ S) (h : H) :
    h ∈ kclosure κ S ↔ ∃ x : Idx κ → H, (∀ i, x i ∈ S) ∧ h = ksum (κ := κ) x := by
  classical
  have hκ := aleph0_le (κ := κ) (H := H)
  obtain ⟨i₀⟩ := nonempty_Idx hκ
  refine ⟨fun hh => ?_, ?_⟩
  · refine hh {h | ∃ x : Idx κ → H, (∀ i, x i ∈ S) ∧ h = ksum (κ := κ) x} ⟨?_, ?_, ?_⟩
    · intro a ha
      refine ⟨fun i => if i = i₀ then a else 0, fun i => ?_, ?_⟩
      · show (if i = i₀ then a else 0) ∈ S
        by_cases hi : i = i₀
        · rwa [if_pos hi]
        · rwa [if_neg hi]
      · rw [ksum_single i₀ _ fun i hi => if_neg hi, if_pos rfl]
    · exact ⟨fun _ => 0, fun _ => h0, ksum_zero.symm⟩
    · intro y hy
      choose x hxS hxsum using hy
      refine ⟨fun k => x ((pairEquiv hκ).symm k).1 ((pairEquiv hκ).symm k).2, fun k => hxS _ _, ?_⟩
      rw [← ksum_sigma x (pairEquiv hκ)]
      exact congrArg _ (funext hxsum)
  · rintro ⟨x, hxS, rfl⟩
    exact (isKSubmonoid_kclosure κ S).ksum_mem x fun i => subset_kclosure (hxS i)

/-- Definition 2.10: `H` is generated as a `κ`-monoid by `S`. -/
def KGenerates (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) : Prop :=
  kclosure κ S = Set.univ

end Sub

end KMonoid

/-! ## Induced structures on sub-objects -/

/-- The commutative monoid structure on a subset containing `0` and closed under `+`. -/
@[instance_reducible]
def addCommMonoidOfClosed {H : Type v} [AddCommMonoid H] {S : Set H} (h0 : (0 : H) ∈ S)
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) : AddCommMonoid ↥S :=
  inferInstanceAs (AddCommMonoid
    ↥({ carrier := S, add_mem' := fun {a b} ha hb => hadd a ha b hb, zero_mem' := h0 } :
      AddSubmonoid H))

/-- A subset of a `κ`-monoid closed under `λ⁻`-sums. -/
structure IsLSubset (lam : Cardinal.{u}) {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]
    (hlk : lam ≤ κ) (S : Set H) : Prop where
  zero_mem : (0 : H) ∈ S
  sumOf_mem : ∀ {ι : Type u} (h : #ι < lam) (x : ι → H), (∀ i, x i ∈ S) →
    KMonoid.sumOf (κ := κ) (h.le.trans hlk) x ∈ S

namespace KMonoid

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-- A `κ`-submonoid of a `κ`-monoid is itself a `κ`-monoid. -/
@[instance_reducible]
noncomputable def IsKSubmonoid.kmonoid {S : Set H} (hS : IsKSubmonoid κ S) : KMonoid κ ↥S :=
  letI acm : AddCommMonoid ↥S :=
    addCommMonoidOfClosed hS.zero_mem fun _ ha _ hb => hS.add_mem ha hb
  { toAddCommMonoid := acm
    aleph0_le := aleph0_le (κ := κ) (H := H)
    isRegular := isRegular_succ' (H := H)
    lsumOf := fun {ι} h x =>
      ⟨sumOf (κ := κ) (le_of_lt_succ h) fun i => (x i : H),
        hS.sumOf_mem _ _ fun i => (x i).2⟩
    lsumOf_congr := fun h h' e x =>
      Subtype.ext (sumOf_equiv (le_of_lt_succ h') (le_of_lt_succ h) e fun i => (x i : H)).symm
    lsumOf_unique := fun h x => Subtype.ext (sumOf_unique (le_of_lt_succ h) fun i => (x i : H))
    lsumOf_sigma := fun h hρ x hσ =>
      Subtype.ext (sumOf_sigma (le_of_lt_succ h) (fun i => le_of_lt_succ (hρ i))
        (le_of_lt_succ hσ) fun i j => (x i j : H))
    add_eq_lsumOf := fun h a b => Subtype.ext (by
      show (a : H) + (b : H) = sumOf (κ := κ) (le_of_lt_succ h) _
      rw [LMonoid.add_eq_lsumOf (lam := Order.succ κ) (le_of_lt_succ h |> lt_succ) (a : H) (b : H)]
      exact congrArg _ (funext fun p => by rcases p with p | p <;> rfl)) }

/-- A `λ⁻`-closed subset of a `κ`-monoid is a `λ⁻`-monoid. -/
@[instance_reducible]
noncomputable def _root_.KappaMonoid.IsLSubset.lmonoid {lam : Cardinal.{u}} {hlk : lam ≤ κ} {S : Set H}
    (hlam : lam.IsRegular) (hS : IsLSubset lam hlk S) : LMonoid lam ↥S :=
  letI hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := by
    intro a ha b hb
    have hUB : #(ULift.{u} Bool) < lam :=
      lt_of_lt_of_le (Cardinal.lt_aleph0_iff_finite.mpr inferInstance) hlam.aleph0_le
    have hmem := hS.sumOf_mem hUB (fun p : ULift.{u} Bool => if p.down then a else b)
      (by rintro ⟨(_ | _)⟩ <;> simpa)
    rwa [sumOf_two a b (hUB.le.trans hlk)] at hmem
  letI acm : AddCommMonoid ↥S := addCommMonoidOfClosed hS.zero_mem hadd
  { toAddCommMonoid := acm
    isRegular := hlam
    lsumOf := fun {ι} h x =>
      ⟨sumOf (κ := κ) (h.le.trans hlk) fun i => (x i : H), hS.sumOf_mem h _ fun i => (x i).2⟩
    lsumOf_congr := fun h h' e x =>
      Subtype.ext (sumOf_equiv (h'.le.trans hlk) (h.le.trans hlk) e fun i => (x i : H)).symm
    lsumOf_unique := fun h x => Subtype.ext (sumOf_unique (h.le.trans hlk) fun i => (x i : H))
    lsumOf_sigma := fun h hρ x hσ =>
      Subtype.ext (sumOf_sigma (h.le.trans hlk) (fun i => (hρ i).le.trans hlk)
        (hσ.le.trans hlk) fun i j => (x i j : H))
    add_eq_lsumOf := fun h a b => Subtype.ext (by
      show (a : H) + (b : H) = sumOf (κ := κ) (h.le.trans hlk) _
      rw [LMonoid.add_eq_lsumOf (lam := Order.succ κ) (lt_succ (h.le.trans hlk)) (a : H) (b : H)]
      exact congrArg _ (funext fun p => by rcases p with p | p <;> rfl)) }

/-- The inclusion of a `κ`-submonoid preserves sums over arbitrary small index types. -/
theorem IsKSubmonoid.coe_sumOf {T : Set H} (hT : IsKSubmonoid κ T) {ι : Type u} (hι : #ι ≤ κ)
    (z : ι → T) :
    letI := hT.kmonoid
    ((sumOf (κ := κ) hι z : T) : H) = sumOf (κ := κ) hι fun i => (z i : H) := rfl

/-- The inclusion of a `κ`-submonoid preserves `κ`-sums. -/
theorem IsKSubmonoid.coe_ksum {T : Set H} (hT : IsKSubmonoid κ T) (z : Idx κ → T) :
    letI := hT.kmonoid
    ((ksum (κ := κ) z : T) : H) = ksum (κ := κ) fun i => (z i : H) := rfl

/-- The inclusion of a `λ⁻`-closed subset preserves `λ⁻`-sums: they are computed as the
ambient `κ`-sums. -/
theorem _root_.KappaMonoid.IsLSubset.coe_lsumOf {lam : Cardinal.{u}} {hlk : lam ≤ κ} {S : Set H}
    (hlam : lam.IsRegular) (hS : IsLSubset lam hlk S) {ι : Type u} (hι : #ι < lam) (z : ι → S) :
    letI := hS.lmonoid hlam
    ((LMonoid.lsumOf (lam := lam) hι z : S) : H)
      = sumOf (κ := κ) (hι.le.trans hlk) fun i => (z i : H) := rfl

/-- A `κ`-monoid is a `λ⁻`-monoid for every regular `λ ≤ κ` (Remark 2.19). -/
@[instance_reducible]
noncomputable def toLMonoidOfLE (H : Type v) [KMonoid κ H] {lam : Cardinal.{u}}
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) : LMonoid lam H :=
  LMonoid.ofLE (lam₂ := Order.succ κ) hlam (hlk.trans (Order.le_succ κ))

/-- The `λ⁻`-sums induced on a `κ`-monoid by `toLMonoidOfLE` are its `κ`-sums. -/
theorem toLMonoidOfLE_lsumOf {lam : Cardinal.{u}} (hlam : lam.IsRegular) (hlk : lam ≤ κ)
    {ι : Type u} (h : #ι < lam) (x : ι → H) :
    letI := toLMonoidOfLE H hlam hlk
    LMonoid.lsumOf (lam := lam) h x = sumOf (κ := κ) (h.le.trans hlk) x := rfl

end KMonoid


/-! ## Reconstructing a `κ`-monoid from `κ`-indexed data (Lemma 2.5)

The constructions of Sections 3 and 4 produce a summation operation for `Idx κ`-indexed
families only.  This section turns such data into a `κ`-monoid: an arbitrary family of size
`≤ κ` is summed by padding it with zeros along an embedding into `Idx κ`, the point being
that the result does not depend on the embedding chosen. -/

/-- Two embeddings whose ranges have equinumerous complements differ by a permutation. -/
theorem exists_perm_comp {ι : Type u} {κ : Cardinal.{u}} (e₁ e₂ : ι ↪ Idx κ)
    (h : #(↥(Set.range ⇑e₁)ᶜ) = #(↥(Set.range ⇑e₂)ᶜ)) :
    ∃ σ : Idx κ ≃ Idx κ, ∀ i, σ (e₁ i) = e₂ i := by
  classical
  obtain ⟨γ⟩ := Cardinal.eq.mp h
  set α : ↥(Set.range ⇑e₁) ≃ ↥(Set.range ⇑e₂) :=
    (Equiv.ofInjective _ e₁.injective).symm.trans (Equiv.ofInjective _ e₂.injective) with hα
  refine ⟨(Equiv.Set.sumCompl (Set.range ⇑e₁)).symm.trans
    ((α.sumCongr γ).trans (Equiv.Set.sumCompl (Set.range ⇑e₂))), fun i => ?_⟩
  have hmem : e₁ i ∈ Set.range ⇑e₁ := ⟨i, rfl⟩
  have hval : α ⟨e₁ i, hmem⟩ = Equiv.ofInjective _ e₂.injective i := by
    rw [hα, Equiv.trans_apply]
    congr 1
    apply (Equiv.ofInjective _ e₁.injective).injective
    rw [Equiv.apply_symm_apply]
    rfl
  show (Equiv.Set.sumCompl (Set.range ⇑e₂))
      ((α.sumCongr γ) ((Equiv.Set.sumCompl (Set.range ⇑e₁)).symm (e₁ i))) = e₂ i
  rw [Equiv.Set.sumCompl_symm_apply_of_mem hmem, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.Set.sumCompl_apply_inl, hval]
  rfl

/-- "Bare" `κ`-monoid data: a pointed type with a `κ`-indexed summation subject to (A1) and
(A2).  By Lemma 2.5 the additive structure and the sums over arbitrary index types of size
`≤ κ` are determined by this data; `KMonoid.ofBare` reconstructs them. -/
structure BareKMonoid (κ : Cardinal.{u}) (H : Type v) [Zero H] where
  /-- `κ` is an infinite cardinal. -/
  aleph0_le : ℵ₀ ≤ κ
  /-- The `κ`-indexed summation. -/
  ksum : (Idx κ → H) → H
  /-- (A1). -/
  ksum_single : ∀ (i₀ : Idx κ) (x : Idx κ → H), (∀ i, i ≠ i₀ → x i = 0) → ksum x = x i₀
  /-- (A2). -/
  ksum_sigma : ∀ (x : Idx κ → Idx κ → H) (π : Idx κ × Idx κ ≃ Idx κ),
      ksum (fun i => ksum (x i)) = ksum fun k => x (π.symm k).1 (π.symm k).2

namespace BareKMonoid

variable {κ : Cardinal.{u}} {H : Type v} [Zero H] (B : BareKMonoid κ H)

include B

/-- A fixed bijection `Idx κ × Idx κ ≃ Idx κ`. -/
noncomputable def pair : Idx κ × Idx κ ≃ Idx κ := pairEquiv B.aleph0_le

/-- A fixed index, used as the "column" along which families are spread out. -/
noncomputable def j₀ : Idx κ := (nonempty_Idx B.aleph0_le).some

theorem ksum_zero : B.ksum (fun _ => 0) = 0 :=
  B.ksum_single B.j₀ _ fun _ _ => rfl

/-- (A3): the summation is invariant under permutations of `Idx κ`. -/
theorem ksum_perm (x : Idx κ → H) (π : Idx κ ≃ Idx κ) : B.ksum x = B.ksum (x ∘ π) := by
  set y : Idx κ → Idx κ → H := fun i j => if j = B.j₀ then x i else 0 with hy
  set w : Idx κ → Idx κ → H := fun i j => y (π i) j
  have hxy : ∀ i, B.ksum (y i) = x i := fun i =>
    (B.ksum_single B.j₀ (y i) fun j hj => if_neg hj).trans (if_pos rfl)
  set f := B.pair with hf
  set g : Idx κ × Idx κ ≃ Idx κ := (π.symm.prodCongr (Equiv.refl (Idx κ))).trans f with hg
  have hgsymm : ∀ l : Idx κ, g.symm l = (π (f.symm l).1, (f.symm l).2) := by
    intro l
    apply Prod.ext <;>
      simp [hg, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  have hstep : (fun l => y (g.symm l).1 (g.symm l).2) = fun l => w (f.symm l).1 (f.symm l).2 := by
    funext l
    rw [hgsymm l]
  calc B.ksum x = B.ksum (fun i => B.ksum (y i)) := by congr 1; funext i; exact (hxy i).symm
    _ = B.ksum (fun l => y (g.symm l).1 (g.symm l).2) := B.ksum_sigma y g
    _ = B.ksum (fun l => w (f.symm l).1 (f.symm l).2) := congrArg _ hstep
    _ = B.ksum (fun i => B.ksum (w i)) := (B.ksum_sigma w f).symm
    _ = B.ksum (x ∘ π) := by congr 1; funext i; exact hxy (π i)

/-- The "first row" embedding `i ↦ (i, j₀)` of `Idx κ` into itself. -/
noncomputable def row : Idx κ ↪ Idx κ :=
  ⟨fun i => B.pair (i, B.j₀), fun _ _ h => (Prod.ext_iff.mp (B.pair.injective h)).1⟩

/-- Zero-padding along `row` does not change the sum: this is (A2) applied to a family
concentrated in one column. -/
theorem ksum_row (z : Idx κ → H) : B.ksum (Function.extend ⇑B.row z 0) = B.ksum z := by
  set Y : Idx κ → Idx κ → H := fun i j => if j = B.j₀ then z i else 0
  have hYsum : ∀ i, B.ksum (Y i) = z i := fun i =>
    (B.ksum_single B.j₀ (Y i) fun j hj => if_neg hj).trans (if_pos rfl)
  have hkey : ∀ k, Y (B.pair.symm k).1 (B.pair.symm k).2 = Function.extend ⇑B.row z 0 k := by
    intro k
    by_cases hk : ∃ i, B.row i = k
    · obtain ⟨i, rfl⟩ := hk
      have hps : B.pair.symm (B.row i) = (i, B.j₀) := B.pair.symm_apply_apply (i, B.j₀)
      rw [hps]
      show (if B.j₀ = B.j₀ then z i else 0) = _
      rw [if_pos rfl, B.row.injective.extend_apply]
    · have hne : (B.pair.symm k).2 ≠ B.j₀ := by
        intro heq
        exact hk ⟨(B.pair.symm k).1, by
          show B.pair ((B.pair.symm k).1, B.j₀) = k
          rw [← heq]
          exact B.pair.apply_symm_apply k⟩
      show (if (B.pair.symm k).2 = B.j₀ then _ else 0) = _
      rw [if_neg hne, Function.extend_apply' z (0 : Idx κ → H) k hk]
      rfl
  calc B.ksum (Function.extend ⇑B.row z 0)
      = B.ksum (fun k => Y (B.pair.symm k).1 (B.pair.symm k).2) := by
        congr 1; funext k; exact (hkey k).symm
    _ = B.ksum (fun i => B.ksum (Y i)) := (B.ksum_sigma Y B.pair).symm
    _ = B.ksum z := by congr 1; funext i; exact hYsum i

theorem mk_compl_row : #(↥(Set.range ⇑B.row)ᶜ) = κ := by
  have := nontrivial_Idx B.aleph0_le
  obtain ⟨j₁, hj₁⟩ := exists_ne B.j₀
  have hmem : ∀ i : Idx κ, B.pair (i, j₁) ∈ (Set.range ⇑B.row)ᶜ := by
    rintro i ⟨i', hi'⟩
    exact hj₁ (Prod.ext_iff.mp (B.pair.injective hi')).2.symm
  have hinj : Function.Injective
      (fun i : Idx κ => (⟨B.pair (i, j₁), hmem i⟩ : ↥(Set.range ⇑B.row)ᶜ)) := by
    intro a b hab
    exact (Prod.ext_iff.mp (B.pair.injective (congrArg Subtype.val hab))).1
  exact le_antisymm ((Cardinal.mk_set_le _).trans_eq (mk_Idx κ))
    ((mk_Idx κ).symm.trans_le (Cardinal.mk_le_of_injective hinj))

/-- Composing with `row` forces the complement of the range to have full cardinality. -/
theorem mk_compl_trans {ι : Type u} (e : ι ↪ Idx κ) :
    #(↥(Set.range ⇑(e.trans B.row))ᶜ) = κ := by
  have hsub : (Set.range ⇑B.row)ᶜ ⊆ (Set.range ⇑(e.trans B.row))ᶜ := by
    apply Set.compl_subset_compl.mpr
    rintro k ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  exact le_antisymm ((Cardinal.mk_set_le _).trans_eq (mk_Idx κ))
    (B.mk_compl_row.symm.trans_le (Cardinal.mk_le_mk_of_subset hsub))

/-- Zero-padded sums do not depend on the embedding, as long as both ranges have large
complement. -/
theorem ksum_extend_congr {ι : Type u} (e₁ e₂ : ι ↪ Idx κ) (h₁ : #(↥(Set.range ⇑e₁)ᶜ) = κ)
    (h₂ : #(↥(Set.range ⇑e₂)ᶜ) = κ) (x : ι → H) :
    B.ksum (Function.extend ⇑e₁ x 0) = B.ksum (Function.extend ⇑e₂ x 0) := by
  obtain ⟨σ, hσ⟩ := exists_perm_comp e₁ e₂ (h₁.trans h₂.symm)
  have hfun : Function.extend ⇑e₂ x 0 = (Function.extend ⇑e₁ x 0) ∘ σ.symm := by
    funext k
    by_cases hk : ∃ i, e₂ i = k
    · obtain ⟨i, rfl⟩ := hk
      show Function.extend ⇑e₂ x 0 (e₂ i) = Function.extend ⇑e₁ x 0 (σ.symm (e₂ i))
      rw [e₂.injective.extend_apply, ← hσ i, Equiv.symm_apply_apply, e₁.injective.extend_apply]
    · have hnot : ¬ ∃ i, e₁ i = σ.symm k := by
        rintro ⟨i, hi⟩
        exact hk ⟨i, by rw [← hσ i, hi, Equiv.apply_symm_apply]⟩
      show Function.extend ⇑e₂ x 0 k = Function.extend ⇑e₁ x 0 (σ.symm k)
      rw [Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ hnot]
      rfl
  rw [hfun]
  exact B.ksum_perm _ σ.symm

/-- The sum of a family indexed by an arbitrary type of cardinality `≤ κ`. -/
noncomputable def bsum {ι : Type u} (h : #ι ≤ κ) (x : ι → H) : H :=
  B.ksum (Function.extend ⇑((emb h).trans B.row) x 0)

theorem extend_trans_row {ι : Type u} (e : ι ↪ Idx κ) (x : ι → H) :
    Function.extend ⇑(e.trans B.row) x 0 = Function.extend ⇑B.row (Function.extend ⇑e x 0) 0 := by
  have hraw := Function.Injective.extend_comp e.injective B.row.injective x (0 : Idx κ → H)
  have h0 : (0 : Idx κ → H) ∘ (⇑B.row) = (0 : Idx κ → H) := rfl
  rw [h0] at hraw
  exact hraw

/-- `bsum` may be computed using *any* embedding of the index type into `Idx κ`. -/
theorem ksum_extend_eq {ι : Type u} (h : #ι ≤ κ) (e : ι ↪ Idx κ) (x : ι → H) :
    B.ksum (Function.extend ⇑e x 0) = B.bsum h x := by
  have h1 : B.ksum (Function.extend ⇑(e.trans B.row) x 0) = B.ksum (Function.extend ⇑e x 0) := by
    rw [B.extend_trans_row e x]; exact B.ksum_row _
  exact h1.symm.trans
    (B.ksum_extend_congr (e.trans B.row) ((emb h).trans B.row) (B.mk_compl_trans e)
      (B.mk_compl_trans (emb h)) x)

theorem bsum_unique {ι : Type u} [Unique ι] (h : #ι ≤ κ) (x : ι → H) : B.bsum h x = x default := by
  set E := (emb h).trans B.row with hE
  show B.ksum (Function.extend ⇑E x 0) = x default
  rw [B.ksum_single (E default) _ ?_, E.injective.extend_apply]
  intro j hj
  by_cases hjk : ∃ i, E i = j
  · obtain ⟨i, rfl⟩ := hjk
    exact absurd (congrArg E (Unique.eq_default i)) hj
  · exact Function.extend_apply' _ _ _ hjk

theorem bsum_congr {ι ι' : Type u} (h : #ι ≤ κ) (h' : #ι' ≤ κ) (e : ι ≃ ι') (x : ι' → H) :
    B.bsum h (x ∘ e) = B.bsum h' x := by
  set E' : ι' ↪ Idx κ := (emb h').trans B.row
  have hE : Function.extend ⇑(e.toEmbedding.trans E') (x ∘ e) 0 = Function.extend ⇑E' x 0 := by
    funext k
    by_cases hk : ∃ i', E' i' = k
    · obtain ⟨i', rfl⟩ := hk
      have hval : (e.toEmbedding.trans E') (e.symm i') = E' i' := by
        show E' (e (e.symm i')) = _
        rw [Equiv.apply_symm_apply]
      rw [E'.injective.extend_apply, ← hval,
        (e.toEmbedding.trans E').injective.extend_apply]
      show x (e (e.symm i')) = x i'
      rw [Equiv.apply_symm_apply]
    · have hnot : ¬ ∃ i, (e.toEmbedding.trans E') i = k := by
        rintro ⟨i, hi⟩
        exact hk ⟨e i, hi⟩
      rw [Function.extend_apply' _ _ _ hnot, Function.extend_apply' _ _ _ hk]
  rw [← B.ksum_extend_eq h (e.toEmbedding.trans E') (x ∘ e), hE]
  exact B.ksum_extend_eq h' E' x

theorem bsum_sigma {ι : Type u} {ρ : ι → Type u} (h : #ι ≤ κ) (hρ : ∀ i, #(ρ i) ≤ κ)
    (x : ∀ i, ρ i → H) (hσ : #((i : ι) × ρ i) ≤ κ) :
    B.bsum h (fun i => B.bsum (hρ i) (x i)) = B.bsum hσ (fun p => x p.1 p.2) := by
  set e : ι ↪ Idx κ := (emb h).trans B.row with hedef
  set f : ∀ i, ρ i ↪ Idx κ := fun i => (emb (hρ i)).trans B.row
  set π : Idx κ × Idx κ ≃ Idx κ := B.pair with hπdef
  set E : ((i : ι) × ρ i) ↪ Idx κ := ⟨fun p => π (e p.1, f p.1 p.2), by
    rintro ⟨i1, r1⟩ ⟨i2, r2⟩ hEq
    have hpair : (e i1, f i1 r1) = (e i2, f i2 r2) := π.injective hEq
    have hi : i1 = i2 := e.injective (Prod.ext_iff.mp hpair).1
    subst hi
    exact congrArg _ ((f i1).injective (Prod.ext_iff.mp hpair).2)⟩ with hEdef
  set W : ∀ _ : ι, Idx κ → H := fun i => Function.extend ⇑(f i) (x i) 0 with hWdef
  set G : Idx κ → (Idx κ → H) := Function.extend ⇑e W (fun _ => (0 : Idx κ → H)) with hGdef
  have hGa : ∀ a, B.ksum (G a) = Function.extend ⇑e (fun i => B.ksum (W i)) 0 a := by
    intro a
    by_cases ha : ∃ i, e i = a
    · obtain ⟨i, rfl⟩ := ha
      rw [hGdef, e.injective.extend_apply, e.injective.extend_apply]
    · rw [hGdef, Function.extend_apply' W (fun _ => (0 : Idx κ → H)) a ha,
        Function.extend_apply' (fun i => B.ksum (W i)) (0 : Idx κ → H) a ha]
      exact B.ksum_zero
  have hGk : ∀ k, G (π.symm k).1 (π.symm k).2 = Function.extend ⇑E (fun p => x p.1 p.2) 0 k := by
    intro k
    by_cases ha : ∃ i, e i = (π.symm k).1
    · obtain ⟨i, hi⟩ := ha
      have hGaeq : G (π.symm k).1 = W i := by rw [hGdef, ← hi, e.injective.extend_apply]
      rw [hGaeq]
      by_cases hb : ∃ r, f i r = (π.symm k).2
      · obtain ⟨r, hr⟩ := hb
        have hWeq : W i (π.symm k).2 = x i r := by
          rw [hWdef, ← hr]
          exact (f i).injective.extend_apply (x i) 0 r
        have hEk : E ⟨i, r⟩ = k := by
          show π (e i, f i r) = k
          rw [hi, hr]
          exact π.apply_symm_apply k
        rw [hWeq, ← hEk, E.injective.extend_apply]
      · show Function.extend ⇑(f i) (x i) 0 (π.symm k).2 = _
        rw [Function.extend_apply' (x i) (0 : Idx κ → H) (π.symm k).2 hb]
        symm
        apply Function.extend_apply'
        rintro ⟨⟨i', r'⟩, hp⟩
        have heqp : (e i', f i' r') = π.symm k := by
          rw [← hp]; exact (π.symm_apply_apply (e i', f i' r')).symm
        have hii : i' = i := e.injective ((congrArg Prod.fst heqp).trans hi.symm)
        subst hii
        exact hb ⟨r', congrArg Prod.snd heqp⟩
    · have hGaeq : G (π.symm k).1 = fun _ => (0 : H) := by
        rw [hGdef]
        exact Function.extend_apply' W (fun _ => (0 : Idx κ → H)) (π.symm k).1 ha
      rw [hGaeq]
      symm
      apply Function.extend_apply'
      rintro ⟨⟨i', r'⟩, hp⟩
      have heqp : (e i', f i' r') = π.symm k := by
        rw [← hp]; exact (π.symm_apply_apply (e i', f i' r')).symm
      exact ha ⟨i', congrArg Prod.fst heqp⟩
  calc B.bsum h (fun i => B.bsum (hρ i) (x i))
      = B.ksum (fun a => B.ksum (G a)) := by
        show B.ksum (Function.extend ⇑e (fun i => B.ksum (W i)) 0) = _
        congr 1
        funext a
        exact (hGa a).symm
    _ = B.ksum (fun k => G (π.symm k).1 (π.symm k).2) := B.ksum_sigma G π
    _ = B.ksum (Function.extend ⇑E (fun p => x p.1 p.2) 0) := by
        congr 1; funext k; exact hGk k
    _ = B.bsum hσ (fun p => x p.1 p.2) := B.ksum_extend_eq hσ E _

/-- The summation data determined by the bare data. -/
noncomputable def sumData : SumData (Order.succ κ) H where
  isRegular := Cardinal.isRegular_succ B.aleph0_le
  sum := fun h x => B.bsum (KMonoid.le_of_lt_succ h) x
  sum_congr := fun _ _ e x => B.bsum_congr _ _ e x
  sum_unique := fun _ x => B.bsum_unique _ x
  sum_sigma := fun _ hρ x hσ =>
    B.bsum_sigma _ (fun i => KMonoid.le_of_lt_succ (hρ i)) x (KMonoid.le_of_lt_succ hσ)

theorem sumData_zero : B.sumData.zero = 0 := by
  show B.bsum _ (PEmpty.elim : PEmpty.{u + 1} → H) = 0
  show B.ksum _ = 0
  have heq : Function.extend ⇑((emb (KMonoid.le_of_lt_succ (B.sumData.small PEmpty.{u + 1})))
      |>.trans B.row) (PEmpty.elim : PEmpty.{u + 1} → H) (0 : Idx κ → H) = fun _ => 0 := by
    funext k
    exact Function.extend_apply' _ _ _ (by rintro ⟨p, _⟩; exact p.elim)
  rw [heq]
  exact B.ksum_zero

end BareKMonoid

/-- **Lemma 2.5**: a `κ`-monoid is determined by its `κ`-indexed summation. -/
@[instance_reducible]
noncomputable def KMonoid.ofBare {κ : Cardinal.{u}} {H : Type v} [Zero H]
    (B : BareKMonoid κ H) : KMonoid κ H :=
  { toLMonoid := B.sumData.toLMonoidOfZero B.sumData_zero
    aleph0_le := B.aleph0_le }

@[simp] theorem KMonoid.ofBare_ksum {κ : Cardinal.{u}} {H : Type v} [Zero H]
    (B : BareKMonoid κ H) (x : Idx κ → H) :
    letI := KMonoid.ofBare B
    ksum (κ := κ) x = B.ksum x := by
  show B.bsum (le_of_eq (mk_Idx κ)) x = B.ksum x
  rw [← B.ksum_extend_eq (le_of_eq (mk_Idx κ)) (Function.Embedding.refl (Idx κ)) x]
  congr 1
  funext k
  exact (Function.Embedding.refl (Idx κ)).injective.extend_apply x 0 k

/-- A `κ`-monoid structure from `κ`-indexed data on a type that already carries a compatible
commutative monoid structure. -/
@[instance_reducible]
noncomputable def KMonoid.ofKsum {κ : Cardinal.{u}} {H : Type v} [AddCommMonoid H]
    (B : BareKMonoid κ H)
    (two : ∀ (a b : H) (i₀ i₁ : Idx κ), i₀ ≠ i₁ →
      B.ksum (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b) :
    KMonoid κ H := by
  classical
  refine { toLMonoid := B.sumData.toLMonoid' ?_, aleph0_le := B.aleph0_le }
  intro h a b
  set E : (PUnit.{u + 1} ⊕ PUnit.{u + 1}) ↪ Idx κ :=
    (emb (KMonoid.le_of_lt_succ h)).trans B.row with hEdef
  have hne : E (Sum.inl PUnit.unit) ≠ E (Sum.inr PUnit.unit) := by
    intro hh
    exact Sum.inl_ne_inr (E.injective hh)
  have hfun : Function.extend ⇑E (Sum.elim (fun _ => a) (fun _ => b)) 0
      = fun i => if i = E (Sum.inl PUnit.unit) then a
        else if i = E (Sum.inr PUnit.unit) then b else 0 := by
    funext k
    by_cases hk : ∃ p, E p = k
    · obtain ⟨p, rfl⟩ := hk
      rcases p with ⟨⟩ | ⟨⟩
      · rw [E.injective.extend_apply, if_pos rfl]
        rfl
      · rw [E.injective.extend_apply, if_neg (fun hh => hne hh.symm), if_pos rfl]
        rfl
    · rw [Function.extend_apply' _ _ _ hk,
        if_neg (fun hh => hk ⟨Sum.inl PUnit.unit, hh.symm⟩),
        if_neg (fun hh => hk ⟨Sum.inr PUnit.unit, hh.symm⟩)]
      rfl
  show a + b = B.ksum (Function.extend ⇑E (Sum.elim (fun _ => a) (fun _ => b)) 0)
  rw [hfun, two a b _ _ hne]

@[simp] theorem KMonoid.ofKsum_ksum {κ : Cardinal.{u}} {H : Type v} [AddCommMonoid H]
    (B : BareKMonoid κ H) (two : ∀ (a b : H) (i₀ i₁ : Idx κ), i₀ ≠ i₁ →
      B.ksum (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b)
    (x : Idx κ → H) :
    letI := KMonoid.ofKsum B two
    ksum (κ := κ) x = B.ksum x := by
  show B.bsum (le_of_eq (mk_Idx κ)) x = B.ksum x
  rw [← B.ksum_extend_eq (le_of_eq (mk_Idx κ)) (Function.Embedding.refl (Idx κ)) x]
  congr 1
  funext k
  exact (Function.Embedding.refl (Idx κ)).injective.extend_apply x 0 k

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
  lsumOf := fun _ x => ∑ᶠ i, x i
  lsumOf_congr := fun _ _ e x => finsum_comp_equiv e
  lsumOf_unique := fun _ x =>
    finsum_eq_single x default fun b hb => absurd (Unique.eq_default b) hb
  lsumOf_sigma := fun {ι ρ} h hρ x hσ => by
    have : Finite ι := mk_lt_aleph0_iff_finite.mp h
    have : ∀ i, Finite (ρ i) := fun i => mk_lt_aleph0_iff_finite.mp (hρ i)
    have : Finite ((i : ι) × ρ i) := mk_lt_aleph0_iff_finite.mp hσ
    let _ : Fintype ι := Fintype.ofFinite ι
    let _ : ∀ i, Fintype (ρ i) := fun i => Fintype.ofFinite (ρ i)
    rw [finsum_eq_sum_of_fintype]
    rw [show (fun i => ∑ᶠ j, x i j) = fun i => ∑ j, x i j from
      funext fun i => finsum_eq_sum_of_fintype _]
    rw [finsum_eq_sum_of_fintype, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  add_eq_lsumOf := fun _ a b => by
    rw [finsum_eq_sum_of_fintype, Fintype.sum_sum_type]
    simp

/-- For `λ = ℵ₀` the summation of any `λ⁻`-monoid structure is the ordinary finite sum. -/
theorem lsumOf_aleph0_eq_finsum {ι : Type u} [Fintype ι] (h : #ι < ℵ₀) {X : Type v}
    [LMonoid ℵ₀ X] (x : ι → X) : lsumOf (lam := ℵ₀) h x = ∑ i, x i := by
  revert h x
  refine Fintype.induction_empty_option
    (P := fun (ι : Type u) [Fintype ι] =>
      ∀ (h : #ι < ℵ₀) (x : ι → X), lsumOf (lam := ℵ₀) h x = ∑ i, x i) ?_ ?_ ?_ ι
  · intro α β _ e ih h x
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    have hα : #α < ℵ₀ := by rw [Cardinal.mk_congr e]; exact h
    rw [lsumOf_equiv h hα e x, ih hα (x ∘ e)]
    exact Equiv.sum_comp e x
  · intro h x
    simp
  · intro α _ ih h x
    have hα : #α < ℵ₀ := lt_of_le_of_lt (Cardinal.mk_le_of_injective (Option.some_injective α)) h
    have hu : #PUnit.{u + 1} < ℵ₀ := mk_lt_finite (X := X) _
    have hsum : #(α ⊕ PUnit.{u + 1}) < ℵ₀ := mk_sum_lt (isRegular' (X := X)) hα hu
    rw [lsumOf_equiv h hsum (Equiv.optionEquivSumPUnit α).symm x,
      show x ∘ (Equiv.optionEquivSumPUnit α).symm
        = Sum.elim (fun a => x (some a)) (fun _ => x none) by
        funext p; rcases p with p | p <;> rfl,
      lsumOf_sumType hα hu hsum, ih hα (fun a => x (some a)), lsumOf_unique,
      Fintype.sum_option]
    exact add_comm _ _

/-- For `λ = ℵ₀`, a sum over a small subset is the `finsum` over that subset. -/
theorem lsumOf_eq_finsum {X : Type v} [LMonoid ℵ₀ X] {ι : Type u} {S : Set ι} (h : #S < ℵ₀)
    (f : ι → X) : lsumOf (lam := ℵ₀) h (fun i : S => f i) = ∑ᶠ i ∈ S, f i := by
  have hfin : S.Finite := Cardinal.lt_aleph0_iff_set_finite.mp h
  let _ : Fintype S := hfin.fintype
  rw [lsumOf_aleph0_eq_finsum h (fun i : S => f i), ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem]

end LMonoid

/-! ## The reducedness of `λ⁻`-monoids that embed into `κ`-monoids

This is the observation behind the hypothesis that has to be added to Theorem 3.11. -/

namespace LMonoid

/-- A `λ⁻`-homomorphism from a `λ⁻`-monoid into (the underlying `λ⁻`-monoid of) a
`κ`-monoid. -/
def IsLHom {lam κ : Cardinal.{u}} {X : Type v} {H : Type w} [LMonoid lam X] [KMonoid κ H]
    (hκ : lam ≤ κ) (f : X → H) : Prop :=
  f 0 = 0 ∧ ∀ {ι : Type u} (h : #ι < lam) (x : ι → X),
    f (lsumOf (lam := lam) h x) = KMonoid.sumOf (κ := κ) (h.le.trans hκ) (f ∘ x)

variable {lam κ : Cardinal.{u}} {X : Type v} {H : Type w} [LMonoid lam X] [KMonoid κ H]

/-- If a `λ⁻`-monoid `X` admits an injective additive map into a `κ`-monoid, then `X` is
reduced.  Since Theorem 3.11 asserts the existence of a `κ`-monoid `Ĥ ⊇ H`, this shows that
reducedness of `H` is a *necessary* hypothesis there. -/
theorem isConical_of_injective (f : X → H) (hf : Function.Injective f) (h0 : f 0 = 0)
    (hadd : ∀ a b, f (a + b) = f a + f b) : IsConical X := by
  intro a b hab
  have h : f a + f b = 0 := by rw [← hadd, hab, h0]
  obtain ⟨ha, hb⟩ := KMonoid.isConical κ H (f a) (f b) h
  exact ⟨hf (by rw [ha, h0]), hf (by rw [hb, h0])⟩

end LMonoid

end KappaMonoid
