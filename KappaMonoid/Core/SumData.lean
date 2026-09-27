/-
`SumData` — summation alone, with no `0` and no `+` — the classes `LMonoid` (Definition 2.18)
and the additive structure it induces (the bullets after **Lemma 2.5**), and conicality.
-/
import KappaMonoid.Core.Index

universe u v w

open Cardinal Function Set

namespace KappaMonoid

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

/-- Reindexing along `e`, with the two families compared pointwise. -/
theorem sum_equiv {ι ι' : Type u} (h : #ι < lam) (h' : #ι' < lam) (e : ι ≃ ι') {x : ι → X}
    {y : ι' → X} (hxy : ∀ i, x i = y (e i)) : S.sum h x = S.sum h' y :=
  (congrArg (S.sum h) (funext hxy)).trans (S.sum_congr h h' e y)

/-- A sum over `α ⊕ β` is the binary sum of the two partial sums: the bridge between `sum` and
`add`.  The two halves of `α ⊕ β` are the fibres of a family over `PUnit ⊕ PUnit`, the index
type of `add`, so this is (B2). -/
theorem sum_sumType {α β : Type u} (hα : #α < lam) (hβ : #β < lam) (hαβ : #(α ⊕ β) < lam)
    (f : α → X) (g : β → X) :
    S.sum hαβ (Sum.elim f g) = S.add (S.sum hα f) (S.sum hβ g) := by
  let ρ : PUnit.{u + 1} ⊕ PUnit.{u + 1} → Type u := Sum.elim (fun _ => α) (fun _ => β)
  let y : ∀ p, ρ p → X := Sum.rec (fun _ => f) (fun _ => g)
  have hρ : ∀ p, #(ρ p) < lam := Sum.rec (fun _ => hα) (fun _ => hβ)
  have h2 := S.hsum (S.small PUnit.{u + 1}) (S.small PUnit.{u + 1})
  calc S.sum hαβ (Sum.elim f g)
      = S.sum (mk_sigma_lt S.isRegular h2 hρ) (fun q => y q.1 q.2) :=
        S.sum_equiv _ _ (sumEquivSigma α β) (by rintro (_ | _) <;> rfl)
    _ = S.sum h2 (fun p => S.sum (hρ p) (y p)) := (S.sum_sigma h2 hρ y _).symm
    _ = S.add (S.sum hα f) (S.sum hβ g) := S.sum_equiv _ _ (Equiv.refl _) (by rintro (_ | _) <;> rfl)

/-! Lemma 2.5: `add` is a commutative monoid operation with neutral element `zero`.  Each law is
`sum_sumType` together with one reindexing of the three-point (or one-point) index type. -/

theorem add_comm' (a b : X) : S.add a b = S.add b a :=
  S.sum_equiv _ _ (Equiv.sumComm _ _) (by rintro (_ | _) <;> rfl)

theorem add_assoc' (a b c : X) : S.add (S.add a b) c = S.add a (S.add b c) := by
  have hu := S.small PUnit.{u + 1}
  calc S.add (S.add a b) c
      = S.sum (S.hsum (S.hsum hu hu) hu)
          (Sum.elim (Sum.elim (fun _ => a) (fun _ => b)) fun _ => c) := by
        rw [S.sum_sumType (S.hsum hu hu) hu, S.sum_punit]; rfl
    _ = S.sum (S.hsum hu (S.hsum hu hu))
          (Sum.elim (fun _ => a) (Sum.elim (fun _ => b) fun _ => c)) :=
        S.sum_equiv _ _ (Equiv.sumAssoc _ _ _) (by rintro ((_ | _) | _) <;> rfl)
    _ = S.add a (S.add b c) := by rw [S.sum_sumType hu (S.hsum hu hu), S.sum_punit]; rfl

theorem zero_add' (a : X) : S.add S.zero a = a := by
  have hu := S.small PUnit.{u + 1}
  have he := S.small PEmpty.{u + 1}
  calc S.add S.zero a
      = S.sum (S.hsum he hu) (Sum.elim PEmpty.elim fun _ => a) := by
        rw [S.sum_sumType he hu, S.sum_punit]; rfl
    _ = S.sum hu (fun _ => a) := S.sum_equiv _ _ (Equiv.emptySum _ _) (by rintro (e | _); exacts [e.elim, rfl])
    _ = a := S.sum_punit a

/-- The commutative monoid determined by the summation, on a type that already carries the neutral
element `0 = Σ ∅`. -/
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

/-- The commutative monoid determined by the summation — the second bullet after **Lemma 2.5**:
`(H, Σ²)` is a commutative monoid. -/
@[instance_reducible]
noncomputable def addCommMonoid : AddCommMonoid X :=
  letI : Zero X := ⟨S.zero⟩
  S.addCommMonoidOfZero rfl

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

/-- The `λ⁻`-monoid determined by bare summation data (Lemma 2.5). -/
@[instance_reducible]
noncomputable def toLMonoid : LMonoid lam X :=
  letI := S.addCommMonoid
  S.toLMonoid' fun _ _ _ => rfl

/-- Variant of `toLMonoid` for a type that already carries the neutral element. -/
@[instance_reducible]
noncomputable def toLMonoidOfZero [Zero X] (h0 : S.zero = 0) : LMonoid lam X :=
  letI := S.addCommMonoidOfZero h0
  S.toLMonoid' fun _ _ _ => rfl

end SumData

/-! ## Reducedness -/

/-- A commutative monoid is *reduced* (or *conical*) if `a + b = 0` forces `a = b = 0`. -/
def IsConical (X : Type v) [AddCommMonoid X] : Prop :=
  ∀ a b : X, a + b = 0 → a = 0 ∧ b = 0

/-- A cardinal sum over a two-point index type. -/
theorem csum_pair' (α β : Cardinal.{u}) :
    Cardinal.sum (Sum.elim (fun _ : PUnit.{u + 1} => α) fun _ : PUnit.{u + 1} => β) = α + β := by
  have hone : ∀ γ : Cardinal.{u}, (Cardinal.sum fun _ : PUnit.{u + 1} => #γ.out) = γ := fun γ => by
    rw [Cardinal.sum_const', Cardinal.mk_eq_one PUnit.{u + 1}, one_mul, Cardinal.mk_out]
  have h1 : Cardinal.sum (Sum.elim (fun _ : PUnit.{u + 1} => α) fun _ : PUnit.{u + 1} => β)
      = #((_ : PUnit.{u + 1}) × α.out ⊕ (_ : PUnit.{u + 1}) × β.out) :=
    Cardinal.mk_congr (Equiv.sumSigmaDistrib _)
  rw [h1, Cardinal.mk_sum, Cardinal.mk_sigma, Cardinal.mk_sigma, hone, hone,
    Cardinal.lift_id, Cardinal.lift_id]

end KappaMonoid
