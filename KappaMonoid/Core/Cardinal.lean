/-
Cardinal summation, and **Examples 2.3(3)**: `F_{λ⁻}` and `F_κ`, the cardinals below a bound.
A construction rather than an example — the free `λ⁻`-monoid of §2.1 is built out of it.
-/
import KappaMonoid.Core

universe u v

open Cardinal Function Set
open scoped Classical

namespace KappaMonoid

/-! ## Cardinal summation

Three facts about `Cardinal.sum` matching the three axioms of `SumData`.  `Cardinal.sum f` is by
definition `#(Σ i, (f i).out)`, so each is an isomorphism of sigma types. -/

/-- Cardinal summation is invariant under reindexing. -/
theorem csum_congr {ι ι' : Type u} (e : ι ≃ ι') (f : ι' → Cardinal.{u}) :
    Cardinal.sum (f ∘ e) = Cardinal.sum f :=
  Cardinal.mk_sigma_congr e fun _ => rfl

/-- A cardinal sum over a one-point index type is its unique entry. -/
theorem csum_unique {ι : Type u} [Unique ι] (f : ι → Cardinal.{u}) :
    Cardinal.sum f = f default := by
  rw [show f = (fun _ : ι => f default) from funext fun i => by rw [Unique.eq_default i],
    Cardinal.sum_const' ι (f default), Cardinal.mk_eq_one ι, one_mul]

/-- Cardinal summation is associative over sigma types. -/
theorem csum_sigma {ι : Type u} {ρ : ι → Type u} (x : ∀ i, ρ i → Cardinal.{u}) :
    Cardinal.sum (fun i => Cardinal.sum (x i)) = Cardinal.sum fun p : (i : ι) × ρ i => x p.1 p.2 := by
  have hrow : ∀ i, #((Cardinal.sum (x i)).out) = #((j : ρ i) × (x i j).out) := by
    intro i
    rw [Cardinal.mk_out, Cardinal.mk_sigma]
    exact congrArg _ (funext fun j => (Cardinal.mk_out _).symm)
  calc Cardinal.sum (fun i => Cardinal.sum (x i))
      = #((i : ι) × (j : ρ i) × (x i j).out) := Cardinal.mk_sigma_congrRight hrow
    _ = Cardinal.sum fun p : (i : ι) × ρ i => x p.1 p.2 :=
        Cardinal.mk_congr (Equiv.sigmaAssoc (fun (i : ι) (j : ρ i) => (x i j).out)).symm

/-- A cardinal sum over a two-point index type is a sum of cardinals. -/
theorem csum_pair (α β : Cardinal.{u}) :
    Cardinal.sum (Sum.elim (fun _ : PUnit.{u + 1} => α) (fun _ : PUnit.{u + 1} => β)) = α + β := by
  have h1 : Cardinal.sum (Sum.elim (fun _ : PUnit.{u + 1} => α) (fun _ : PUnit.{u + 1} => β))
      = #((_ : PUnit.{u + 1}) × α.out ⊕ (_ : PUnit.{u + 1}) × β.out) :=
    Cardinal.mk_congr (Equiv.sumSigmaDistrib _)
  rw [h1, Cardinal.mk_sum, Cardinal.mk_sigma, Cardinal.mk_sigma, csum_unique, csum_unique,
    Cardinal.mk_out, Cardinal.mk_out, Cardinal.lift_id, Cardinal.lift_id]

/-- An empty cardinal sum is `0`. -/
theorem csum_isEmpty {ι : Type u} [IsEmpty ι] (f : ι → Cardinal.{u}) : Cardinal.sum f = 0 := by
  have : IsEmpty ((i : ι) × (f i).out) := ⟨fun q => IsEmpty.false q.1⟩
  exact Cardinal.mk_eq_zero _

/-- A `≤ κ`-indexed sum of cardinals `≤ κ` is `≤ κ`. -/
theorem csum_le_of_le {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) {ι : Type u} (hι : #ι ≤ κ)
    {f : ι → Cardinal.{u}} (hf : ∀ i, f i ≤ κ) : Cardinal.sum f ≤ κ :=
  calc Cardinal.sum f ≤ Cardinal.sum (fun _ : ι => κ) := Cardinal.sum_le_sum _ _ hf
    _ = #ι * κ := Cardinal.sum_const' ι κ
    _ ≤ κ * κ := mul_le_mul' hι le_rfl
    _ = κ := Cardinal.mul_eq_self hκ

/-! ## Examples 2.3(3) and its `λ⁻` analogue: the cardinals below a bound

Examples 2.3(3) is the `κ`-monoid `F_κ` of cardinals `≤ κ`; §2.4 uses the same construction for
the `λ⁻`-monoid `F_{λ⁻}` of cardinals `< λ`.  Since `α ≤ κ ↔ α < κ⁺`, these are one type, and
`Fcard κ` is by definition `LCard κ⁺`. -/

/-- `F_{λ⁻}`, the `λ⁻`-monoid of all cardinals `< λ`. -/
abbrev LCard (lam : Cardinal.{u}) : Type (u + 1) := {α : Cardinal.{u} // α < lam}

/-- `F_κ`, the `κ`-monoid of all cardinals `≤ κ` (Examples 2.3(3)). -/
abbrev Fcard (κ : Cardinal.{u}) : Type (u + 1) := LCard (Order.succ κ)

namespace LCard

variable {lam : Cardinal.{u}}

theorem ext {a b : LCard lam} (h : (a : Cardinal.{u}) = b) : a = b := Subtype.ext h

/-- The summation data on `F_{λ⁻}`: cardinal summation, which stays `< λ` by regularity. -/
noncomputable def sumData (hlam : lam.IsRegular) : SumData lam (LCard lam) where
  isRegular := hlam
  sum {_ι} h x :=
    ⟨Cardinal.sum fun i => (x i : Cardinal.{u}),
      Cardinal.sum_lt_of_isRegular hlam h fun i => (x i).2⟩
  sum_congr _ _ e x := ext (csum_congr e fun i => (x i : Cardinal.{u}))
  sum_unique _ x := ext (csum_unique fun i => (x i : Cardinal.{u}))
  sum_sigma _ _ x _ := ext (csum_sigma fun i j => (x i j : Cardinal.{u}))

/-- The cardinals `< λ` form a `λ⁻`-monoid (the free `λ⁻`-monoid on one generator, §2.4).
Its neutral element is the cardinal `0` and its addition is addition of cardinals; both are
*derived* from `Σ` by Lemma 2.5, see `val_zero` and `val_add`. -/
@[instance_reducible]
noncomputable def instLMonoid (hlam : lam.IsRegular) : LMonoid lam (LCard lam) :=
  (sumData hlam).toLMonoid

/-- The `λ⁻`-sum on `F_{λ⁻}` is cardinal summation. -/
@[simp] theorem val_lsumOf (hlam : lam.IsRegular) {ι : Type u} (h : #ι < lam) (x : ι → LCard lam) :
    letI := instLMonoid hlam
    ((LMonoid.lsumOf (lam := lam) h x : LCard lam) : Cardinal.{u})
      = Cardinal.sum fun i => (x i : Cardinal.{u}) := rfl

/-- The neutral element of `F_{λ⁻}` is the cardinal `0`. -/
@[simp] theorem val_zero (hlam : lam.IsRegular) :
    letI := instLMonoid hlam
    ((0 : LCard lam) : Cardinal.{u}) = 0 := csum_isEmpty _

/-- Cardinal scalar multiplication in `F_{λ⁻}` is multiplication of cardinals. -/
theorem val_lcmul (hlam : lam.IsRegular) (α : Cardinal.{u}) (hα : α < lam) (c : LCard lam) :
    letI := instLMonoid hlam
    ((LMonoid.lcmul (lam := lam) α hα c : LCard lam) : Cardinal.{u})
      = α * (c : Cardinal.{u}) := by
  let := instLMonoid hlam
  show (Cardinal.sum fun _ : Idx α => ((c : LCard lam) : Cardinal.{u})) = _
  rw [Cardinal.sum_const', mk_Idx]

/-- Addition in `F_{λ⁻}` is addition of cardinals. -/
theorem val_add (hlam : lam.IsRegular) (a b : LCard lam) :
    letI := instLMonoid hlam
    ((a + b : LCard lam) : Cardinal.{u}) = (a : Cardinal.{u}) + b := by
  let := instLMonoid hlam
  show Cardinal.sum (fun p : PUnit.{u + 1} ⊕ PUnit.{u + 1} =>
      ((Sum.elim (fun _ => a) (fun _ => b) p : LCard lam) : Cardinal.{u})) = _
  rw [show (fun p : PUnit.{u + 1} ⊕ PUnit.{u + 1} =>
        ((Sum.elim (fun _ => a) (fun _ => b) p : LCard lam) : Cardinal.{u}))
      = Sum.elim (fun _ => (a : Cardinal.{u})) (fun _ => (b : Cardinal.{u})) from
    funext fun p => by rcases p with p | p <;> rfl]
  exact csum_pair _ _

end LCard

namespace Fcard

variable {κ : Cardinal.{u}}

/-- The elements of `F_κ` are the cardinals `≤ κ`, as in the paper. -/
theorem lt_iff_le {α : Cardinal.{u}} : α < Order.succ κ ↔ α ≤ κ := Order.lt_succ_iff

/-- The element of `F_κ` given by a cardinal `α ≤ κ`. -/
def mk (α : Cardinal.{u}) (h : α ≤ κ) : Fcard κ := ⟨α, lt_iff_le.mpr h⟩

@[simp] theorem val_mk (α : Cardinal.{u}) (h : α ≤ κ) : ((mk α h : Fcard κ) : Cardinal.{u}) = α :=
  rfl

theorem le (a : Fcard κ) : (a : Cardinal.{u}) ≤ κ := lt_iff_le.mp a.2

theorem ext {a b : Fcard κ} (h : (a : Cardinal.{u}) = b) : a = b := Subtype.ext h

/-- **Examples 2.3(3)**: the cardinals `≤ κ` form a `κ`-monoid. -/
@[instance_reducible]
noncomputable def instKMonoid (hκ : ℵ₀ ≤ κ) : KMonoid κ (Fcard κ) where
  toLMonoid := LCard.instLMonoid (Cardinal.isRegular_succ hκ)
  aleph0_le := hκ

/-- `F_{ℵ₀}` is an `ℵ₀`-monoid: `instKMonoid` at the distinguished cardinal, promoted to an
instance because it recurs in every statement about `F_{ℵ₀}`.  The hypothesis it takes is a
`Prop`, so this is definitionally the structure any `letI := instKMonoid h` would produce. -/
noncomputable instance instKMonoidAleph0 :
    KMonoid (ℵ₀ : Cardinal.{u}) (Fcard (ℵ₀ : Cardinal.{u})) := instKMonoid le_rfl

/-- The `κ`-sum on `F_κ` is cardinal summation. -/
@[simp] theorem instKMonoid_sumOf (hκ : ℵ₀ ≤ κ) {ι : Type u} (h : #ι ≤ κ) (x : ι → Fcard κ) :
    letI := instKMonoid hκ
    ((KMonoid.sumOf (κ := κ) h x : Fcard κ) : Cardinal.{u})
      = Cardinal.sum fun i => (x i : Cardinal.{u}) := rfl

/-- The neutral element of `F_κ` is the cardinal `0`. -/
@[simp] theorem instKMonoid_zero (hκ : ℵ₀ ≤ κ) :
    letI := instKMonoid hκ
    ((0 : Fcard κ) : Cardinal.{u}) = 0 := LCard.val_zero _

/-- Addition on `F_κ` is addition of cardinals. -/
theorem instKMonoid_add (hκ : ℵ₀ ≤ κ) (a b : Fcard κ) :
    letI := instKMonoid hκ
    ((a + b : Fcard κ) : Cardinal.{u}) = (a : Cardinal.{u}) + b :=
  LCard.val_add _ a b

end Fcard

end KappaMonoid
