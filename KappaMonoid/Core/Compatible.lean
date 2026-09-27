/-
**Remark 2.19**, second half: a compatible family of `λ`-monoid structures, one for every infinite
`λ < κ`, assembles into a `κ⁻`-monoid structure; conversely every `κ⁻`-monoid restricts to such a
family (the direction `LMonoid.ofLE`), and the two constructions are mutually inverse.
-/
import Mathlib.Algebra.Group.Ext
import KappaMonoid.Core.KMonoid

universe u v

open Cardinal

namespace KappaMonoid

/-! ### Extensionality

A `λ⁻`-monoid structure is determined by its addition and its summation: `0` and `nsmul` are
determined by `+` (`AddCommMonoid.ext`), and the remaining fields are propositions. -/

/-- Two `λ⁻`-monoid structures with the same addition and the same sums coincide. -/
theorem LMonoid.ext_of_lsumOf {lam : Cardinal.{u}} {X : Type v} {A B : LMonoid lam X}
    (hadd : (letI := A; HAdd.hAdd : X → X → X) = (letI := B; HAdd.hAdd : X → X → X))
    (hsum : ∀ {ι : Type u} (h : #ι < lam) (x : ι → X),
      @LMonoid.lsumOf lam X A ι h x = @LMonoid.lsumOf lam X B ι h x) : A = B := by
  obtain @⟨acmA, @⟨regA, sA, _, _, _⟩, _⟩ := A
  obtain @⟨acmB, @⟨regB, sB, _, _, _⟩, _⟩ := B
  obtain rfl : acmA = acmB := AddCommMonoid.ext hadd
  obtain rfl : @sA = @sB := by
    funext ι h x
    exact hsum h x
  rfl

/-- Two `κ`-monoid structures with the same addition and the same sums coincide. -/
theorem KMonoid.ext_of_sumOf {κ : Cardinal.{u}} {H : Type v} {A B : KMonoid κ H}
    (hadd : (letI := A; HAdd.hAdd : H → H → H) = (letI := B; HAdd.hAdd : H → H → H))
    (hsum : ∀ {ι : Type u} (h : #ι ≤ κ) (x : ι → H),
      (letI := A; ∑[≤ κ] i, x i) = (letI := B; ∑[≤ κ] i, x i)) : A = B := by
  obtain @⟨LA, _⟩ := A
  obtain @⟨LB, _⟩ := B
  obtain rfl : LA = LB :=
    LMonoid.ext_of_lsumOf hadd fun h x => hsum (KMonoid.le_of_lt_succ h) x
  rfl

namespace LMonoid

variable {κ : Cardinal.{u}} {H : Type v}

/-! ### Compatible families -/

/-- **Remark 2.19**: a family of `λ`-monoid structures on `H`, one for every infinite `λ < κ`, is
*compatible* if a family indexed by at most `λ₁` elements has the same sum in the `λ₁`- and in the
`λ₂`-structure whenever `λ₁ ≤ λ₂`.  This is "compatible in the natural way" of the paper. -/
def IsCompatible (κ : Cardinal.{u}) {H : Type v}
    (S : ∀ lam : Cardinal.{u}, ℵ₀ ≤ lam → lam < κ → KMonoid lam H) : Prop :=
  ∀ (lam₁ lam₂ : Cardinal.{u}) (h₁ : ℵ₀ ≤ lam₁) (h₁' : lam₁ < κ) (h₂ : ℵ₀ ≤ lam₂)
    (h₂' : lam₂ < κ) (hle : lam₁ ≤ lam₂) {ι : Type u} (hι : #ι ≤ lam₁) (x : ι → H),
    (letI := S lam₁ h₁ h₁'; ∑[≤ lam₁] i, x i) = (letI := S lam₂ h₂ h₂'; ∑[≤ lam₂] i, x i)

variable {S : ∀ lam : Cardinal.{u}, ℵ₀ ≤ lam → lam < κ → KMonoid lam H}

/-- In a compatible family, a family has the same sum in *any* two structures in which it can be
summed, comparable or not: compare both with the structure at `max λ λ'`. -/
theorem IsCompatible.sumOf_eq (hS : IsCompatible κ S) {lam lam' : Cardinal.{u}} (h0 : ℵ₀ ≤ lam)
    (hl : lam < κ) (h0' : ℵ₀ ≤ lam') (hl' : lam' < κ) {ι : Type u} (hι : #ι ≤ lam)
    (hι' : #ι ≤ lam') (x : ι → H) :
    (letI := S lam h0 hl; ∑[≤ lam] i, x i) = (letI := S lam' h0' hl'; ∑[≤ lam'] i, x i) :=
  (hS lam (max lam lam') h0 hl (le_max_of_le_left h0) (max_lt hl hl') (le_max_left _ _) hι x).trans
    (hS lam' (max lam lam') h0' hl' (le_max_of_le_left h0) (max_lt hl hl') (le_max_right _ _)
      hι' x).symm

/-- In a compatible family all the additions agree: `a + b` is the sum of a two-element family,
which by compatibility is the same in every structure. -/
theorem IsCompatible.add_eq (hS : IsCompatible κ S) {lam lam' : Cardinal.{u}} (h0 : ℵ₀ ≤ lam)
    (hl : lam < κ) (h0' : ℵ₀ ≤ lam') (hl' : lam' < κ) (a b : H) :
    (letI := S lam h0 hl; a + b) = (letI := S lam' h0' hl'; a + b) := by
  have hB : #(ULift.{u} Bool) ≤ ℵ₀ := (lt_aleph0_of_finite _).le
  exact (@KMonoid.sumOf_two lam H (S lam h0 hl) a b).symm.trans
    ((hS.sumOf_eq h0 hl h0' hl' (hB.trans h0) (hB.trans h0') _).trans
      (@KMonoid.sumOf_two lam' H (S lam' h0' hl') a b))

/-- The sum of a `< κ`-indexed family in a compatible family of structures: computed in the
structure at `max #ι ℵ₀`, the least infinite cardinal at which it can be summed. -/
noncomputable def compatSum (S : ∀ lam : Cardinal.{u}, ℵ₀ ≤ lam → lam < κ → KMonoid lam H)
    (hκ0 : ℵ₀ < κ) {ι : Type u} (h : #ι < κ) (x : ι → H) : H :=
  letI := S _ (le_max_right _ _) (max_lt h hκ0)
  LMonoid.lsumOf (lam := Order.succ (max #ι ℵ₀)) (KMonoid.lt_succ (le_max_left _ _)) x

/-- `compatSum` agrees with the sum in any structure of the family that can compute it. -/
theorem IsCompatible.compatSum_eq (hS : IsCompatible κ S) (hκ0 : ℵ₀ < κ) {lam : Cardinal.{u}}
    (h0 : ℵ₀ ≤ lam) (hl : lam < κ) {ι : Type u} (hι : #ι ≤ lam) (h : #ι < κ) (x : ι → H) :
    compatSum S hκ0 h x = (letI := S lam h0 hl; ∑[≤ lam] i, x i) :=
  hS.sumOf_eq _ _ h0 hl (le_max_left _ _) hι x

theorem IsCompatible.compatSum_congr (hS : IsCompatible κ S) (hκ0 : ℵ₀ < κ) {ι ι' : Type u}
    (h : #ι < κ) (h' : #ι' < κ) (e : ι ≃ ι') (x : ι' → H) :
    compatSum S hκ0 h (x ∘ e) = compatSum S hκ0 h' x := by
  have hι : #ι ≤ max #ι' ℵ₀ := (mk_congr e).le.trans (le_max_left _ _)
  rw [hS.compatSum_eq hκ0 (le_max_right _ _) (max_lt h' hκ0) hι]
  exact (@KMonoid.sumOf_equiv _ H (S _ (le_max_right _ _) (max_lt h' hκ0)) ι' ι
    (CardLE.mk' (le_max_left _ _)) (CardLE.mk' hι) e x).symm

theorem compatSum_unique (hκ0 : ℵ₀ < κ) {ι : Type u} [Unique ι] (h : #ι < κ) (x : ι → H) :
    compatSum S hκ0 h x = x default :=
  @KMonoid.sumOf_unique _ H (S _ _ _) ι _ (CardLE.mk' (le_max_left _ _)) x

/-- (B2) for `compatSum`.  All sums involved can be computed in the single structure at
`λ' = max (max #ι #(Σ i, ρ i)) ℵ₀ < κ`, where the sigma law of that structure applies. -/
theorem IsCompatible.compatSum_sigma (hS : IsCompatible κ S) (hκ0 : ℵ₀ < κ) {ι : Type u}
    {ρ : ι → Type u} (h : #ι < κ) (hρ : ∀ i, #(ρ i) < κ) (x : ∀ i, ρ i → H)
    (hσ : #((i : ι) × ρ i) < κ) :
    compatSum S hκ0 h (fun i => compatSum S hκ0 (hρ i) (x i))
      = compatSum S hκ0 hσ (fun p => x p.1 p.2) := by
  obtain ⟨L, hL0, hLκ, hιL, hσL⟩ :
      ∃ L, ℵ₀ ≤ L ∧ L < κ ∧ #ι ≤ L ∧ #((i : ι) × ρ i) ≤ L :=
    ⟨max (max #ι #((i : ι) × ρ i)) ℵ₀, le_max_right _ _, max_lt (max_lt h hσ) hκ0,
      (le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _)⟩
  have hρL : ∀ i, #(ρ i) ≤ L := fun i =>
    (mk_le_of_injective (f := Sigma.mk (β := ρ) i) sigma_mk_injective).trans hσL
  rw [hS.compatSum_eq hκ0 hL0 hLκ hιL, hS.compatSum_eq hκ0 hL0 hLκ hσL,
    show (fun i => compatSum S hκ0 (hρ i) (x i))
        = fun i => (letI := S L hL0 hLκ
          lsumOf (lam := Order.succ L) (KMonoid.lt_succ (hρL i)) (x i)) from
      funext fun i => hS.compatSum_eq hκ0 hL0 hLκ (hρL i) (hρ i) (x i)]
  exact @KMonoid.sumOf_sigma L H (S L hL0 hLκ) ι ρ (CardLE.mk' hιL) (fun i => CardLE.mk' (hρL i)) x

/-- The addition of the structure at `ℵ₀` is the two-element `compatSum`. -/
theorem IsCompatible.add_eq_compatSum (hS : IsCompatible κ S) (hκ0 : ℵ₀ < κ)
    (h : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) < κ) (a b : H) :
    (letI := S ℵ₀ le_rfl hκ0; a + b) = compatSum S hκ0 h (Sum.elim (fun _ => a) (fun _ => b)) := by
  have hle : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) ≤ ℵ₀ := (lt_aleph0_of_finite _).le
  exact (@LMonoid.add_eq_lsumOf _ H (S ℵ₀ le_rfl hκ0).toLMonoid (KMonoid.lt_succ hle) a b).trans
    (hS.compatSum_eq hκ0 le_rfl hκ0 hle h _).symm

/-! ### The `κ⁻`-monoid of a compatible family -/

/-- **Remark 2.19** (second half): a compatible family of `λ`-monoid structures on `H`, one for
every infinite cardinal `λ < κ`, defines a `κ⁻`-monoid structure on `H`.  The sum of a family
indexed by `ι` with `#ι < κ` is its sum in the structure at `max #ι ℵ₀`; the addition is that of
the structure at `ℵ₀` (all the additions agree, `IsCompatible.add_eq`).  Restricting back gives
the family one started with (`kMonoidOfLT_ofCompatible`), and every `κ⁻`-monoid arises this way
(`ofCompatible_kMonoidOfLT`).

The paper does not say `ℵ₀ < κ`.  It is needed because a "`λ`-monoid" is only defined for an
infinite cardinal `λ`: at `κ = ℵ₀` the family is empty and carries no information, while an
`ℵ₀⁻`-monoid is an arbitrary commutative monoid.

Paper proof: the only difficulty is (B2).  Since `κ` is regular, for a family of cardinals
`λ_i < κ` indexed by a set of cardinality `< κ` also `λ' = ∑ λ_i < κ`, so any sum occurring in
(B2) can be expressed in the `λ'`-monoid, where (B2) holds.  In the formalisation the regularity
of `κ` is what guarantees the index `Σ i, ρ i` of (B2) to have cardinality `< κ` (the hypothesis
`hσ` of `SumData.sum_sigma`, supplied by `mk_sigma_lt`); `λ'` is then
`max (max #ι #(Σ i, ρ i)) ℵ₀`, see `IsCompatible.compatSum_sigma`. -/
@[instance_reducible]
noncomputable def ofCompatible (hκ : κ.IsRegular) (hκ0 : ℵ₀ < κ)
    (S : ∀ lam : Cardinal.{u}, ℵ₀ ≤ lam → lam < κ → KMonoid lam H) (hS : IsCompatible κ S) :
    LMonoid κ H :=
  { toAddCommMonoid := (S ℵ₀ le_rfl hκ0).toAddCommMonoid
    isRegular := hκ
    sum := compatSum S hκ0
    sum_congr := hS.compatSum_congr hκ0
    sum_unique := compatSum_unique hκ0
    sum_sigma := hS.compatSum_sigma hκ0
    add_eq_sum := hS.add_eq_compatSum hκ0 }

/-- **Remark 2.19**: the sums of `ofCompatible` restrict to those of each member of the family. -/
theorem ofCompatible_lsumOf (hκ : κ.IsRegular) (hκ0 : ℵ₀ < κ) (hS : IsCompatible κ S)
    {lam : Cardinal.{u}} (h0 : ℵ₀ ≤ lam) (hl : lam < κ) {ι : Type u} (hι : #ι ≤ lam)
    (x : ι → H) :
    letI := ofCompatible hκ hκ0 S hS
    lsumOf (lam := κ) (hι.trans_lt hl) x = (letI := S lam h0 hl; ∑[≤ lam] i, x i) := by
  let := ofCompatible hκ hκ0 S hS
  exact hS.compatSum_eq hκ0 h0 hl hι (hι.trans_lt hl) x

/-- **Remark 2.19**: the addition of `ofCompatible` is that of each member of the family. -/
theorem ofCompatible_add (hκ : κ.IsRegular) (hκ0 : ℵ₀ < κ) (hS : IsCompatible κ S)
    {lam : Cardinal.{u}} (h0 : ℵ₀ ≤ lam) (hl : lam < κ) (a b : H) :
    (letI := ofCompatible hκ hκ0 S hS; a + b) = (letI := S lam h0 hl; a + b) :=
  hS.add_eq le_rfl hκ0 h0 hl a b

/-! ### Restriction, and the round trips -/

/-- **Remark 2.19** (first half): a `κ⁻`-monoid is a `λ`-monoid for every infinite `λ < κ`, by
restricting the summation (`LMonoid.ofLE` at `λ⁺ ≤ κ`). -/
@[instance_reducible]
noncomputable def kMonoidOfLT [LMonoid κ H] {lam : Cardinal.{u}} (h0 : ℵ₀ ≤ lam) (hl : lam < κ) :
    KMonoid lam H :=
  { toLMonoid := LMonoid.ofLE (lam₂ := κ) (Cardinal.isRegular_succ h0) (Order.succ_le_of_lt hl)
    aleph0_le := h0 }

/-- **Remark 2.19** (first half): the restrictions of a `κ⁻`-monoid are compatible. -/
theorem isCompatible_kMonoidOfLT [LMonoid κ H] :
    IsCompatible κ (fun _ h0 hl => kMonoidOfLT (H := H) h0 hl) :=
  fun _ _ _ _ _ _ _ _ _ _ => rfl

/-- **Remark 2.19**: restricting the `κ⁻`-monoid of a compatible family to an infinite `λ < κ`
gives back the `λ`-monoid structure of the family. -/
theorem kMonoidOfLT_ofCompatible (hκ : κ.IsRegular) (hκ0 : ℵ₀ < κ) (hS : IsCompatible κ S)
    {lam : Cardinal.{u}} (h0 : ℵ₀ ≤ lam) (hl : lam < κ) :
    letI := ofCompatible hκ hκ0 S hS
    kMonoidOfLT h0 hl = S lam h0 hl := by
  let := ofCompatible hκ hκ0 S hS
  refine KMonoid.ext_of_sumOf ?_ fun hι x =>
    hS.compatSum_eq hκ0 h0 hl hι (hι.trans_lt hl) x
  funext a b
  exact hS.add_eq le_rfl hκ0 h0 hl a b

/-- **Remark 2.19**: every `κ⁻`-monoid (`κ > ℵ₀`) is the `κ⁻`-monoid of the compatible family of
its restrictions. -/
theorem ofCompatible_kMonoidOfLT [M : LMonoid κ H] (hκ0 : ℵ₀ < κ) :
    ofCompatible M.isRegular hκ0 (fun _ h0 hl => kMonoidOfLT (H := H) h0 hl)
      isCompatible_kMonoidOfLT = M :=
  LMonoid.ext_of_lsumOf rfl fun _ _ => rfl

end LMonoid

end KappaMonoid
