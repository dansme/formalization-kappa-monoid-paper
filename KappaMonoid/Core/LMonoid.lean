/-
The `λ⁻`-sum API: the basic laws, sums over subsets, restriction along `λ ≤ λ'`, products,
cardinal scalar multiplication (**Definition 2.6**, **Lemma 2.7**) and reducedness.
-/
import KappaMonoid.Core.LamSmall

universe u v w

open Cardinal Function Set

namespace KappaMonoid

namespace LMonoid

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X]

theorem isRegular' {X : Type v} [inst : LMonoid lam X] : lam.IsRegular := inst.isRegular

theorem aleph0_le {X : Type v} [inst : LMonoid lam X] : ℵ₀ ≤ lam := inst.isRegular.aleph0_le

theorem mk_lt_finite {X : Type v} [LMonoid lam X] (ι : Type u) [Finite ι] : #ι < lam :=
  mk_lt_of_finite (isRegular' (X := X)) ι

theorem mk_uLift_bool_lt {X : Type v} [LMonoid lam X] : #(ULift.{u} Bool) < lam :=
  mk_lt_finite (X := X) _

/-- `λ` is regular, as the instance the product, sum and sigma rules for `CardLT` need. -/
theorem factRegular {X : Type v} [LMonoid lam X] : Fact lam.IsRegular := ⟨isRegular' (X := X)⟩

/-! ### Basic laws -/

/-- Reindexing along an equivalence. -/
theorem lsumOf_equiv {ι ι' : Type u} [h : CardLT ι lam] [h' : CardLT ι' lam] (e : ι' ≃ ι)
    (x : ι → X) :
    ∑[lam] i, x i = ∑[lam] i', x (e i') :=
  (lsumOf_congr _ _ e x).symm

/-- A sum over `α ⊕ β` splits as a binary sum. -/
theorem lsumOf_sumType {α β : Type u} [hα : CardLT α lam] [hβ : CardLT β lam] (f : α → X)
    (g : β → X) :
    ∑[lam] p : α ⊕ β, Sum.elim f g p = ∑[lam] a, f a + ∑[lam] b, g b := by
  have := factRegular (lam := lam) (X := X)
  have hρ : ∀ p : ULift.{u} Bool, CardLT (bif p.down then β else α) lam := by
    rintro ⟨(_ | _)⟩ <;> assumption
  calc ∑[lam] p : α ⊕ β, Sum.elim f g p
      = ∑[lam] q, Sum.elim f g (sigmaBoolEquiv α β q) := lsumOf_equiv (sigmaBoolEquiv α β) _
    _ = ∑[lam] q : (p : ULift.{u} Bool) × (bif p.down then β else α), boolFam f g q.1 q.2 := by
        congr 1; funext p; obtain ⟨⟨(_ | _)⟩, y⟩ := p <;> rfl
    _ = ∑[lam] p, ∑[lam] q, boolFam f g p q :=
        (lsumOf_sigma CardLT.lt (fun p => (hρ p).lt) (boolFam f g) CardLT.lt).symm
    _ = ∑[lam] p : PUnit.{u + 1} ⊕ PUnit.{u + 1},
          Sum.elim (fun _ => ∑[lam] a, f a) (fun _ => ∑[lam] b, g b) p := by
        rw [lsumOf_equiv uliftBoolEquiv]
        congr 1; funext p; obtain ⟨(_ | _)⟩ := p <;> rfl
    _ = ∑[lam] a, f a + ∑[lam] b, g b := (add_eq_lsumOf _ _ _).symm

@[simp] theorem lsumOf_isEmpty {ι : Type u} [IsEmpty ι] [h : CardLT ι lam] (x : ι → X) :
    ∑[lam] i, x i = 0 := by
  have := factRegular (lam := lam) (X := X)
  calc ∑[lam] i, x i
      = ∑[lam] _ : PUnit.{u + 1}, (0 : X) + ∑[lam] i, x i := by
        rw [lsumOf_unique (ι := PUnit.{u + 1}) CardLT.lt, zero_add]
    _ = ∑[lam] p : PUnit.{u + 1} ⊕ ι, Sum.elim (fun _ => 0) x p := (lsumOf_sumType _ _).symm
    _ = ∑[lam] _ : PUnit.{u + 1}, (0 : X) := lsumOf_equiv (Equiv.sumEmpty PUnit.{u + 1} ι).symm _
    _ = 0 := lsumOf_unique CardLT.lt _

/-- A double sum is the sum over the product. -/
theorem lsumOf_prod {ι J : Type u} [hι : CardLT ι lam] [hJ : CardLT J lam] (x : ι → J → X) :
    ∑[lam] i, ∑[lam] j, x i j = ∑[lam] p : ι × J, x p.1 p.2 := by
  have := factRegular (lam := lam) (X := X)
  rw [lsumOf_sigma CardLT.lt (fun _ => CardLT.lt) x CardLT.lt]
  exact lsumOf_equiv (Equiv.sigmaEquivProd ι J).symm _

@[simp] theorem lsumOf_zero {ι : Type u} [h : CardLT ι lam] : ∑[lam] _ : ι, (0 : X) = 0 := by
  have := factRegular (lam := lam) (X := X)
  calc ∑[lam] _ : ι, (0 : X)
      = ∑[lam] _ : ι, ∑[lam] _ : PEmpty.{u + 1}, (0 : X) := by simp only [lsumOf_isEmpty]
    _ = ∑[lam] _ : ι × PEmpty.{u + 1}, (0 : X) := lsumOf_prod _
    _ = 0 := lsumOf_isEmpty _

theorem lsumOf_eq_zero_of_forall {ι : Type u} [h : CardLT ι lam] {x : ι → X} (hx : ∀ i, x i = 0) :
    ∑[lam] i, x i = 0 := by
  simp only [hx, lsumOf_zero]

/-- Zero-padding along an embedding does not change a sum: split `ι'` into the image of `e`,
where the padded family is `x` reindexed, and the rest, where it is `0`. -/
theorem lsumOf_extend {ι ι' : Type u} [h : CardLT ι lam] [h' : CardLT ι' lam] (e : ι ↪ ι')
    (x : ι → X) :
    ∑[lam] j, Function.extend e x 0 j = ∑[lam] i, x i := by
  classical
  have := factRegular (lam := lam) (X := X)
  let y := Function.extend e x 0
  calc ∑[lam] j, y j
      = ∑[lam] p : {j // j ∈ Set.range e} ⊕ {j // j ∉ Set.range e},
          Sum.elim (fun j => y j.1) (fun j => y j.1) p := by
        rw [lsumOf_equiv (Equiv.sumCompl (· ∈ Set.range e))]
        congr 1; funext p; rcases p with p | p <;> rfl
    _ = ∑[lam] j : {j // j ∈ Set.range e}, y j.1 + ∑[lam] j : {j // j ∉ Set.range e}, y j.1 :=
        lsumOf_sumType _ _
    _ = ∑[lam] i, x i + 0 := by
        congr 1
        · rw [lsumOf_equiv (Equiv.ofInjective e e.injective)]
          exact congrArg _ (funext fun i => e.injective.extend_apply x 0 i)
        · exact lsumOf_eq_zero_of_forall fun j => Function.extend_apply' _ _ _ j.2
    _ = ∑[lam] i, x i := add_zero _

/-- The binary sum, in the `Bool`-indexed form used throughout Sections 3 and 4. -/
theorem lsumOf_two (a b : X) : ∑[lam] p : ULift.{u} Bool, (if p.down then a else b) = a + b := by
  have := factRegular (lam := lam) (X := X)
  rw [lsumOf_equiv uliftBoolEquiv.symm,
    show (fun p => if (uliftBoolEquiv.symm p).down then a else b)
      = Sum.elim (fun _ : PUnit.{u + 1} => b) (fun _ : PUnit.{u + 1} => a) by
        funext p; rcases p with p | p <;> rfl,
    lsumOf_sumType, lsumOf_unique, lsumOf_unique]
  exact add_comm b a

/-- Iterated sums may be interchanged: the `λ⁻` form of (A4).

Both sides are the sum over `ι × J`, indexed once as `(i, j)` and once as `(j, i)`. -/
theorem lsumOf_comm {ι J : Type u} [hι : CardLT ι lam] [hJ : CardLT J lam] (x : ι → J → X) :
    ∑[lam] i, ∑[lam] j, x i j = ∑[lam] j, ∑[lam] i, x i j := by
  have := factRegular (lam := lam) (X := X)
  rw [lsumOf_prod, lsumOf_prod, lsumOf_equiv (Equiv.prodComm J ι)]
  rfl

/-- Sums are additive.

Write `f i + g i` as a sum over `Bool`, swap the two sums, and read off `Σ f + Σ g`. -/
theorem lsumOf_add {ι : Type u} [h : CardLT ι lam] (f g : ι → X) :
    ∑[lam] i, (f i + g i) = ∑[lam] i, f i + ∑[lam] i, g i := by
  have := factRegular (lam := lam) (X := X)
  let x : ι → ULift.{u} Bool → X := fun i b => if b.down then f i else g i
  calc ∑[lam] i, (f i + g i)
      = ∑[lam] i, ∑[lam] b, x i b := by
        simp only [x, lsumOf_two]
    _ = ∑[lam] b, ∑[lam] i, x i b := lsumOf_comm x
    _ = ∑[lam] i, f i + ∑[lam] i, g i := by
        rw [← lsumOf_two]
        congr 1; funext b; rcases b with ⟨_ | _⟩ <;> rfl

/-! ### Sums over subsets -/

/-- Additivity over a disjoint union of two small subsets. -/
theorem lsumOf_union {ι : Type u} (S T : Set ι) (hd : Disjoint S T) [hS : CardLT S lam]
    [hT : CardLT T lam] (f : ι → X) :
    ∑[lam] i ∈ S ∪ T, f i = ∑[lam] i ∈ S, f i + ∑[lam] i ∈ T, f i := by
  classical
  have := factRegular (lam := lam) (X := X)
  rw [lsumOf_equiv (Equiv.Set.union hd).symm, ← lsumOf_sumType]
  congr 1
  funext p
  rcases p with p | p <;> rfl

/-- Terms with value `0` may be discarded: `S = T ⊔ (S \ T)`, and the sum over `S \ T` is `0`. -/
theorem lsumOf_of_subset {ι : Type u} {S T : Set ι} [hS : CardLT S lam] [hT : CardLT T lam]
    (hsub : T ⊆ S) (f : ι → X) (hzero : ∀ i ∈ S, i ∉ T → f i = 0) :
    ∑[lam] i ∈ S, f i = ∑[lam] i ∈ T, f i := by
  have := factRegular (lam := lam) (X := X)
  calc ∑[lam] i ∈ S, f i
      = ∑[lam] i ∈ T ∪ (S \ T), f i :=
        lsumOf_equiv (Equiv.setCongr (Set.union_sdiff_cancel hsub)) _
    _ = ∑[lam] i ∈ T, f i + ∑[lam] i ∈ S \ T, f i := lsumOf_union _ _ Set.disjoint_sdiff_right _
    _ = ∑[lam] i ∈ T, f i + 0 := by
        rw [lsumOf_eq_zero_of_forall (x := fun i : ↥(S \ T) => f i) fun i => hzero i i.2.1 i.2.2]
    _ = ∑[lam] i ∈ T, f i := add_zero _

/-- A sum of zeros over a subset vanishes. -/
theorem lsumOf_eq_zero {ι : Type u} {T : Set ι} [hT : CardLT T lam] (f : ι → X)
    (hzero : ∀ i ∈ T, f i = 0) :
    ∑[lam] i ∈ T, f i = 0 :=
  lsumOf_eq_zero_of_forall fun i => hzero i i.2

/-- Regrouping a sum over a set along a disjoint indexed cover by `< λ`-sized pieces. -/
theorem lsumOf_biUnion_subset {ι J : Type u} (S : Set ι) (I : J → Set ι)
    (hdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q)) (hcover : (⋃ p, I p) = S) [hJ : CardLT J lam]
    [hS : CardLT S lam] [hI : ∀ p, CardLT (I p) lam] (x : ι → X) :
    ∑[lam] p, ∑[lam] i ∈ I p, x i = ∑[lam] i ∈ S, x i := by
  have := factRegular (lam := lam) (X := X)
  let e : S ≃ (p : J) × I p :=
    (Equiv.setCongr hcover.symm).trans (Set.unionEqSigmaOfDisjoint fun p q h => hdisj p q h)
  rw [lsumOf_sigma CardLT.lt (fun _ => CardLT.lt) _ CardLT.lt, lsumOf_equiv e.symm]
  congr 1

/-- A sum over a two-element subset. -/
theorem lsumOf_pair {ι : Type u} {a b : ι} (hab : a ≠ b) (f : ι → X) :
    ∑[lam] i ∈ ({a, b} : Set ι), f i = f a + f b := by
  have := factRegular (lam := lam) (X := X)
  calc ∑[lam] i ∈ ({a, b} : Set ι), f i
      = ∑[lam] i ∈ ({a} : Set ι) ∪ {b}, f i :=
        lsumOf_equiv (Equiv.setCongr (Set.insert_eq a {b})).symm _
    _ = f a + f b := by
        rw [lsumOf_union _ _ (Set.disjoint_singleton.mpr hab) f, lsumOf_unique, lsumOf_unique]
        rfl

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

/-! ### Products

The Cartesian product of `λ⁻`-monoids is a `λ⁻`-monoid with coordinatewise operations; this is
the ambient monoid `F_κ^B` of the free objects of §2.1. -/

/-- Coordinatewise summation data on a product of `λ⁻`-monoids. -/
noncomputable def piSumData (lam : Cardinal.{u}) {B : Type w} (Y : B → Type v)
    [∀ b, LMonoid lam (Y b)] (hlam : lam.IsRegular) : SumData lam (∀ b, Y b) where
  isRegular := hlam
  sum h x := fun b => lsumOf (lam := lam) h fun i => x i b
  sum_congr h h' e x := funext fun b => lsumOf_congr h h' e fun i => x i b
  sum_unique h x := funext fun b => lsumOf_unique h fun i => x i b
  sum_sigma h hρ x hσ := funext fun b => lsumOf_sigma h hρ (fun i j => x i j b) hσ

/-- A product of `λ⁻`-monoids is a `λ⁻`-monoid, with coordinatewise summation. -/
@[instance_reducible]
noncomputable def pi (lam : Cardinal.{u}) {B : Type w} (Y : B → Type v)
    [∀ b, LMonoid lam (Y b)] (hlam : lam.IsRegular) : LMonoid lam (∀ b, Y b) :=
  (piSumData lam Y hlam).toLMonoid' fun h a b => funext fun i => by
    show a i + b i = lsumOf (lam := lam) h fun p => Sum.elim (fun _ => a) (fun _ => b) p i
    rw [show (fun p : PUnit.{u + 1} ⊕ PUnit.{u + 1} => Sum.elim (fun _ => a) (fun _ => b) p i)
        = Sum.elim (fun _ => a i) (fun _ => b i) from
      funext fun p => by rcases p with p | p <;> rfl]
    exact add_eq_lsumOf h (a i) (b i)

/-- Sums in a product of `λ⁻`-monoids are computed coordinatewise. -/
@[simp] theorem pi_lsumOf (lam : Cardinal.{u}) {B : Type w} (Y : B → Type v)
    [∀ b, LMonoid lam (Y b)] (hlam : lam.IsRegular) {ι : Type u} (h : #ι < lam)
    (x : ι → ∀ b, Y b) (b : B) :
    letI := pi lam Y hlam
    lsumOf (lam := lam) h x b = lsumOf (lam := lam) h fun i => x i b := rfl

/-! ### Cardinal scalar multiplication (Definition 2.6, Lemma 2.7)

The paper states Definition 2.6 and Lemma 2.7 for `κ`-monoids, and remarks at the end of §2.4
that the analogues hold for `λ⁻`-monoids with all cardinals taken `< λ`.  They are proved here
in that generality; `KMonoid.cmul` and its lemmas are the special case `λ = κ⁺`. -/

/-- **Definition 2.6** for `λ⁻`-monoids: `lcmul α x` is the sum of `α` many copies of `x`. -/
noncomputable def lcmul (α : Cardinal.{u}) (hα : α < lam) (x : X) : X :=
  lsumOf (lam := lam) (lt_of_eq_of_lt (mk_Idx α) hα) fun _ : Idx α => x

/-- `Idx α` is small when `α < λ`: the index type of `lcmul α`. -/
theorem cardLT_Idx {α : Cardinal.{u}} (hα : α < lam) : CardLT (Idx α) lam :=
  ⟨lt_of_eq_of_lt (mk_Idx α) hα⟩

theorem lcmul_congr {α β : Cardinal.{u}} (h : α = β) (hα : α < lam) (hβ : β < lam) (x : X) :
    lcmul (lam := lam) α hα x = lcmul (lam := lam) β hβ x := by subst h; rfl

/-- **Lemma 2.7(1)**, first half. -/
@[simp] theorem lcmul_zero_cardinal (h0 : (0 : Cardinal.{u}) < lam) (x : X) :
    lcmul (lam := lam) 0 h0 x = 0 := by
  have : IsEmpty (Idx (0 : Cardinal.{u})) := Cardinal.mk_eq_zero_iff.mp (mk_Idx 0)
  have := cardLT_Idx h0
  exact lsumOf_isEmpty _

/-- **Lemma 2.7(1)**, second half. -/
@[simp] theorem lcmul_one (h1 : (1 : Cardinal.{u}) < lam) (x : X) :
    lcmul (lam := lam) 1 h1 x = x := by
  have hsub : Subsingleton (Idx (1 : Cardinal.{u})) :=
    Cardinal.le_one_iff_subsingleton.mp (le_of_eq (mk_Idx 1))
  have hne : Nonempty (Idx (1 : Cardinal.{u})) := by
    rw [← Cardinal.mk_ne_zero_iff, mk_Idx]; exact one_ne_zero
  let : Unique (Idx (1 : Cardinal.{u})) := uniqueOfSubsingleton hne.some
  exact lsumOf_unique _ _

/-- `α` many copies of `0` sum to `0`. -/
@[simp] theorem lcmul_zero (α : Cardinal.{u}) (hα : α < lam) :
    lcmul (lam := lam) (X := X) α hα 0 = 0 := by
  have := cardLT_Idx hα
  exact lsumOf_zero

/-- **Lemma 2.7(2)**. -/
theorem lcmul_lsumOf_cardinal {I : Type u} [hI : CardLT I lam] (l : I → Cardinal.{u})
    (hl : ∀ i, l i < lam) (hsum : Cardinal.sum l < lam) (x : X) :
    lcmul (lam := lam) (Cardinal.sum l) hsum x
      = ∑[lam] i, lcmul (lam := lam) (l i) (hl i) x := by
  have := factRegular (lam := lam) (X := X)
  have hρ : ∀ i, CardLT (Idx (l i)) lam := fun i => cardLT_Idx (hl i)
  have := cardLT_Idx hsum
  have hmk : #((i : I) × Idx (l i)) = Cardinal.sum l := by
    rw [mk_sigma]; exact congrArg _ (funext fun i => mk_Idx (l i))
  obtain ⟨Ψ⟩ := Cardinal.eq.mp (hmk.trans (mk_Idx (Cardinal.sum l)).symm)
  calc lcmul (lam := lam) (Cardinal.sum l) hsum x
      = ∑[lam] _ : (i : I) × Idx (l i), x := lsumOf_equiv Ψ (fun _ => x)
    _ = ∑[lam] i, lcmul (lam := lam) (l i) (hl i) x :=
        (lsumOf_sigma CardLT.lt (fun i => (hρ i).lt) (fun i (_ : Idx (l i)) => x) CardLT.lt).symm

/-- **Lemma 2.7(3)**. -/
theorem lcmul_lsumOf {I : Type u} [hI : CardLT I lam] (α : Cardinal.{u}) (hα : α < lam)
    (x : I → X) :
    lcmul (lam := lam) α hα (∑[lam] i, x i) = ∑[lam] i, lcmul (lam := lam) α hα (x i) :=
  haveI := cardLT_Idx (lam := lam) hα
  lsumOf_comm fun _ i => x i

/-- **Lemma 2.7(2)** for a two-term sum of cardinals. -/
theorem lcmul_add {α β : Cardinal.{u}} (hα : α < lam) (hβ : β < lam) (hαβ : α + β < lam) (x : X) :
    lcmul (lam := lam) (α + β) hαβ x
      = lcmul (lam := lam) α hα x + lcmul (lam := lam) β hβ x := by
  have := factRegular (lam := lam) (X := X)
  have := cardLT_Idx hα
  have := cardLT_Idx hβ
  have := cardLT_Idx hαβ
  obtain ⟨e⟩ : Nonempty (Idx α ⊕ Idx β ≃ Idx (α + β)) := Cardinal.eq.mp (by simp)
  calc lcmul (lam := lam) (α + β) hαβ x
      = ∑[lam] p : Idx α ⊕ Idx β, Sum.elim (fun _ : Idx α => x) (fun _ : Idx β => x) p := by
        rw [lcmul, lsumOf_equiv e]
        congr 1; funext p; rcases p with p | p <;> rfl
    _ = lcmul (lam := lam) α hα x + lcmul (lam := lam) β hβ x := lsumOf_sumType _ _

/-- Iterated scaling: `α` copies of `β` copies of `x` is `α * β` copies of `x`. -/
theorem lcmul_lcmul {α β : Cardinal.{u}} (hα : α < lam) (hβ : β < lam) (hαβ : α * β < lam)
    (x : X) :
    lcmul (lam := lam) α hα (lcmul (lam := lam) β hβ x) = lcmul (lam := lam) (α * β) hαβ x := by
  have := factRegular (lam := lam) (X := X)
  have := cardLT_Idx hα
  have := cardLT_Idx hβ
  have := cardLT_Idx hαβ
  have hmk : #((_ : Idx α) × Idx β) = α * β := by
    rw [Cardinal.mk_congr (Equiv.sigmaEquivProd (Idx α) (Idx β)), Cardinal.mk_prod, mk_Idx,
      mk_Idx, Cardinal.lift_id, Cardinal.lift_id]
  obtain ⟨Ψ⟩ := Cardinal.eq.mp (hmk.trans (mk_Idx (α * β)).symm)
  calc lcmul (lam := lam) α hα (lcmul (lam := lam) β hβ x)
      = ∑[lam] _ : (_ : Idx α) × Idx β, x :=
        lsumOf_sigma CardLT.lt (fun _ => CardLT.lt) (fun (_ : Idx α) (_ : Idx β) => x) CardLT.lt
    _ = lcmul (lam := lam) (α * β) hαβ x := (lsumOf_equiv Ψ (fun _ => x)).symm

/-- The remark after **Definition 2.6**: for an infinite `α < λ`, adding one more copy of `x` to
`α` many copies of `x` does not change the value.  Immediate from `lcmul_add` and `1 + α = α`. -/
theorem add_lcmul_self {α : Cardinal.{u}} (hα0 : ℵ₀ ≤ α) (hα : α < lam) (x : X) :
    x + lcmul (lam := lam) α hα x = lcmul (lam := lam) α hα x := by
  have h1 : (1 : Cardinal.{u}) < lam := lt_of_lt_of_le one_lt_aleph0 (aleph0_le (X := X))
  have hsum : (1 : Cardinal.{u}) + α = α := Cardinal.add_eq_right hα0 (one_le_aleph0.trans hα0)
  calc x + lcmul (lam := lam) α hα x
      = lcmul (lam := lam) 1 h1 x + lcmul (lam := lam) α hα x := by rw [lcmul_one]
    _ = lcmul (lam := lam) (1 + α) (lt_of_eq_of_lt hsum hα) x := (lcmul_add h1 hα _ x).symm
    _ = lcmul (lam := lam) α hα x := lcmul_congr hsum _ _ x

/-- Scaling distributes over `+` (a special case of **Lemma 2.7(3)**). -/
theorem lcmul_distrib {α : Cardinal.{u}} (hα : α < lam) (a b : X) :
    lcmul (lam := lam) α hα (a + b)
      = lcmul (lam := lam) α hα a + lcmul (lam := lam) α hα b :=
  haveI : CardLT (Idx α) lam := ⟨lt_of_eq_of_lt (mk_Idx α) hα⟩
  lsumOf_add (fun _ => a) fun _ => b

/-! ### Reducedness (Lemma 2.8) -/

/-- **Lemma 2.8(1)** for `λ⁻`-monoids: a `λ⁻`-monoid with `ℵ₀ < λ` is reduced.

The paper's Eilenberg–Mazur swindle, run with `ℵ₀` in place of `κ`: if `x + y = 0` then
`x = x + ℵ₀·0 = x + ℵ₀(x+y) = (x + ℵ₀x) + ℵ₀y = ℵ₀x + ℵ₀y = ℵ₀(x+y) = 0`.

The hypothesis `ℵ₀ < λ` cannot be dropped: an `ℵ₀⁻`-monoid is an arbitrary commutative
monoid (`LMonoid.ofAddCommMonoid`), and `ℤ` is not reduced.  This is the `κ > ℵ₀` the paper asks
for when it says the analogues of Lemma 2.8 hold for `κ⁻`-monoids. -/
theorem isConical (h : ℵ₀ < lam) : IsConical X := by
  have key : ∀ x y : X, x + y = 0 → x = 0 := by
    intro x y hxy
    have hcz : lcmul (lam := lam) ℵ₀ h (0 : X) = 0 := lcmul_zero _ _
    calc x = x + (0 : X) := (add_zero x).symm
      _ = x + lcmul (lam := lam) ℵ₀ h 0 := by rw [hcz]
      _ = x + lcmul (lam := lam) ℵ₀ h (x + y) := by rw [hxy]
      _ = x + (lcmul (lam := lam) ℵ₀ h x + lcmul (lam := lam) ℵ₀ h y) := by rw [lcmul_distrib]
      _ = (x + lcmul (lam := lam) ℵ₀ h x) + lcmul (lam := lam) ℵ₀ h y := (add_assoc _ _ _).symm
      _ = lcmul (lam := lam) ℵ₀ h x + lcmul (lam := lam) ℵ₀ h y := by
          rw [add_lcmul_self le_rfl h x]
      _ = lcmul (lam := lam) ℵ₀ h (x + y) := (lcmul_distrib h x y).symm
      _ = 0 := by rw [hxy, hcz]
  exact fun x y hxy => ⟨key x y hxy, key y x (by rw [add_comm]; exact hxy)⟩

/-- Scaling by an infinite cardinal is idempotent (since `α * α = α`). -/
theorem lcmul_idem {α : Cardinal.{u}} (hα0 : ℵ₀ ≤ α) (hα : α < lam) (x : X) :
    lcmul (lam := lam) α hα (lcmul (lam := lam) α hα x) = lcmul (lam := lam) α hα x := by
  rw [lcmul_lcmul hα hα (lt_of_eq_of_lt (Cardinal.mul_eq_self hα0) hα) x]
  exact lcmul_congr (Cardinal.mul_eq_self hα0) _ _ x

/-- **Lemma 2.8(2)** for `λ⁻`-monoids. -/
theorem add_lcmul_eq {α : Cardinal.{u}} (hα0 : ℵ₀ ≤ α) (hα : α < lam) {t₁ t₂ t₃ : X}
    (h : t₁ + t₂ = lcmul (lam := lam) α hα t₃) :
    t₁ + lcmul (lam := lam) α hα t₃ = lcmul (lam := lam) α hα t₃ := by
  have hstep : lcmul (lam := lam) α hα (t₁ + t₂) = lcmul (lam := lam) α hα t₃ := by
    rw [h]; exact lcmul_idem hα0 hα t₃
  calc t₁ + lcmul (lam := lam) α hα t₃
      = t₁ + lcmul (lam := lam) α hα (t₁ + t₂) := by rw [← hstep]
    _ = t₁ + (lcmul (lam := lam) α hα t₁ + lcmul (lam := lam) α hα t₂) := by rw [lcmul_distrib]
    _ = (t₁ + lcmul (lam := lam) α hα t₁) + lcmul (lam := lam) α hα t₂ := (add_assoc _ _ _).symm
    _ = lcmul (lam := lam) α hα t₁ + lcmul (lam := lam) α hα t₂ := by
        rw [add_lcmul_self hα0 hα t₁]
    _ = lcmul (lam := lam) α hα (t₁ + t₂) := by rw [lcmul_distrib]
    _ = lcmul (lam := lam) α hα t₃ := hstep

end LMonoid

end KappaMonoid
