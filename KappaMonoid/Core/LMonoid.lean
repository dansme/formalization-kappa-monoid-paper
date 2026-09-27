/-
The `λ⁻`-sum API: the basic laws, sums over subsets, restriction along `λ ≤ λ'`, products,
cardinal scalar multiplication (**Definition 2.6**, **Lemma 2.7**) and reducedness.

Everything is derived from the four axioms (reindexing, one-point sums, (B2), and `+` as the
two-point sum) through a few structural laws, each used by name: `lsumOf_reindex`,
`lsumOf_sumType` (a sum over `α ⊕ β` splits), `lsumOf_prod` (a double sum is a sum over the
product) and `lsumOf_const` (a constant sum depends only on the size of the index type).
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

/-- Reindexing along an equivalence, with the two families compared pointwise. -/
theorem lsumOf_reindex {ι ι' : Type u} [h : CardLT ι lam] [h' : CardLT ι' lam] (e : ι' ≃ ι)
    {x : ι → X} {y : ι' → X} (hxy : ∀ i', x (e i') = y i') :
    ∑[lam] i, x i = ∑[lam] i', y i' :=
  (lsumOf_equiv e x).trans (congrArg _ (funext hxy))

/-- (B1): a sum over a one-point type is its entry. -/
theorem lsumOf_unique {ι : Type u} [Unique ι] [h : CardLT ι lam] (x : ι → X) :
    ∑[lam] i, x i = x default :=
  (inferInstance : LMonoid lam X).sum_unique h.lt x

/-- (B2): a sum may be computed by first summing over the fibres of a partition. -/
theorem lsumOf_sigma {ι : Type u} {ρ : ι → Type u} [h : CardLT ι lam]
    [hρ : ∀ i, CardLT (ρ i) lam] (x : ∀ i, ρ i → X) :
    ∑[lam] i, ∑[lam] j, x i j = ∑[lam] p : (i : ι) × ρ i, x p.1 p.2 :=
  (inferInstance : LMonoid lam X).sum_sigma _ _ x _

/-- Binary addition is the sum over the two-point type `PUnit ⊕ PUnit`. -/
theorem add_eq_lsum (a b : X) :
    a + b = ∑[lam] p : PUnit.{u + 1} ⊕ PUnit.{u + 1}, Sum.elim (fun _ => a) (fun _ => b) p :=
  add_eq_lsumOf _ a b

/-- A sum over `α ⊕ β` splits as a binary sum (`SumData.sum_sumType`). -/
theorem lsumOf_sumType {α β : Type u} [hα : CardLT α lam] [hβ : CardLT β lam] (f : α → X)
    (g : β → X) :
    ∑[lam] p : α ⊕ β, Sum.elim f g p = ∑[lam] a, f a + ∑[lam] b, g b :=
  have := factRegular (lam := lam) (X := X)
  ((LMonoid.toSumData (lam := lam) (X := X)).sum_sumType hα.lt hβ.lt CardLT.lt f g).trans
    (add_eq_lsum _ _).symm

/-- The binary sum, in the `Bool`-indexed form used throughout Sections 3 and 4. -/
theorem lsumOf_two (a b : X) : ∑[lam] p : ULift.{u} Bool, (if p.down then a else b) = a + b := by
  have := factRegular (lam := lam) (X := X)
  calc ∑[lam] p : ULift.{u} Bool, (if p.down then a else b)
      = ∑[lam] p : PUnit.{u + 1} ⊕ PUnit.{u + 1}, Sum.elim (fun _ => b) (fun _ => a) p :=
        lsumOf_reindex uliftBoolEquiv.symm (by rintro (_ | _) <;> rfl)
    _ = a + b := (add_eq_lsum b a).symm.trans (add_comm b a)

@[simp] theorem lsumOf_isEmpty {ι : Type u} [IsEmpty ι] [h : CardLT ι lam] (x : ι → X) :
    ∑[lam] i, x i = 0 := by
  have := factRegular (lam := lam) (X := X)
  calc ∑[lam] i, x i
      = ∑[lam] _ : PUnit.{u + 1}, (0 : X) + ∑[lam] i, x i := by
        rw [lsumOf_unique (ι := PUnit.{u + 1}), zero_add]
    _ = ∑[lam] p : PUnit.{u + 1} ⊕ ι, Sum.elim (fun _ => 0) x p := (lsumOf_sumType _ _).symm
    _ = ∑[lam] _ : PUnit.{u + 1}, (0 : X) := lsumOf_reindex (Equiv.sumEmpty _ ι).symm fun _ => rfl
    _ = 0 := lsumOf_unique _

/-- A double sum is the sum over the product. -/
theorem lsumOf_prod {ι J : Type u} [hι : CardLT ι lam] [hJ : CardLT J lam] (x : ι → J → X) :
    ∑[lam] i, ∑[lam] j, x i j = ∑[lam] p : ι × J, x p.1 p.2 := by
  have := factRegular (lam := lam) (X := X)
  rw [lsumOf_sigma x]
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

/-- Iterated sums may be interchanged: the `λ⁻` form of (A4).

Both sides are the sum over `ι × J`, indexed once as `(i, j)` and once as `(j, i)`. -/
theorem lsumOf_comm {ι J : Type u} [hι : CardLT ι lam] [hJ : CardLT J lam] (x : ι → J → X) :
    ∑[lam] i, ∑[lam] j, x i j = ∑[lam] j, ∑[lam] i, x i j := by
  have := factRegular (lam := lam) (X := X)
  rw [lsumOf_prod, lsumOf_prod, lsumOf_equiv (Equiv.prodComm J ι)]
  rfl

/-- Sums are additive: write `f i + g i` as a sum over two points and swap the two sums. -/
theorem lsumOf_add {ι : Type u} [h : CardLT ι lam] (f g : ι → X) :
    ∑[lam] i, (f i + g i) = ∑[lam] i, f i + ∑[lam] i, g i := by
  have := factRegular (lam := lam) (X := X)
  let x : ι → PUnit.{u + 1} ⊕ PUnit.{u + 1} → X := fun i => Sum.elim (fun _ => f i) (fun _ => g i)
  calc ∑[lam] i, (f i + g i)
      = ∑[lam] i, ∑[lam] p, x i p := by simp only [x, ← add_eq_lsum]
    _ = ∑[lam] p, ∑[lam] i, x i p := lsumOf_comm x
    _ = ∑[lam] i, f i + ∑[lam] i, g i :=
        (lsumOf_reindex (Equiv.refl _) (by rintro (_ | _) <;> rfl)).trans (add_eq_lsum _ _).symm

/-! ### Sums over subsets -/

/-- Additivity over a disjoint union of two small subsets. -/
theorem lsumOf_union {ι : Type u} (S T : Set ι) (hd : Disjoint S T) [hS : CardLT S lam]
    [hT : CardLT T lam] (f : ι → X) :
    ∑[lam] i ∈ S ∪ T, f i = ∑[lam] i ∈ S, f i + ∑[lam] i ∈ T, f i := by
  classical
  have := factRegular (lam := lam) (X := X)
  exact (lsumOf_reindex (Equiv.Set.union hd).symm (by rintro (_ | _) <;> rfl)).trans
    (lsumOf_sumType _ _)

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

/-- Zero-padding along an embedding does not change a sum: the padded family vanishes off the
image of `e` (`lsumOf_of_subset`), and on the image it is `x` reindexed. -/
theorem lsumOf_extend {ι ι' : Type u} [h : CardLT ι lam] [h' : CardLT ι' lam] (e : ι ↪ ι')
    (x : ι → X) :
    ∑[lam] j, Function.extend e x 0 j = ∑[lam] i, x i := by
  let y := Function.extend e x 0
  calc ∑[lam] j, y j
      = ∑[lam] j ∈ (Set.univ : Set ι'), y j := lsumOf_reindex (Equiv.Set.univ ι') fun _ => rfl
    _ = ∑[lam] j ∈ Set.range e, y j :=
        lsumOf_of_subset (Set.subset_univ _) y fun j _ hj => Function.extend_apply' _ _ _ hj
    _ = ∑[lam] i, x i :=
        lsumOf_reindex (Equiv.ofInjective e e.injective) fun i => e.injective.extend_apply x 0 i

/-- Regrouping a sum over a set along a disjoint indexed cover by `< λ`-sized pieces. -/
theorem lsumOf_biUnion_subset {ι J : Type u} (S : Set ι) (I : J → Set ι)
    (hdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q)) (hcover : (⋃ p, I p) = S) [hJ : CardLT J lam]
    [hS : CardLT S lam] [hI : ∀ p, CardLT (I p) lam] (x : ι → X) :
    ∑[lam] p, ∑[lam] i ∈ I p, x i = ∑[lam] i ∈ S, x i := by
  have := factRegular (lam := lam) (X := X)
  let e : S ≃ (p : J) × I p :=
    (Equiv.setCongr hcover.symm).trans (Set.unionEqSigmaOfDisjoint fun p q h => hdisj p q h)
  rw [lsumOf_sigma, lsumOf_equiv e.symm]
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
  sum h x := lsumOf (lam := lam₂) (h.trans_le hle) x
  sum_congr _ _ e x := lsumOf_congr _ _ e x
  sum_unique _ x := (inferInstance : LMonoid lam₂ Y).sum_unique _ x
  sum_sigma h hρ x hσ := (inferInstance : LMonoid lam₂ Y).sum_sigma
    (h.trans_le hle) (fun i => (hρ i).trans_le hle) x (hσ.trans_le hle)
  add_eq_sum _ a b := add_eq_lsumOf _ a b

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
  sum_unique h x := funext fun b => (inferInstance : LMonoid lam (Y b)).sum_unique h fun i => x i b
  sum_sigma h hρ x hσ := funext fun b =>
    (inferInstance : LMonoid lam (Y b)).sum_sigma h hρ (fun i j => x i j b) hσ

/-- A product of `λ⁻`-monoids is a `λ⁻`-monoid, with coordinatewise summation. -/
@[instance_reducible]
noncomputable def pi (lam : Cardinal.{u}) {B : Type w} (Y : B → Type v)
    [∀ b, LMonoid lam (Y b)] (hlam : lam.IsRegular) : LMonoid lam (∀ b, Y b) :=
  (piSumData lam Y hlam).toLMonoid' fun h a b => funext fun i =>
    (add_eq_lsumOf h (a i) (b i)).trans
      (congrArg (lsumOf h) (by funext p; rcases p with _ | _ <;> rfl))

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

/-- A constant sum depends only on the size of its index type: it is `#ι` copies of `x`. -/
theorem lsumOf_const {ι : Type u} [h : CardLT ι lam] (x : X) :
    ∑[lam] _ : ι, x = lcmul (lam := lam) #ι h.lt x := by
  obtain ⟨e⟩ := Cardinal.eq.mp (mk_Idx #ι)
  have := cardLT_Idx h.lt
  exact lsumOf_reindex e fun _ => rfl

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
  have := cardLT_Idx h1
  exact lsumOf_unique _

/-- `α` many copies of `0` sum to `0`. -/
@[simp] theorem lcmul_zero (α : Cardinal.{u}) (hα : α < lam) :
    lcmul (lam := lam) (X := X) α hα 0 = 0 := by
  have := cardLT_Idx hα
  exact lsumOf_zero

/-- **Lemma 2.7(2)**: `(Σ l_i) x = Σ (l_i x)`.  Both sides are the constant sum over
`Σ i, Idx (l i)`, grouped by (B2) on the right. -/
theorem lcmul_lsumOf_cardinal {I : Type u} [hI : CardLT I lam] (l : I → Cardinal.{u})
    (hl : ∀ i, l i < lam) (hsum : Cardinal.sum l < lam) (x : X) :
    lcmul (lam := lam) (Cardinal.sum l) hsum x
      = ∑[lam] i, lcmul (lam := lam) (l i) (hl i) x := by
  have := factRegular (lam := lam) (X := X)
  have hρ : ∀ i, CardLT (Idx (l i)) lam := fun i => cardLT_Idx (hl i)
  have hmk : #((i : I) × Idx (l i)) = Cardinal.sum l := by
    rw [mk_sigma]; exact congrArg _ (funext fun i => mk_Idx (l i))
  calc lcmul (lam := lam) (Cardinal.sum l) hsum x
      = ∑[lam] _ : (i : I) × Idx (l i), x := by rw [lsumOf_const]; exact lcmul_congr hmk.symm _ _ x
    _ = ∑[lam] i, lcmul (lam := lam) (l i) (hl i) x :=
        (lsumOf_sigma (fun i (_ : Idx (l i)) => x)).symm

/-- **Lemma 2.7(3)**. -/
theorem lcmul_lsumOf {I : Type u} [hI : CardLT I lam] (α : Cardinal.{u}) (hα : α < lam)
    (x : I → X) :
    lcmul (lam := lam) α hα (∑[lam] i, x i) = ∑[lam] i, lcmul (lam := lam) α hα (x i) :=
  haveI := cardLT_Idx (lam := lam) hα
  lsumOf_comm fun _ i => x i

/-- **Lemma 2.7(2)** for a two-term sum of cardinals: split the constant sum over
`Idx α ⊕ Idx β`. -/
theorem lcmul_add {α β : Cardinal.{u}} (hα : α < lam) (hβ : β < lam) (hαβ : α + β < lam) (x : X) :
    lcmul (lam := lam) (α + β) hαβ x
      = lcmul (lam := lam) α hα x + lcmul (lam := lam) β hβ x := by
  have := factRegular (lam := lam) (X := X)
  have := cardLT_Idx hα
  have := cardLT_Idx hβ
  calc lcmul (lam := lam) (α + β) hαβ x
      = ∑[lam] p : Idx α ⊕ Idx β, Sum.elim (fun _ => x) (fun _ => x) p := by
        rw [Sum.elim_lam_const_lam_const, lsumOf_const]
        exact lcmul_congr (by simp) _ _ x
    _ = lcmul (lam := lam) α hα x + lcmul (lam := lam) β hβ x := lsumOf_sumType _ _

/-- Iterated scaling: `α` copies of `β` copies of `x` is the constant sum over `Idx α × Idx β`,
that is `α * β` copies of `x`. -/
theorem lcmul_lcmul {α β : Cardinal.{u}} (hα : α < lam) (hβ : β < lam) (hαβ : α * β < lam)
    (x : X) :
    lcmul (lam := lam) α hα (lcmul (lam := lam) β hβ x) = lcmul (lam := lam) (α * β) hαβ x := by
  have := factRegular (lam := lam) (X := X)
  have := cardLT_Idx hα
  have := cardLT_Idx hβ
  calc lcmul (lam := lam) α hα (lcmul (lam := lam) β hβ x)
      = ∑[lam] _ : Idx α × Idx β, x := lsumOf_prod fun _ _ => x
    _ = lcmul (lam := lam) (α * β) hαβ x := by
        rw [lsumOf_const]
        exact lcmul_congr (by rw [mk_prod, mk_Idx, mk_Idx, lift_id, lift_id]) _ _ x

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

/-- **Lemma 2.8(1)** for `λ⁻`-monoids: a `λ⁻`-monoid with `ℵ₀ < λ` is reduced.

The paper's Eilenberg–Mazur swindle, run with `ℵ₀` in place of `κ`: if `x + y = 0 = ℵ₀·0`,
then `x + ℵ₀·0 = ℵ₀·0` by Lemma 2.8(2) (`add_lcmul_eq`), that is `x = 0`.

The hypothesis `ℵ₀ < λ` cannot be dropped: an `ℵ₀⁻`-monoid is an arbitrary commutative
monoid (`LMonoid.ofAddCommMonoid`), and `ℤ` is not reduced.  This is the `κ > ℵ₀` the paper asks
for when it says the analogues of Lemma 2.8 hold for `κ⁻`-monoids. -/
theorem isConical (h : ℵ₀ < lam) : IsConical X := by
  have key : ∀ x y : X, x + y = 0 → x = 0 := fun x y hxy => by
    have := add_lcmul_eq le_rfl h (t₃ := (0 : X)) (by rw [lcmul_zero]; exact hxy)
    rwa [lcmul_zero, add_zero] at this
  exact fun x y hxy => ⟨key x y hxy, key y x (by rwa [add_comm])⟩

end LMonoid

end KappaMonoid
