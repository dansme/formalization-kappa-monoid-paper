/-
The `λ⁻`-sum API: the basic laws, sums over subsets, restriction along `λ ≤ λ'`, products,
cardinal scalar multiplication (**Definition 2.6**, **Lemma 2.7**) and reducedness.
-/
import KappaMonoid.Core.SumData

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

/-- Iterated sums may be interchanged: the `λ⁻` form of (A4). -/
theorem lsumOf_comm {ι J : Type u} (hι : #ι < lam) (hJ : #J < lam) (x : ι → J → X) :
    lsumOf (lam := lam) hι (fun i => lsumOf (lam := lam) hJ (x i))
      = lsumOf (lam := lam) hJ fun j => lsumOf (lam := lam) hι fun i => x i j := by
  have hσ1 : #((_ : ι) × J) < lam := mk_sigma_lt (isRegular' (X := X)) hι fun _ => hJ
  have hσ2 : #((_ : J) × ι) < lam := mk_sigma_lt (isRegular' (X := X)) hJ fun _ => hι
  rw [lsumOf_sigma hι (fun _ => hJ) x hσ1, lsumOf_sigma hJ (fun _ => hι) (fun j i => x i j) hσ2,
    lsumOf_equiv hσ2 hσ1 ((Equiv.sigmaEquivProd ι J).trans
      ((Equiv.prodComm ι J).trans (Equiv.sigmaEquivProd J ι).symm))]
  congr 1

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

theorem lcmul_congr {α β : Cardinal.{u}} (h : α = β) (hα : α < lam) (hβ : β < lam) (x : X) :
    lcmul (lam := lam) α hα x = lcmul (lam := lam) β hβ x := by subst h; rfl

/-- **Lemma 2.7(1)**, first half. -/
@[simp] theorem lcmul_zero_cardinal (h0 : (0 : Cardinal.{u}) < lam) (x : X) :
    lcmul (lam := lam) 0 h0 x = 0 := by
  have : IsEmpty (Idx (0 : Cardinal.{u})) := Cardinal.mk_eq_zero_iff.mp (mk_Idx 0)
  exact lsumOf_isEmpty _ _

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
    lcmul (lam := lam) (X := X) α hα 0 = 0 := lsumOf_zero _

/-- **Lemma 2.7(2)**. -/
theorem lcmul_lsumOf_cardinal {I : Type u} (hI : #I < lam) (l : I → Cardinal.{u})
    (hl : ∀ i, l i < lam) (hsum : Cardinal.sum l < lam) (x : X) :
    lcmul (lam := lam) (Cardinal.sum l) hsum x
      = lsumOf (lam := lam) hI fun i => lcmul (lam := lam) (l i) (hl i) x := by
  have hρ : ∀ i, #(Idx (l i)) < lam := fun i => lt_of_eq_of_lt (mk_Idx (l i)) (hl i)
  have hmk : #((i : I) × Idx (l i)) = Cardinal.sum l := by
    rw [mk_sigma]; exact congrArg _ (funext fun i => mk_Idx (l i))
  have hσ : #((i : I) × Idx (l i)) < lam := lt_of_eq_of_lt hmk hsum
  obtain ⟨Ψ⟩ := Cardinal.eq.mp (hmk.trans (mk_Idx (Cardinal.sum l)).symm)
  calc lcmul (lam := lam) (Cardinal.sum l) hsum x
      = lsumOf (lam := lam) hσ (fun _ : (i : I) × Idx (l i) => x) :=
        lsumOf_equiv (lt_of_eq_of_lt (mk_Idx (Cardinal.sum l)) hsum) hσ Ψ (fun _ => x)
    _ = lsumOf (lam := lam) hI (fun i => lcmul (lam := lam) (l i) (hl i) x) :=
        (lsumOf_sigma hI hρ (fun i (_ : Idx (l i)) => x) hσ).symm

/-- **Lemma 2.7(3)**. -/
theorem lcmul_lsumOf {I : Type u} (hI : #I < lam) (α : Cardinal.{u}) (hα : α < lam) (x : I → X) :
    lcmul (lam := lam) α hα (lsumOf (lam := lam) hI x)
      = lsumOf (lam := lam) hI fun i => lcmul (lam := lam) α hα (x i) := by
  have hα' : #(Idx α) < lam := lt_of_eq_of_lt (mk_Idx α) hα
  have hσ1 : #((_ : Idx α) × I) < lam := mk_sigma_lt (isRegular' (X := X)) hα' fun _ => hI
  have hσ2 : #((_ : I) × Idx α) < lam := mk_sigma_lt (isRegular' (X := X)) hI fun _ => hα'
  have stepA : lcmul (lam := lam) α hα (lsumOf (lam := lam) hI x)
      = lsumOf (lam := lam) hσ1 (fun p : (_ : Idx α) × I => x p.2) :=
    lsumOf_sigma hα' (fun _ => hI) (fun (_ : Idx α) (i : I) => x i) hσ1
  have stepB : lsumOf (lam := lam) hI (fun i => lcmul (lam := lam) α hα (x i))
      = lsumOf (lam := lam) hσ2 (fun q : (_ : I) × Idx α => x q.1) :=
    lsumOf_sigma hI (fun _ => hα') (fun (i : I) (_ : Idx α) => x i) hσ2
  have stepC : lsumOf (lam := lam) hσ2 (fun q : (_ : I) × Idx α => x q.1)
      = lsumOf (lam := lam) hσ1 (fun p : (_ : Idx α) × I => x p.2) :=
    lsumOf_equiv hσ2 hσ1 ((Equiv.sigmaEquivProd (Idx α) I).trans
      ((Equiv.prodComm (Idx α) I).trans (Equiv.sigmaEquivProd I (Idx α)).symm)) _
  rw [stepA, stepB, stepC]

/-- **Lemma 2.7(2)** for a two-term sum of cardinals. -/
theorem lcmul_add {α β : Cardinal.{u}} (hα : α < lam) (hβ : β < lam) (hαβ : α + β < lam) (x : X) :
    lcmul (lam := lam) (α + β) hαβ x
      = lcmul (lam := lam) α hα x + lcmul (lam := lam) β hβ x := by
  have hu : #PUnit.{u + 1} < lam := mk_lt_finite (X := X) _
  have hPP : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) < lam := mk_sum_lt (isRegular' (X := X)) hu hu
  have hcast : ∀ p : PUnit.{u + 1} ⊕ PUnit.{u + 1},
      Sum.elim (fun _ : PUnit.{u + 1} => α) (fun _ : PUnit.{u + 1} => β) p < lam := by
    rintro (p | p)
    · exact hα
    · exact hβ
  have hsum := csum_pair' α β
  calc lcmul (lam := lam) (α + β) hαβ x
      = lcmul (lam := lam) (Cardinal.sum (Sum.elim (fun _ : PUnit.{u + 1} => α)
          fun _ : PUnit.{u + 1} => β)) (lt_of_eq_of_lt hsum hαβ) x := lcmul_congr hsum.symm _ _ x
    _ = lsumOf (lam := lam) hPP (fun p => lcmul (lam := lam) _ (hcast p) x) :=
        lcmul_lsumOf_cardinal hPP _ hcast (lt_of_eq_of_lt hsum hαβ) x
    _ = lcmul (lam := lam) α hα x + lcmul (lam := lam) β hβ x := by
        rw [show (fun p => lcmul (lam := lam) _ (hcast p) x)
            = Sum.elim (fun _ : PUnit.{u + 1} => lcmul (lam := lam) α hα x)
              (fun _ : PUnit.{u + 1} => lcmul (lam := lam) β hβ x) from
          funext fun p => by rcases p with p | p <;> rfl,
          lsumOf_sumType hu hu hPP, lsumOf_unique, lsumOf_unique]

/-- Iterated scaling: `α` copies of `β` copies of `x` is `α * β` copies of `x`. -/
theorem lcmul_lcmul {α β : Cardinal.{u}} (hα : α < lam) (hβ : β < lam) (hαβ : α * β < lam)
    (x : X) :
    lcmul (lam := lam) α hα (lcmul (lam := lam) β hβ x) = lcmul (lam := lam) (α * β) hαβ x := by
  have hα' : #(Idx α) < lam := lt_of_eq_of_lt (mk_Idx α) hα
  have hβ' : #(Idx β) < lam := lt_of_eq_of_lt (mk_Idx β) hβ
  have hmk : #((_ : Idx α) × Idx β) = α * β := by
    rw [Cardinal.mk_congr (Equiv.sigmaEquivProd (Idx α) (Idx β)), Cardinal.mk_prod, mk_Idx,
      mk_Idx, Cardinal.lift_id, Cardinal.lift_id]
  have hσ : #((_ : Idx α) × Idx β) < lam := lt_of_eq_of_lt hmk hαβ
  obtain ⟨Ψ⟩ := Cardinal.eq.mp (hmk.trans (mk_Idx (α * β)).symm)
  calc lcmul (lam := lam) α hα (lcmul (lam := lam) β hβ x)
      = lsumOf (lam := lam) hσ (fun _ : (_ : Idx α) × Idx β => x) :=
        lsumOf_sigma hα' (fun _ => hβ') (fun (_ : Idx α) (_ : Idx β) => x) hσ
    _ = lcmul (lam := lam) (α * β) hαβ x :=
        (lsumOf_equiv (lt_of_eq_of_lt (mk_Idx (α * β)) hαβ) hσ Ψ fun _ => x).symm

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
      = lcmul (lam := lam) α hα a + lcmul (lam := lam) α hα b := by
  have hUB : #(ULift.{u} Bool) < lam := mk_uLift_bool_lt (X := X)
  rw [← lsumOf_two a b hUB,
    lcmul_lsumOf hUB α hα (fun p : ULift.{u} Bool => if p.down then a else b),
    show (fun p : ULift.{u} Bool => lcmul (lam := lam) α hα (if p.down then a else b))
        = fun p : ULift.{u} Bool =>
          if p.down then lcmul (lam := lam) α hα a else lcmul (lam := lam) α hα b from
      funext fun p => by cases p.down <;> rfl]
  exact lsumOf_two _ _ hUB

/-! ### Reducedness (Lemma 2.8) -/

/-- **Lemma 2.8(1)** for `λ⁻`-monoids: a `λ⁻`-monoid with `ℵ₀ < λ` is reduced.

The paper's Eilenberg–Mazur swindle, run with `ℵ₀` in place of `κ`: if `x + y = 0` then
`x = x + ℵ₀·0 = x + ℵ₀(x+y) = (x + ℵ₀x) + ℵ₀y = ℵ₀x + ℵ₀y = ℵ₀(x+y) = 0`.

The hypothesis `ℵ₀ < λ` cannot be dropped: an `ℵ₀⁻`-monoid is an arbitrary commutative
monoid (`LMonoid.ofAddCommMonoid`), and `ℤ` is not reduced. -/
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
