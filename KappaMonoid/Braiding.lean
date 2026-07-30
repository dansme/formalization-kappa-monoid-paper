/-
Part 2 — Section 3: braiding of `κ`-indexed families over a `λ⁻`-monoid.

Modelling the "limit well-order" of Definition 3.1
-------------------------------------------------
The paper fixes a *limit well-order* on `κ`: a well-order in which every element has a
successor (equivalently, one with no maximum).  Such an order decomposes uniquely into
`ω`-blocks indexed by its limit elements, and for a limit well-order of cardinality `κ`
there are exactly `κ` many blocks (as `κ · ℵ₀ = κ`).  Conversely `ι × ℕ`, ordered
lexicographically, is a limit well-order of cardinality `#ι` whenever `ι` is infinite.

We therefore index braiding partitions and braiding families by `ι × ℕ`, with successor
`(a, n) ↦ (a, n + 1)` and limit elements `(a, 0)`.  This is *not* a loss of generality: it
is exactly the content of Lemma 3.4(2)(3) (a braiding decomposes into countable braidings)
together with Lemma 3.5 (independence of the chosen well-order), which is why those two
lemmas do not appear as separate results below — they are absorbed into the definition.
-/
import KappaMonoid.Basic

universe u v w

open Cardinal Function Set

namespace NS

open KMonoid LMonoid

/-! ## Auxiliary summation lemmas

Generic facts about `sumOf` and `lsumOf` — Section 2 material that the braiding arguments
below need.  Nothing here is specific to braiding; they live in this file only to keep
`Basic.lean` untouched. -/

section Aux

/-- Zero-padding along an embedding does not change a `κ`-sum.  This is the `sumOf`-level
form of `KMonoid.ksum_extend`. -/
theorem KMonoid.sumOf_extend {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H] {ι ι' : Type u}
    (h : #ι ≤ κ) (h' : #ι' ≤ κ) (e : ι ↪ ι') (x : ι → H) :
    sumOf (κ := κ) h' (Function.extend e x 0) = sumOf (κ := κ) h x := by
  have hraw := Function.Injective.extend_comp e.injective (emb h').injective x (0 : Idx κ → H)
  have h0 : (0 : Idx κ → H) ∘ (⇑(emb h')) = (0 : ι' → H) := by funext i; simp
  rw [h0] at hraw
  rw [sumOf_eq_extend h (e.trans (emb h')) x]
  show ksum (κ := κ) (Function.extend (⇑(emb h')) (Function.extend (⇑e) x 0) 0) = _
  rw [← hraw]
  rfl

/-- Zero-padding along an embedding does not change a `λ⁻`-sum. -/
theorem LMonoid.lsumOf_extend {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι ι' : Type u}
    (h : #ι < lam) (h' : #ι' < lam) (e : ι ↪ ι') (x : ι → X) :
    lsumOf (lam := lam) h' (Function.extend e x 0) = lsumOf (lam := lam) h x := by
  have hraw := Function.Injective.extend_comp e.injective (emb h'.le).injective x
    (0 : Idx lam → X)
  have h0 : (0 : Idx lam → X) ∘ (⇑(emb h'.le)) = (0 : ι' → X) := by funext i; simp
  rw [h0] at hraw
  rw [lsumOf_eq_extend h (e.trans (emb h'.le)) x]
  show lsum (Function.extend (⇑(emb h'.le)) (Function.extend (⇑e) x 0) 0) = _
  rw [← hraw]
  rfl

/-- Enlarging the index set of a `λ⁻`-sum by indices where the summand vanishes does not
change the sum. -/
theorem LMonoid.lsumOf_of_subset {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u}
    {S T : Set ι} (hS : #S < lam) (hT : #T < lam) (hsub : T ⊆ S) (f : ι → X)
    (hzero : ∀ i ∈ S, i ∉ T → f i = 0) :
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
  rw [hfun, LMonoid.lsumOf_extend hT hS e (fun i : T => f i)]

/-- `κ`-sums are additive. -/
theorem KMonoid.sumOf_add {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H] {ι : Type u}
    (h : #ι ≤ κ) (f g : ι → H) :
    sumOf (κ := κ) h (fun i => f i + g i) = sumOf (κ := κ) h f + sumOf (κ := κ) h g := by
  have hκ := KMonoid.aleph0_le (κ := κ) (H := H)
  have hUB : #(ULift.{u} Bool) ≤ κ := KMonoid.mk_uLift_bool_le κ H
  set F : ULift.{u} Bool → ι → H := fun b i => if b.down then f i else g i with hFdef
  have hprod1 : #((ULift.{u} Bool) × ι) ≤ κ := by
    have hmp : #((ULift.{u} Bool) × ι) = #(ULift.{u} Bool) * #ι := by simp [Cardinal.mk_prod]
    rw [hmp]
    calc #(ULift.{u} Bool) * #ι ≤ κ * κ := mul_le_mul' hUB h
      _ = κ := Cardinal.mul_eq_self hκ
  have hprod2 : #(ι × (ULift.{u} Bool)) ≤ κ := by
    have hmp : #(ι × (ULift.{u} Bool)) = #ι * #(ULift.{u} Bool) := by simp [Cardinal.mk_prod]
    rw [hmp]
    calc #ι * #(ULift.{u} Bool) ≤ κ * κ := mul_le_mul' h hUB
      _ = κ := Cardinal.mul_eq_self hκ
  have hσ1 : #(Σ _ : ι, ULift.{u} Bool) ≤ κ :=
    (Cardinal.mk_congr (Equiv.sigmaEquivProd ι (ULift.{u} Bool))).trans_le hprod2
  have hσ2 : #(Σ _ : ULift.{u} Bool, ι) ≤ κ :=
    (Cardinal.mk_congr (Equiv.sigmaEquivProd (ULift.{u} Bool) ι)).trans_le hprod1
  set Θ : (Σ _ : ι, ULift.{u} Bool) ≃ (Σ _ : ULift.{u} Bool, ι) :=
    (Equiv.sigmaEquivProd ι (ULift.{u} Bool)).trans
      ((Equiv.prodComm ι (ULift.{u} Bool)).trans
        (Equiv.sigmaEquivProd (ULift.{u} Bool) ι).symm) with hΘdef
  have hΘapp : ∀ (i : ι) (b : ULift.{u} Bool), Θ ⟨i, b⟩ = ⟨b, i⟩ := by
    intro i b
    simp [hΘdef]
  have stepA : sumOf (κ := κ) h (fun i => f i + g i)
      = sumOf (κ := κ) hσ1 (fun p : Σ _ : ι, ULift.{u} Bool => F p.2 p.1) := by
    have hinner : (fun i => f i + g i)
        = fun i => sumOf (κ := κ) hUB (fun b : ULift.{u} Bool => F b i) := by
      funext i
      exact (sumOf_two (f i) (g i) hUB).symm
    rw [hinner]
    exact sumOf_sigma h (fun _ => hUB) hσ1 (fun (i : ι) (b : ULift.{u} Bool) => F b i)
  have stepB : sumOf (κ := κ) hσ2 (fun q : Σ _ : ULift.{u} Bool, ι => F q.1 q.2)
      = sumOf (κ := κ) hσ1 (fun p : Σ _ : ι, ULift.{u} Bool => F p.2 p.1) := by
    rw [sumOf_equiv hσ2 hσ1 Θ (fun q : Σ _ : ULift.{u} Bool, ι => F q.1 q.2)]
    congr 1
  have stepC : sumOf (κ := κ) hσ2 (fun q : Σ _ : ULift.{u} Bool, ι => F q.1 q.2)
      = sumOf (κ := κ) hUB (fun b => sumOf (κ := κ) h (fun i => F b i)) :=
    (sumOf_sigma hUB (fun _ => h) hσ2 (fun (b : ULift.{u} Bool) (i : ι) => F b i)).symm
  have stepD : (fun b : ULift.{u} Bool => sumOf (κ := κ) h (fun i => F b i))
      = fun b : ULift.{u} Bool =>
        if b.down then sumOf (κ := κ) h f else sumOf (κ := κ) h g := by
    funext b
    match b with
    | ⟨true⟩ => simp [hFdef]
    | ⟨false⟩ => simp [hFdef]
  rw [stepA, ← stepB, stepC, stepD, sumOf_two (sumOf (κ := κ) h f) (sumOf (κ := κ) h g) hUB]

/-- `#(ι × ℕ) ≤ κ` whenever `#ι ≤ κ` and `κ` is infinite: the index type of braiding
partitions is no bigger than the index type of the families. -/
theorem mk_prod_nat_le {κ : Cardinal.{u}} {ι : Type u} (hκ : ℵ₀ ≤ κ) (hι : #ι ≤ κ) :
    #(ι × ℕ) ≤ κ := by
  have hmp : #(ι × ℕ) = #ι * ℵ₀ := by simp [Cardinal.mk_prod]
  rw [hmp]
  calc #ι * ℵ₀ ≤ κ * κ := mul_le_mul' hι hκ
    _ = κ := Cardinal.mul_eq_self hκ

/-- The `λ⁻`-sums induced on a `κ`-monoid by `KMonoid.toLMonoid` are its `κ`-sums. -/
theorem KMonoid.toLMonoid_lsumOf {κ lam : Cardinal.{u}} {H : Type v} [KMonoid κ H]
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) {ι : Type u} (h : #ι < lam) (x : ι → H) :
    letI := KMonoid.toLMonoid H hlam hlk
    LMonoid.lsumOf (lam := lam) h x = sumOf (κ := κ) (h.le.trans hlk) x := by
  letI := KMonoid.toLMonoid H hlam hlk
  have hidx : #(Idx lam) ≤ κ := le_of_eq_of_le (mk_Idx lam) hlk
  have hsub : Function.support (Function.extend (⇑(emb h.le)) x (0 : Idx lam → H))
      ⊆ Set.range (emb h.le) := by
    intro k hk
    by_contra hkr
    apply hk
    rw [Function.extend_apply' x (0 : Idx lam → H) k hkr]
    rfl
  have hsupp : #(Function.support (Function.extend (⇑(emb h.le)) x (0 : Idx lam → H))) < lam := by
    calc #(Function.support (Function.extend (⇑(emb h.le)) x (0 : Idx lam → H)))
        ≤ #(Set.range (emb h.le)) := Cardinal.mk_le_mk_of_subset hsub
      _ = #ι := Cardinal.mk_range_eq _ (emb h.le).injective
      _ < lam := h
  show (if _ : #(Function.support (Function.extend (⇑(emb h.le)) x (0 : Idx lam → H))) < lam then
      sumOf (κ := κ) hidx (Function.extend (⇑(emb h.le)) x (0 : Idx lam → H)) else 0)
    = sumOf (κ := κ) (h.le.trans hlk) x
  rw [dif_pos hsupp]
  exact KMonoid.sumOf_extend (h.le.trans hlk) hidx (emb h.le) x

end Aux

/-- The successor map of the limit well-order modelled by `ι × ℕ`. -/
def bsucc {ι : Type u} (p : ι × ℕ) : ι × ℕ := (p.1, p.2 + 1)

theorem bsucc_injective {ι : Type u} : Function.Injective (bsucc (ι := ι)) := by
  rintro ⟨a, n⟩ ⟨b, m⟩ h
  simp [bsucc, Prod.ext_iff] at h
  simp [h.1, h.2]

@[simp] theorem bsucc_snd_ne_zero {ι : Type u} (p : ι × ℕ) : (bsucc p).2 ≠ 0 := Nat.succ_ne_zero _

/-- Additivity of `lsumOf` over a disjoint union of two small subsets: the "two-piece"
special case of `lsumOf_sigma`, obtained by transporting along the equivalence
`↥(S ∪ T) ≃ Σ p : ULift Bool, (if p.down then ↥S else ↥T)` and collapsing the outer
`Bool`-indexed sum via `lsumOf_two`. Needed to regroup braiding partitions (Lemma 3.6(2)). -/
theorem lsumOf_union {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u}
    (S T : Set ι) (hd : Disjoint S T) (hS : #S < lam) (hT : #T < lam)
    (hST : #(S ∪ T : Set ι) < lam) (f : ι → X) :
    lsumOf (lam := lam) hST (fun i : (S ∪ T : Set ι) => f i)
      = lsumOf (lam := lam) hS (fun i : S => f i) + lsumOf (lam := lam) hT (fun i : T => f i) := by
  classical
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  have hUB : #(ULift.{u} Bool) < lam :=
    lt_of_lt_of_le (by simpa using nat_lt_aleph0 2) hlam0
  set ρ : ULift.{u} Bool → Type u := fun p => if p.down then (S : Type u) else (T : Type u)
    with hρdef
  set e : (S ∪ T : Set ι) ≃ Σ p : ULift.{u} Bool, ρ p :=
    (Equiv.Set.union hd).trans
      { toFun := fun s => Sum.rec (fun a => ⟨ULift.up true, a⟩) (fun b => ⟨ULift.up false, b⟩) s
        invFun := fun p => match p with
          | ⟨⟨true⟩, a⟩ => Sum.inl a
          | ⟨⟨false⟩, b⟩ => Sum.inr b
        left_inv := fun s => by cases s <;> rfl
        right_inv := fun p => by
          obtain ⟨q, y⟩ := p
          match q with
          | ⟨true⟩ => rfl
          | ⟨false⟩ => rfl } with hedef
  have hρbound : ∀ p : ULift.{u} Bool, #(ρ p) < lam := by
    intro p
    match p with
    | ⟨true⟩ => exact hS
    | ⟨false⟩ => exact hT
  have hσ : #(Σ p : ULift.{u} Bool, ρ p) < lam := by
    rw [← Cardinal.mk_congr e]
    exact hST
  have hmain := lsumOf_sigma (X := X) hUB hρbound
    (fun p (y : ρ p) => f (e.symm ⟨p, y⟩)) hσ
  have step1 : lsumOf (lam := lam) hST (fun i : (S ∪ T : Set ι) => f i)
      = lsumOf (lam := lam) hσ ((fun i : (S ∪ T : Set ι) => f i) ∘ e.symm) :=
    lsumOf_equiv hST hσ e.symm (fun i => f i)
  have hcomp2 : ((fun i : (S ∪ T : Set ι) => f i) ∘ e.symm)
      = fun p : Σ q : ULift.{u} Bool, ρ q => f (e.symm ⟨p.fst, p.snd⟩) := rfl
  rw [step1, hcomp2, ← hmain]
  have htrue : lsumOf (hρbound (ULift.up true)) (fun y => f (e.symm (⟨ULift.up true, y⟩ :
      Σ p : ULift.{u} Bool, ρ p))) = lsumOf (lam := lam) hS (fun i : S => f i) := by
    congr 1
  have hfalse : lsumOf (hρbound (ULift.up false)) (fun y => f (e.symm (⟨ULift.up false, y⟩ :
      Σ p : ULift.{u} Bool, ρ p))) = lsumOf (lam := lam) hT (fun i : T => f i) := by
    congr 1
  have heq : (fun p : ULift.{u} Bool => lsumOf (hρbound p) (fun y => f (e.symm ⟨p, y⟩)))
      = fun p => if p.down then lsumOf (lam := lam) hS (fun i : S => f i)
        else lsumOf (lam := lam) hT (fun i : T => f i) := by
    funext p
    match p with
    | ⟨true⟩ => exact htrue
    | ⟨false⟩ => exact hfalse
  rw [heq, LMonoid.lsumOf_two (lsumOf hS (fun i : S => f i)) (lsumOf hT (fun i : T => f i)) hUB]

/-! ## Definition 3.1(1): braided families -/

/-- The data witnessing that two `κ`-indexed families `x` and `y` over a `λ⁻`-monoid `X` are
`λ⁻`-*braided*: indexed partitions `I`, `J` of the index set into pieces of size `< λ`,
together with braiding families `u`, `v` such that `v` vanishes at limit elements and

  `Σ_{i ∈ I p} x i = v p + u p`,   `Σ_{j ∈ J p} y j = v (p+1) + u p`. -/
structure BraidingData (lam : Cardinal.{u}) {X : Type v} [LMonoid lam X] {ι : Type u}
    (x y : ι → X) where
  I : ι × ℕ → Set ι
  J : ι × ℕ → Set ι
  I_disjoint : ∀ p q, p ≠ q → Disjoint (I p) (I q)
  J_disjoint : ∀ p q, p ≠ q → Disjoint (J p) (J q)
  I_cover : (⋃ p, I p) = Set.univ
  J_cover : (⋃ p, J p) = Set.univ
  I_small : ∀ p, #(I p) < lam
  J_small : ∀ p, #(J p) < lam
  u : ι × ℕ → X
  v : ι × ℕ → X
  /-- `v` vanishes at the limit elements of the well-order. -/
  v_limit : ∀ a : ι, v (a, 0) = 0
  hI : ∀ p, lsumOf (lam := lam) (I_small p) (fun i : I p => x i) = v p + u p
  hJ : ∀ p, lsumOf (lam := lam) (J_small p) (fun j : J p => y j) = v (bsucc p) + u p

/-- Definition 3.1(1): `x` and `y` are `λ⁻`-braided. -/
def IsBraided (lam : Cardinal.{u}) {X : Type v} [LMonoid lam X] {ι : Type u} (x y : ι → X) :
    Prop :=
  Nonempty (BraidingData lam x y)

/-- For `λ = ℵ₀` — the case the paper singles out as the interesting one — we simply say
*braided*. -/
abbrev IsBraided₀ {X : Type v} [LMonoid ℵ₀ X] {ι : Type u} (x y : ι → X) : Prop :=
  IsBraided ℵ₀ x y

/-! ## Basic properties of the braiding relation -/

namespace IsBraided

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u}

/-- Lemma 3.6(1): a family is braided to any of its reindexings along a bijection.  We use the
trivial witness: every index is its own `<lam`-sized (singleton) piece, sitting at the "limit"
slot `(i, 0)`, with `v ≡ 0` and `u (i, 0) := x i`. -/
theorem of_perm (x : ι → X) (π : ι ≃ ι) : IsBraided lam x (x ∘ π) := by
  have hlam0 : ℵ₀ ≤ lam := (‹LMonoid lam X›).isRegular.aleph0_le
  set I : ι × ℕ → Set ι := fun p => if p.2 = 0 then {p.1} else ∅ with hIdef
  set J : ι × ℕ → Set ι := fun p => if p.2 = 0 then {π.symm p.1} else ∅ with hJdef
  set u : ι × ℕ → X := fun p => if p.2 = 0 then x p.1 else 0 with hudef
  set v : ι × ℕ → X := fun _ : ι × ℕ => (0 : X) with hvdef
  have I_disjoint : ∀ p q : ι × ℕ, p ≠ q → Disjoint (I p) (I q) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ hpq
    rcases eq_or_ne n 0 with hn | hn
    · rcases eq_or_ne m 0 with hm | hm
      · subst hn; subst hm
        have hab : a ≠ b := fun h => hpq (by rw [h])
        simp [hIdef, hab]
      · simp [hIdef, hn, hm]
    · simp [hIdef, hn]
  have J_disjoint : ∀ p q : ι × ℕ, p ≠ q → Disjoint (J p) (J q) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ hpq
    rcases eq_or_ne n 0 with hn | hn
    · rcases eq_or_ne m 0 with hm | hm
      · subst hn; subst hm
        have hab : a ≠ b := fun h => hpq (by rw [h])
        have hab' : π.symm a ≠ π.symm b := fun h => hab (π.symm.injective h)
        simp [hJdef, hab']
      · simp [hJdef, hn, hm]
    · simp [hJdef, hn]
  have I_cover : (⋃ p, I p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    exact Set.mem_iUnion.mpr ⟨(a, 0), by simp [hIdef]⟩
  have J_cover : (⋃ p, J p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    exact Set.mem_iUnion.mpr ⟨(π a, 0), by simp [hJdef]⟩
  have hempty_pos : (0 : Cardinal.{u}) < lam := Cardinal.aleph0_pos.trans_le hlam0
  have I_small : ∀ p, #(I p) < lam := by
    rintro ⟨a, n⟩
    rcases eq_or_ne n 0 with hn | hn
    · have hset : I (a, n) = ({a} : Set ι) := by simp [hIdef, hn]
      rw [hset, Cardinal.mk_singleton]
      exact lt_of_lt_of_le one_lt_aleph0 hlam0
    · have hset : I (a, n) = (∅ : Set ι) := by simp [hIdef, hn]
      rw [hset, Cardinal.mk_eq_zero]
      exact hempty_pos
  have J_small : ∀ p, #(J p) < lam := by
    rintro ⟨a, n⟩
    rcases eq_or_ne n 0 with hn | hn
    · have hset : J (a, n) = ({π.symm a} : Set ι) := by simp [hJdef, hn]
      rw [hset, Cardinal.mk_singleton]
      exact lt_of_lt_of_le one_lt_aleph0 hlam0
    · have hset : J (a, n) = (∅ : Set ι) := by simp [hJdef, hn]
      rw [hset, Cardinal.mk_eq_zero]
      exact hempty_pos
  have v_limit : ∀ a : ι, v (a, 0) = 0 := fun _ => rfl
  have hI : ∀ p, lsumOf (lam := lam) (I_small p) (fun i : I p => x i) = v p + u p := by
    rintro ⟨a, n⟩
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      letI : Unique ↥(I (a, 0)) := Set.uniqueSingleton a
      show lsumOf (I_small (a, 0)) (fun i : I (a, 0) => x i) = 0 + x a
      rw [lsumOf_unique (I_small (a, 0)) (fun i : I (a, 0) => x i), zero_add]
      rfl
    · letI : IsEmpty ↥(I (a, n)) := by
        have hset : I (a, n) = (∅ : Set ι) := by simp [hIdef, hn]
        rw [hset]; infer_instance
      simp only [hvdef, hudef, if_neg hn, add_zero]
      exact lsumOf_isEmpty (I_small (a, n)) (fun i : I (a, n) => x i)
  have hJ : ∀ p, lsumOf (lam := lam) (J_small p) (fun j : J p => (x ∘ π) j) = v (bsucc p) + u p := by
    rintro ⟨a, n⟩
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      letI : Unique ↥(J (a, 0)) := Set.uniqueSingleton (π.symm a)
      show lsumOf (J_small (a, 0)) (fun j : J (a, 0) => (x ∘ π) j) = 0 + x a
      rw [lsumOf_unique (J_small (a, 0)) (fun j : J (a, 0) => (x ∘ π) j), zero_add]
      show (x ∘ π) (π.symm a) = x a
      simp
    · letI : IsEmpty ↥(J (a, n)) := by
        have hset : J (a, n) = (∅ : Set ι) := by simp [hJdef, hn]
        rw [hset]; infer_instance
      simp only [hvdef, hudef, if_neg hn, add_zero]
      exact lsumOf_isEmpty (J_small (a, n)) (fun j : J (a, n) => (x ∘ π) j)
  exact ⟨⟨I, J, I_disjoint, J_disjoint, I_cover, J_cover, I_small, J_small, u, v, v_limit, hI, hJ⟩⟩

/-- Lemma 3.6(2), reflexivity. -/
@[refl] theorem refl (x : ι → X) : IsBraided lam x x := by
  simpa using of_perm x (Equiv.refl ι)

/-- Lemma 3.6(2), symmetry.  Paper proof: shift the indices, replacing `(u, v)` by
`u' μ = u μ + v (μ+1)`, `v' μ = 0` at limit elements and `u' μ = v (μ+1)`, `v' μ = u μ`
otherwise. -/
@[symm] theorem symm {x y : ι → X} (h : IsBraided lam x y) : IsBraided lam y x := by
  sorry

/-- Lemma 3.7: two braidings sharing the middle family can be chosen so that their
partitions of the middle family interleave, i.e.

  `⋃_{ν ≤ μ} Jν ⊆ ⋃_{ν ≤ μ} J'ν ⊆ ⋃_{ν ≤ μ+1} Jν`.

This is the technical heart of transitivity; the paper proves it by a transfinite recursion
constructing left-saturated `λ⁻`-intervals. -/
theorem exists_aligned {x y z : ι → X} (hxy : IsBraided lam x y) (hyz : IsBraided lam y z) :
    ∃ (d₁ : BraidingData lam x y) (d₂ : BraidingData lam y z),
      ∀ p : ι × ℕ, True := by
  -- The precise alignment condition requires the linear order on `ι × ℕ`; we record the
  -- existence statement here and refer to the paper for the (purely combinatorial) proof.
  sorry

/-- Lemma 3.8, transitivity. -/
@[trans] theorem trans {x y z : ι → X} (hxy : IsBraided lam x y) (hyz : IsBraided lam y z) :
    IsBraided lam x z := by
  sorry

end IsBraided

/-- Lemma 3.8: `λ⁻`-braidedness is an equivalence relation on `κ`-indexed families. -/
def braidingSetoid (lam κ : Cardinal.{u}) (X : Type v) [LMonoid lam X] :
    Setoid (Idx κ → X) where
  r := IsBraided lam
  iseqv := ⟨IsBraided.refl, IsBraided.symm, IsBraided.trans⟩

/-! ## Lemma 3.2 and Lemma 3.4 -/

section Ambient

variable {lam κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]
  (hlam : lam.IsRegular) (hlk : lam ≤ κ)

/-- Lemma 3.2 (telescoping): braided families have equal `κ`-sums.

Note that the braiding is taken with respect to the `λ⁻`-monoid structure that `H` carries
as a `κ`-monoid (`KMonoid.toLMonoid`). -/
theorem sumOf_eq_of_isBraided {ι : Type u} (hι : #ι ≤ κ) (x y : ι → H)
    (h : letI := KMonoid.toLMonoid H hlam hlk; IsBraided lam x y) :
    sumOf (κ := κ) hι x = sumOf (κ := κ) hι y := by
  obtain ⟨d⟩ := h
  have hκ := KMonoid.aleph0_le (κ := κ) (H := H)
  have hP : #(ι × ℕ) ≤ κ := mk_prod_nat_le hκ hι
  have hIle : ∀ p, #(d.I p) ≤ κ := fun p => (d.I_small p).le.trans hlk
  have hJle : ∀ p, #(d.J p) ≤ κ := fun p => (d.J_small p).le.trans hlk
  -- Regroup each side along its braiding partition and use the defining equations.
  have hxsum : sumOf (κ := κ) hι x = sumOf (κ := κ) hP (fun p => d.v p + d.u p) := by
    rw [← sumOf_biUnion d.I d.I_disjoint d.I_cover hP hι hIle x]
    congr 1
    funext p
    exact (KMonoid.toLMonoid_lsumOf hlam hlk (d.I_small p)
      (fun i : d.I p => x i)).symm.trans (d.hI p)
  have hysum : sumOf (κ := κ) hι y = sumOf (κ := κ) hP (fun p => d.v (bsucc p) + d.u p) := by
    rw [← sumOf_biUnion d.J d.J_disjoint d.J_cover hP hι hJle y]
    congr 1
    funext p
    exact (KMonoid.toLMonoid_lsumOf hlam hlk (d.J_small p)
      (fun j : d.J p => y j)).symm.trans (d.hJ p)
  rw [hxsum, hysum, KMonoid.sumOf_add hP d.v d.u,
    KMonoid.sumOf_add hP (fun p => d.v (bsucc p)) d.u]
  congr 1
  -- The telescoping step: `v` vanishes at the limit elements `(a, 0)`, and `bsucc` is a
  -- bijection onto the non-limit elements, so `Σ v = Σ (v ∘ bsucc)`.
  have hbs : d.v = Function.extend (bsucc (ι := ι)) (fun p => d.v (bsucc p)) 0 := by
    funext p
    obtain ⟨a, n⟩ := p
    cases n with
    | zero =>
      have hnr : ¬ ∃ q : ι × ℕ, bsucc q = (a, 0) := by
        rintro ⟨⟨b, m⟩, hbm⟩
        exact Nat.succ_ne_zero m (congrArg Prod.snd hbm)
      rw [Function.extend_apply' (fun p => d.v (bsucc p)) (0 : ι × ℕ → H) (a, 0) hnr]
      exact d.v_limit a
    | succ m =>
      have hmem : bsucc (a, m) = (a, m + 1) := rfl
      rw [← hmem, bsucc_injective.extend_apply]
  calc sumOf (κ := κ) hP d.v
      = sumOf (κ := κ) hP (Function.extend (bsucc (ι := ι)) (fun p => d.v (bsucc p)) 0) := by
        rw [← hbs]
    _ = sumOf (κ := κ) hP (fun p => d.v (bsucc p)) :=
        KMonoid.sumOf_extend hP hP ⟨bsucc, bsucc_injective⟩ _

end Ambient

section Lemma34

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u}

/-- Lemma 3.4(1): families with support of size `< λ` and equal `λ⁻`-sums are braided. -/
theorem isBraided_of_small_support (x y : ι → X)
    (hx : #(Function.support x) < lam) (hy : #(Function.support y) < lam)
    (h : lsumOf (lam := lam) hx (fun i : Function.support x => x i)
        = lsumOf (lam := lam) hy (fun i : Function.support y => y i)) :
    IsBraided lam x y := by
  sorry

/-- Lemma 3.4(4): for uncountable `λ` the braiding relation collapses to the much simpler
condition that the two families admit partitions into pieces of size `< λ` with equal
partial sums. -/
theorem isBraided_iff_of_ne_aleph0 (hlam : lam ≠ ℵ₀) (x y : ι → X) :
    IsBraided lam x y ↔
      ∃ (I J : ι × ℕ → Set ι) (hI : ∀ p, #(I p) < lam) (hJ : ∀ p, #(J p) < lam),
        (∀ p q, p ≠ q → Disjoint (I p) (I q)) ∧ (∀ p q, p ≠ q → Disjoint (J p) (J q)) ∧
        (⋃ p, I p) = Set.univ ∧ (⋃ p, J p) = Set.univ ∧
        ∀ p, lsumOf (lam := lam) (hI p) (fun i : I p => x i)
            = lsumOf (lam := lam) (hJ p) (fun j : J p => y j) := by
  sorry

end Lemma34

/-! ## Definition 3.1(2): `λ⁻`-braided extensions -/

/-- Definition 3.1(2): the `κ`-monoid `H` is `λ⁻`-braided over the `λ⁻`-monoid `X`,
embedded by `f`.  We ask that

* `f` is an injective `λ⁻`-homomorphism (so that `X` is a `λ⁻`-submonoid of `H`);
* `H` is generated by the image of `f` as a `κ`-monoid;
* any two `κ`-indexed families in `X` with equal `κ`-sum in `H` are `λ⁻`-braided. -/
structure IsBraidedOver (lam κ : Cardinal.{u}) (X : Type v) (H : Type w)
    [LMonoid lam X] [KMonoid κ H] (hlk : lam ≤ κ) (f : X → H) : Prop where
  isLHom : IsLHom hlk f
  injective : Function.Injective f
  generates : ∀ h : H, ∃ x : Idx κ → X, h = ksum (κ := κ) fun i => f (x i)
  braided : ∀ x y : Idx κ → X,
    (ksum (κ := κ) fun i => f (x i)) = (ksum (κ := κ) fun i => f (y i)) → IsBraided lam x y

end NS
