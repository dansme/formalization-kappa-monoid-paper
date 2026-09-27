/-
Auxiliary lemmas on `λ⁻`-sums, braidings and `λ⁻`-homomorphisms, used by Proposition 3.10 and
the construction of the universal `κ`-extension.
-/
import KappaMonoid.Braiding.Over

universe u v w z

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid


/-! ## Auxiliary lemmas on `λ⁻`-sums and braidings -/

section Aux

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X]

/-- Braiding is invariant under reindexing both families along one and the same
bijection of index types. -/
theorem IsBraided.reindex {ι ι' : Type u} {x y : ι → X} (e : ι' ≃ ι)
    (h : IsBraided lam x y) : IsBraided lam (x ∘ e) (y ∘ e) := by
  obtain ⟨d⟩ := h
  have hpre : ∀ S : Set ι, #(↥(e ⁻¹' S)) = #S := fun S =>
    Cardinal.mk_congr (e.subtypeEquiv (fun _ => Iff.rfl))
  have hsum : ∀ (S : Set ι) (hS : #S < lam) (hS' : #(↥(e ⁻¹' S)) < lam) (g : ι → X),
      ∑[lam] i ∈ e ⁻¹' S, (g ∘ e) i
        = ∑[lam] i ∈ S, g i := by
    intro S hS hS' g
    exact (lsumOf_equiv (e.subtypeEquiv (fun _ => Iff.rfl)) (fun i : S => g i) hS).symm
  have hcover : ∀ (K : ι × ℕ → Set ι), (⋃ p, K p) = Set.univ →
      (⋃ p : ι' × ℕ, e ⁻¹' K (e p.1, p.2)) = Set.univ := by
    intro K hK
    apply Set.eq_univ_of_forall
    intro i'
    obtain ⟨⟨a, n⟩, ha⟩ := Set.mem_iUnion.mp (hK ▸ Set.mem_univ (e i'))
    refine Set.mem_iUnion.mpr ⟨(e.symm a, n), ?_⟩
    show e i' ∈ K (e (e.symm a), n)
    rw [Equiv.apply_symm_apply]
    exact ha
  have hdisj : ∀ (K : ι × ℕ → Set ι), (∀ p q, p ≠ q → Disjoint (K p) (K q)) →
      ∀ p q : ι' × ℕ, p ≠ q → Disjoint (e ⁻¹' K (e p.1, p.2)) (e ⁻¹' K (e q.1, q.2)) := by
    intro K hK p q hpq
    refine Disjoint.preimage e (hK _ _ ?_)
    intro hcon
    have h1 := Prod.ext_iff.mp hcon
    exact hpq (Prod.ext (e.injective h1.1) h1.2)
  exact ⟨{ I := fun p => e ⁻¹' d.I (e p.1, p.2)
           J := fun p => e ⁻¹' d.J (e p.1, p.2)
           I_disjoint := hdisj d.I d.I_disjoint
           J_disjoint := hdisj d.J d.J_disjoint
           I_cover := hcover d.I d.I_cover
           J_cover := hcover d.J d.J_cover
           I_small := fun p => (hpre _).trans_lt (d.I_small _)
           J_small := fun p => (hpre _).trans_lt (d.J_small _)
           u := fun p => d.u (e p.1, p.2)
           v := fun p => d.v (e p.1, p.2)
           v_limit := fun a => d.v_limit (e a)
           hI := fun p => by
             rw [hsum (d.I (e p.1, p.2)) (d.I_small _) _ x]; exact d.hI _
           hJ := fun p => by
             rw [hsum (d.J (e p.1, p.2)) (d.J_small _) _ y]; exact d.hJ _ }⟩

/-- Braidings can be concatenated: a family of braidings indexed by `A` yields a braiding
of the concatenated families indexed by `A × B`. -/
theorem IsBraided.prod {A B : Type u} {x y : A → B → X} (h : ∀ a, IsBraided lam (x a) (y a)) :
    IsBraided lam (fun p : A × B => x p.1 p.2) (fun p : A × B => y p.1 p.2) := by
  have d : ∀ a, BraidingData lam (x a) (y a) := fun a => (h a).some
  have hinj : ∀ a : A, Function.Injective (Prod.mk a : B → A × B) :=
    fun a i j hij => congrArg Prod.snd hij
  -- the pieces: the `a`-th braiding lives on the slice `{a} × B`
  have hdisj : ∀ (K : ∀ a, B × ℕ → Set B), (∀ a p q, p ≠ q → Disjoint (K a p) (K a q)) →
      ∀ p q : (A × B) × ℕ, p ≠ q →
        Disjoint (Prod.mk p.1.1 '' K p.1.1 (p.1.2, p.2)) (Prod.mk q.1.1 '' K q.1.1 (q.1.2, q.2)) := by
    rintro K hK ⟨⟨a, b⟩, n⟩ ⟨⟨a', b'⟩, n'⟩ hpq
    by_cases haa : a = a'
    · subst haa
      refine Set.disjoint_image_of_injective (hinj a) (hK a _ _ ?_)
      intro hcon
      obtain ⟨hb, hn⟩ := Prod.ext_iff.mp hcon
      simp only at hb hn
      exact hpq (by subst hb; subst hn; rfl)
    · rw [Set.disjoint_left]
      rintro ⟨c, i⟩ ⟨i1, _, hi1⟩ ⟨i2, _, hi2⟩
      have e1 : a = c := congrArg Prod.fst hi1
      have e2 : a' = c := congrArg Prod.fst hi2
      exact haa (e1.trans e2.symm)
  have hcover : ∀ (K : ∀ a, B × ℕ → Set B), (∀ a, (⋃ p, K a p) = Set.univ) →
      (⋃ p : (A × B) × ℕ, Prod.mk p.1.1 '' K p.1.1 (p.1.2, p.2)) = Set.univ := by
    intro K hK
    apply Set.eq_univ_of_forall
    rintro ⟨a, i⟩
    obtain ⟨⟨b, n⟩, hb⟩ := Set.mem_iUnion.mp ((hK a) ▸ Set.mem_univ i)
    exact Set.mem_iUnion.mpr ⟨((a, b), n), ⟨i, hb, rfl⟩⟩
  have hsmall : ∀ (a : A) (S : Set B), #(↥(Prod.mk a '' S)) = #S := fun a S =>
    Cardinal.mk_image_eq (hinj a)
  have hsum : ∀ (a : A) (S : Set B) (hS : #S < lam) (hS' : #(↥(Prod.mk a '' S)) < lam)
      (g : A → B → X),
      ∑[lam] p ∈ Prod.mk a '' S, g (p : A × B).1 (p : A × B).2
        = ∑[lam] i ∈ S, g a i := by
    intro a S hS hS' g
    exact lsumOf_equiv (Equiv.Set.image (Prod.mk a) S (hinj a))
      (fun p : ↥(Prod.mk a '' S) => g (p : A × B).1 (p : A × B).2) hS'
  exact ⟨{ I := fun p => Prod.mk p.1.1 '' (d p.1.1).I (p.1.2, p.2)
           J := fun p => Prod.mk p.1.1 '' (d p.1.1).J (p.1.2, p.2)
           I_disjoint := hdisj (fun a => (d a).I) (fun a => (d a).I_disjoint)
           J_disjoint := hdisj (fun a => (d a).J) (fun a => (d a).J_disjoint)
           I_cover := hcover (fun a => (d a).I) (fun a => (d a).I_cover)
           J_cover := hcover (fun a => (d a).J) (fun a => (d a).J_cover)
           I_small := fun p => (hsmall _ _).trans_lt ((d p.1.1).I_small _)
           J_small := fun p => (hsmall _ _).trans_lt ((d p.1.1).J_small _)
           u := fun p => (d p.1.1).u (p.1.2, p.2)
           v := fun p => (d p.1.1).v (p.1.2, p.2)
           v_limit := fun a => (d a.1).v_limit a.2
           hI := fun p => by
             rw [hsum p.1.1 _ ((d p.1.1).I_small (p.1.2, p.2)) _ x]; exact (d p.1.1).hI _
           hJ := fun p => by
             rw [hsum p.1.1 _ ((d p.1.1).J_small (p.1.2, p.2)) _ y]; exact (d p.1.1).hJ _ }⟩

/-- **Braiding from an aggregation.**  Suppose the index set carries pairwise disjoint `< λ`-small
sets `A a`, one for each `a : ι`, such that `x` sums over `A a` to `y a` and vanishes outside
`⋃ A`.  Then `x` and `y` are braided.

The `BraidingData` is the obvious one: `A a` against `{a}` on level `0`, and the indices no `A a`
covers — where `x` vanishes — parked on level `1` against the empty set.  Both braidings needed for
Proposition 3.10 are of this shape, with `A a` a one- or two-element set. -/
theorem of_aggregation {ι : Type u} {x y : ι → X} (A : ι → Set ι)
    (hdisj : ∀ a b, a ≠ b → Disjoint (A a) (A b)) (hsmall : ∀ a, #(A a) < lam)
    (hzero : ∀ i, i ∉ ⋃ a, A a → x i = 0)
    (hsum : ∀ a, ∑[lam] i ∈ A a, x i = y a) :
    IsBraided lam x y := by
  classical
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  have hfin : ∀ S : Set ι, S.Finite → #S < lam := fun S hS =>
    lt_of_lt_of_le (lt_aleph0_iff_set_finite.mpr hS) hlam0
  set U : Set ι := ⋃ a, A a with hUdef
  set I : ι × ℕ → Set ι :=
    fun p => if p.2 = 0 then A p.1 else if p.2 = 1 then {p.1} \ U else ∅ with hIdef
  set J : ι × ℕ → Set ι := fun p => if p.2 = 0 then {p.1} else ∅ with hJdef
  have hI0 : ∀ a : ι, I (a, 0) = A a := fun _ => rfl
  have hI1 : ∀ a : ι, I (a, 1) = {a} \ U := fun _ => rfl
  have hI2 : ∀ (a : ι) (m : ℕ), I (a, m + 2) = ∅ := fun _ _ => rfl
  have hJ0 : ∀ a : ι, J (a, 0) = {a} := fun _ => rfl
  have hJn : ∀ (a : ι) (m : ℕ), J (a, m + 1) = ∅ := fun _ _ => rfl
  have hmemU : ∀ (a : ι) (i : ι), i ∈ A a → i ∈ U := fun a i hi => Set.mem_iUnion.mpr ⟨a, hi⟩
  have hIsmall : ∀ p, #(I p) < lam := by
    rintro ⟨a, n⟩
    match n with
    | 0 => rw [hI0 a]; exact hsmall a
    | 1 => rw [hI1 a]; exact hfin _ ((Set.finite_singleton a).subset Set.sdiff_subset)
    | (m + 2) => rw [hI2 a m]; exact hfin _ Set.finite_empty
  have hJsmall : ∀ p, #(J p) < lam := by
    rintro ⟨a, n⟩
    match n with
    | 0 => rw [hJ0 a]; exact hfin _ (Set.finite_singleton _)
    | (m + 1) => rw [hJn a m]; exact hfin _ Set.finite_empty
  have hIchar : ∀ (a : ι) (n : ℕ) (i : ι), i ∈ I (a, n) →
      (n = 0 ∧ i ∈ A a) ∨ (n = 1 ∧ i = a ∧ i ∉ U) := by
    intro a n i hi
    match n with
    | 0 => exact Or.inl ⟨rfl, hi⟩
    | 1 => exact Or.inr ⟨rfl, hi.1, hi.2⟩
    | (m + 2) => exact absurd hi (by rw [hI2 a m]; exact Set.notMem_empty i)
  have hIdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ hpq
    rw [Set.disjoint_left]
    intro i hi hj
    rcases hIchar a n i hi with ⟨hn, hia⟩ | ⟨hn, hia, hiU⟩ <;>
      rcases hIchar b m i hj with ⟨hm, hib⟩ | ⟨hm, hib, hiU'⟩
    · have hab : a = b := by
        by_contra hc
        exact Set.disjoint_left.mp (hdisj a b hc) hia hib
      exact hpq (by subst hn; subst hm; subst hab; rfl)
    · exact hiU' (hmemU a i hia)
    · exact hiU (hmemU b i hib)
    · have hab : a = b := hia.symm.trans hib
      exact hpq (by subst hn; subst hm; subst hab; rfl)
  have hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ hpq
    rw [Set.disjoint_left]
    intro i hi hj
    match n, m with
    | 0, 0 =>
      have hia : i = a := hi
      have hib : i = b := hj
      exact hpq (by subst hia; subst hib; rfl)
    | 0, (m + 1) => exact absurd hj (by rw [hJn b m]; exact Set.notMem_empty i)
    | (n + 1), _ => exact absurd hi (by rw [hJn a n]; exact Set.notMem_empty i)
  have hIcover : (⋃ p, I p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    by_cases hi : i ∈ U
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hi
      exact Set.mem_iUnion.mpr ⟨(a, 0), by rw [hI0 a]; exact ha⟩
    · exact Set.mem_iUnion.mpr ⟨(i, 1), by rw [hI1 i]; exact ⟨rfl, hi⟩⟩
  have hJcover : (⋃ p, J p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    exact Set.mem_iUnion.mpr ⟨(i, 0), by rw [hJ0 i]; rfl⟩
  refine IsBraided.of_partition I J hIdisj hJdisj hIcover hJcover hIsmall hJsmall ?_
  rintro ⟨a, n⟩
  match n with
  | 0 =>
    let : Unique ↥(J (a, 0)) := Set.uniqueSingleton a
    rw [lsumOf_unique (hJsmall (a, 0)) (fun i : J (a, 0) => y i)]
    exact (hsum a).trans rfl
  | 1 =>
    have hL : ∑[lam] i ∈ I (a, 1), x i = 0 := by
      refine LMonoid.lsumOf_eq_zero (hIsmall (a, 1)) x (fun i hi => ?_)
      rw [hI1 a] at hi
      exact hzero i hi.2
    have hR : ∑[lam] i ∈ J (a, 1), y i = 0 :=
      LMonoid.lsumOf_eq_zero (hJsmall (a, 1)) y (fun i hi => absurd hi (Set.notMem_empty i))
    rw [hL, hR]
  | (m + 2) =>
    have hL : ∑[lam] i ∈ I (a, m + 2), x i = 0 :=
      LMonoid.lsumOf_eq_zero (hIsmall (a, m + 2)) x
        (fun i hi => absurd hi (Set.notMem_empty i))
    have hR : ∑[lam] i ∈ J (a, m + 2), y i = 0 :=
      LMonoid.lsumOf_eq_zero (hJsmall (a, m + 2)) y (fun i hi => absurd hi (Set.notMem_empty i))
    rw [hL, hR]

/-- Zero-padding a family along an embedding of the index type into itself produces a
braided family. -/
theorem isBraided_extend {ι : Type u} (e : ι ↪ ι) (w : ι → X) :
    IsBraided lam (Function.extend e w 0) w := by
  classical
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  have hsmall : ∀ a : ι, #({e a} : Set ι) < lam := fun a =>
    lt_of_lt_of_le (lt_aleph0_iff_set_finite.mpr (Set.finite_singleton _)) hlam0
  refine of_aggregation (fun a => {e a})
    (fun a b hab => Set.disjoint_singleton.mpr fun h => hab (e.injective h)) hsmall
    (fun i hi => ?_) (fun a => ?_)
  · exact Function.extend_apply' w (0 : ι → X) i
      (fun ⟨c, hc⟩ => hi (Set.mem_iUnion.mpr ⟨c, hc.symm⟩))
  · let : Unique ↥({e a} : Set ι) := Set.uniqueSingleton (e a)
    rw [lsumOf_unique (hsmall a) (fun i : ({e a} : Set ι) => Function.extend e w 0 i)]
    show Function.extend e w 0 (e a) = w a
    exact e.injective.extend_apply w 0 a

/-- Merging two families along embeddings with disjoint ranges realises their pointwise
sum. -/
theorem isBraided_merge {ι : Type u} (e₀ e₁ : ι ↪ ι) (hdisj : ∀ i j, e₀ i ≠ e₁ j)
    (x y : ι → X) :
    IsBraided lam (fun i => x i + y i)
      (fun j => Function.extend e₀ x 0 j + Function.extend e₁ y 0 j) := by
  classical
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  set M : ι → X := fun j => Function.extend e₀ x 0 j + Function.extend e₁ y 0 j with hMdef
  -- the values of the merged family
  have hM0 : ∀ a, M (e₀ a) = x a := by
    intro a
    show Function.extend e₀ x 0 (e₀ a) + Function.extend e₁ y 0 (e₀ a) = x a
    rw [e₀.injective.extend_apply,
      Function.extend_apply' y (0 : ι → X) (e₀ a) (fun ⟨c, hc⟩ => hdisj a c hc.symm)]
    exact add_zero _
  have hM1 : ∀ a, M (e₁ a) = y a := by
    intro a
    show Function.extend e₀ x 0 (e₁ a) + Function.extend e₁ y 0 (e₁ a) = y a
    rw [e₁.injective.extend_apply,
      Function.extend_apply' x (0 : ι → X) (e₁ a) (fun ⟨c, hc⟩ => hdisj c a hc)]
    exact zero_add _
  have hsmall : ∀ a : ι, #({e₀ a, e₁ a} : Set ι) < lam := fun a =>
    lt_of_lt_of_le (lt_aleph0_iff_set_finite.mpr ((Set.finite_singleton _).insert _)) hlam0
  refine IsBraided.symm (of_aggregation (fun a => {e₀ a, e₁ a}) (fun a b hab => ?_)
    hsmall (fun i hi => ?_) (fun a => ?_))
  · -- the pairs are disjoint: both embeddings are injective and their ranges do not meet
    rw [Set.disjoint_left]
    rintro i (rfl | rfl) (h | h)
    · exact hab (e₀.injective h)
    · exact hdisj a b h
    · exact hdisj b a h.symm
    · exact hab (e₁.injective h)
  · -- outside the two ranges the merged family vanishes
    show Function.extend e₀ x 0 i + Function.extend e₁ y 0 i = 0
    rw [Function.extend_apply' x (0 : ι → X) i
        (fun ⟨c, hc⟩ => hi (Set.mem_iUnion.mpr ⟨c, Or.inl hc.symm⟩)),
      Function.extend_apply' y (0 : ι → X) i
        (fun ⟨c, hc⟩ => hi (Set.mem_iUnion.mpr ⟨c, Or.inr hc.symm⟩))]
    exact add_zero _
  · rw [LMonoid.lsumOf_pair (hdisj a a) M (hsmall a), hM0 a, hM1 a]

/-- Variant of `isBraided_of_small_support` where the supports are replaced by arbitrary
small sets containing them. -/
theorem isBraided_of_small_sets {ι : Type u} {x y : ι → X} {S T : Set ι}
    (hS : #S < lam) (hT : #T < lam) (hx : ∀ i ∉ S, x i = 0) (hy : ∀ i ∉ T, y i = 0)
    (h : ∑[lam] i ∈ S, x i
      = ∑[lam] i ∈ T, y i) :
    IsBraided lam x y := by
  have hxsub : Function.support x ⊆ S := by
    intro i hi
    by_contra hiS
    exact hi (hx i hiS)
  have hysub : Function.support y ⊆ T := by
    intro i hi
    by_contra hiT
    exact hi (hy i hiT)
  have hxs : #(Function.support x) < lam :=
    lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hxsub) hS
  have hys : #(Function.support y) < lam :=
    lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hysub) hT
  refine isBraided_of_small_support x y hxs hys ?_
  rw [← LMonoid.lsumOf_of_subset hS hxs hxsub x (fun i _ hi => by
        by_contra hc; exact hi hc),
    ← LMonoid.lsumOf_of_subset hT hys hysub y (fun i _ hi => by
        by_contra hc; exact hi hc)]
  exact h

end Aux

section AuxHom

variable {lam κ : Cardinal.{u}} {X : Type v} {H : Type w} [LMonoid lam X] [KMonoid κ H]

/-- A `λ⁻`-homomorphism is additive: `+` is a `λ⁻`-sum over a two-element index type. -/
theorem IsLHom.map_add (hlk : lam ≤ Order.succ κ) {f : X → H} (hf : IsLHom hlk f) (a b : X) :
    f (a + b) = f a + f b := by
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  have hUB : #(ULift.{u} Bool) < lam := lt_of_lt_of_le (by simp) hlam0
  have h1 := hf.2 hUB (fun p : ULift.{u} Bool => if p.down then a else b)
  rw [LMonoid.lsumOf_two a b hUB] at h1
  have h2 : (f ∘ fun p : ULift.{u} Bool => if p.down then a else b)
      = fun p : ULift.{u} Bool => if p.down then f a else f b := by
    funext p
    match p with
    | ⟨true⟩ => rfl
    | ⟨false⟩ => rfl
  rw [h1, h2, sumOf_two (f a) (f b) (le_of_lt_of_le_succ hlk hUB)]

/-- A `λ⁻`-homomorphism into a `κ`-monoid is a homomorphism of `λ⁻`-monoids for the induced
structure — the two notions differ only in how the target's sums are packaged. -/
theorem isLMonoidHom_of_isLHom (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ) {f : X → H}
    (hf : IsLHom hlk f) :
    letI := KMonoid.toLMonoidOfLE H hlam hlk
    IsLMonoidHom lam f := by
  let := KMonoid.toLMonoidOfLE H hlam hlk
  intro ι h x
  rw [KMonoid.toLMonoidOfLE_lsumOf hlam hlk h (f ∘ x)]
  exact hf.2 h x

/-- The converse of `IsLHom.isLMonoidHom`. -/
theorem isLHom_of_isLMonoidHom (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ) {f : X → H}
    (hf : letI := KMonoid.toLMonoidOfLE H hlam hlk
      IsLMonoidHom lam f) : IsLHom hlk f := by
  let := KMonoid.toLMonoidOfLE H hlam hlk
  refine ⟨hf.map_zero, fun {ι} h x => ?_⟩
  rw [hf h x]
  exact (KMonoid.toLMonoidOfLE_lsumOf hlam hlk h (f ∘ x)).symm

/-- A `λ⁻`-homomorphism carries braided families to braided families. -/
theorem IsBraided.map_lhom (hlk : lam ≤ Order.succ κ) {f : X → H} (hf : IsLHom hlk f) {ι : Type u}
    {x y : ι → X} (h : IsBraided lam x y) :
    letI := KMonoid.toLMonoidOfLE H (‹LMonoid lam X›.isRegular) hlk
    IsBraided lam (f ∘ x) (f ∘ y) := by
  have hlam : lam.IsRegular := ‹LMonoid lam X›.isRegular
  let := KMonoid.toLMonoidOfLE H hlam hlk
  obtain ⟨d⟩ := h
  have hpush : ∀ {S : Set ι} (hS : #S < lam) (g : ι → X),
      ∑[lam] i ∈ S, (f ∘ g) i = f (∑[lam] i ∈ S, g i) := by
    intro S hS g
    rw [KMonoid.toLMonoidOfLE_lsumOf hlam hlk hS (fun i : S => (f ∘ g) i), hf.2 hS (fun i : S => g i)]
    rfl
  exact ⟨{ I := d.I
           J := d.J
           I_disjoint := d.I_disjoint
           J_disjoint := d.J_disjoint
           I_cover := d.I_cover
           J_cover := d.J_cover
           I_small := d.I_small
           J_small := d.J_small
           u := fun p => f (d.u p)
           v := fun p => f (d.v p)
           v_limit := fun a => by rw [d.v_limit a, hf.1]
           hI := fun p => by
             rw [hpush (d.I_small p) x, d.hI p, IsLHom.map_add hlk hf]
           hJ := fun p => by
             rw [hpush (d.J_small p) y, d.hJ p, IsLHom.map_add hlk hf] }⟩

/-- The telescoping principle in the form needed for Proposition 3.10: a `λ⁻`-homomorphism
into a `κ`-monoid takes braided families to families with equal `κ`-sums. -/
theorem sumOf_map_eq_of_isBraided (hlk : lam ≤ Order.succ κ) {f : X → H} (hf : IsLHom hlk f)
    {ι : Type u} (hι : #ι ≤ κ) {x y : ι → X} (h : IsBraided lam x y) :
    sumOf (κ := κ) hι (f ∘ x) = sumOf (κ := κ) hι (f ∘ y) := by
  let := KMonoid.toLMonoidOfLE H (‹LMonoid lam X›.isRegular) hlk
  exact sumOf_eq_of_isBraided (‹LMonoid lam X›.isRegular) hlk hι _ _ (h.map_lhom hlk hf)

end AuxHom

/-! ## Padding a braiding by zeros -/

section Padding

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X]

/-- **Padding a braiding by zeros.**  If two families vanish outside a set `C` of indices and
their restrictions to `C` are `λ⁻`-braided, then so are the families themselves: the pieces of
the braiding on `C` are kept at the slots named by elements of `C`, and every index outside `C`
is parked alone at its own limit slot, against itself.  (This is the converse of restricting a
braiding to a set containing both supports, and is what lets a braiding of countable families be
used inside an uncountable index set.) -/
theorem isBraided_of_subtype {ι : Type u} (C : Set ι) {x y : ι → X}
    (hx : ∀ i ∉ C, x i = 0) (hy : ∀ i ∉ C, y i = 0)
    (h : IsBraided lam (fun c : C => x c) (fun c : C => y c)) : IsBraided lam x y := by
  classical
  obtain ⟨d⟩ := h
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  -- the padded pieces and the padded braiding families
  let pad : (C × ℕ → Set C) → ι × ℕ → Set ι := fun P p =>
    if h : p.1 ∈ C then Subtype.val '' P (⟨p.1, h⟩, p.2) else if p.2 = 0 then {p.1} else ∅
  let padV : (C × ℕ → X) → ι × ℕ → X := fun w p =>
    if h : p.1 ∈ C then w (⟨p.1, h⟩, p.2) else 0
  have hpos : ∀ P (p : ι × ℕ) (h : p.1 ∈ C), pad P p = Subtype.val '' P (⟨p.1, h⟩, p.2) :=
    fun P p h => dif_pos h
  have hneg : ∀ P (p : ι × ℕ), p.1 ∉ C → pad P p ⊆ {p.1} := by
    intro P p h i hi
    simp only [pad, dif_neg h] at hi
    split_ifs at hi
    · exact hi
    · exact absurd hi (Set.notMem_empty i)
  have hneg0 : ∀ P (a : ι), a ∉ C → pad P (a, 0) = {a} := by
    intro P a h
    show (if h' : a ∈ C then _ else if (0 : ℕ) = 0 then ({a} : Set ι) else ∅) = {a}
    rw [dif_neg h, if_pos rfl]
  have hVpos : ∀ w (p : ι × ℕ) (h : p.1 ∈ C), padV w p = w (⟨p.1, h⟩, p.2) :=
    fun w p h => dif_pos h
  have hVneg : ∀ w (p : ι × ℕ), p.1 ∉ C → padV w p = 0 := fun w p h => dif_neg h
  have hdisj : ∀ P : C × ℕ → Set C, (∀ p q, p ≠ q → Disjoint (P p) (P q)) →
      ∀ p q, p ≠ q → Disjoint (pad P p) (pad P q) := by
    intro P hP p q hpq
    rw [Set.disjoint_left]
    intro i hip hiq
    by_cases hp : p.1 ∈ C <;> by_cases hq : q.1 ∈ C
    · rw [hpos P p hp] at hip
      rw [hpos P q hq] at hiq
      obtain ⟨c, hc, rfl⟩ := hip
      obtain ⟨c', hc', hcc'⟩ := hiq
      have hc'eq : c' = c := Subtype.ext hcc'
      subst hc'eq
      have hne : ((⟨p.1, hp⟩ : C), p.2) ≠ (⟨q.1, hq⟩, q.2) := by
        intro heq
        obtain ⟨h1, h2⟩ := Prod.ext_iff.mp heq
        exact hpq (Prod.ext (congrArg Subtype.val h1) h2)
      exact Set.disjoint_left.mp (hP _ _ hne) hc hc'
    · rw [hpos P p hp] at hip
      obtain ⟨c, _, rfl⟩ := hip
      have := hneg P q hq hiq
      rw [Set.mem_singleton_iff] at this
      exact hq (this ▸ c.2)
    · rw [hpos P q hq] at hiq
      obtain ⟨c, _, rfl⟩ := hiq
      have := hneg P p hp hip
      rw [Set.mem_singleton_iff] at this
      exact hp (this ▸ c.2)
    · have h1 := hneg P p hp hip
      have h2 := hneg P q hq hiq
      rw [Set.mem_singleton_iff] at h1 h2
      have hp0 : p.2 = 0 := by
        by_contra h0
        simp only [pad, dif_neg hp, if_neg h0] at hip
        exact hip
      have hq0 : q.2 = 0 := by
        by_contra h0
        simp only [pad, dif_neg hq, if_neg h0] at hiq
        exact hiq
      exact hpq (Prod.ext (h1.symm.trans h2) (hp0.trans hq0.symm))
  have hcov : ∀ P : C × ℕ → Set C, (⋃ p, P p) = Set.univ → (⋃ p, pad P p) = Set.univ := by
    intro P hP
    refine Set.eq_univ_of_forall fun i => Set.mem_iUnion.mpr ?_
    by_cases hi : i ∈ C
    · obtain ⟨⟨c, n⟩, hc⟩ := Set.mem_iUnion.mp (hP ▸ Set.mem_univ (⟨i, hi⟩ : C))
      refine ⟨((c : ι), n), ?_⟩
      rw [hpos P ((c : ι), n) c.2]
      exact ⟨⟨i, hi⟩, hc, rfl⟩
    · exact ⟨(i, 0), by rw [hneg0 P i hi]; rfl⟩
  have hsmall : ∀ P : C × ℕ → Set C, (∀ p, #(P p) < lam) → ∀ p, #(pad P p) < lam := by
    intro P hP p
    by_cases hp : p.1 ∈ C
    · rw [hpos P p hp]
      exact lt_of_le_of_lt Cardinal.mk_image_le (hP _)
    · exact lt_of_lt_of_le (Cardinal.lt_aleph0_iff_set_finite.mpr
        ((Set.finite_singleton _).subset (hneg P p hp))) hlam0
  -- sums over the padded pieces
  have hsumpos : ∀ (P : C × ℕ → Set C) (hP : ∀ p, #(P p) < lam) (z : ι → X) (p : ι × ℕ)
      (hp : p.1 ∈ C), ∑[lam] i ∈ pad P p, z i
        = ∑[lam] c ∈ P (⟨p.1, hp⟩, p.2), z c := by
    intro P hP z p hp
    have hcongr : ∀ (S T : Set ι) (hST : S = T) (hS : #S < lam) (hT : #T < lam),
        ∑[lam] i ∈ S, z i = ∑[lam] i ∈ T, z i := by
      rintro S T rfl hS hT
      rfl
    have himg : #(Subtype.val '' P (⟨p.1, hp⟩, p.2)) < lam :=
      lt_of_le_of_lt Cardinal.mk_image_le (hP _)
    rw [hcongr _ _ (hpos P p hp) (hsmall P hP p) himg,
      lsumOf_equiv (Equiv.Set.image Subtype.val _ Subtype.val_injective) _ himg]
    rfl
  have hsumneg : ∀ (P : C × ℕ → Set C) (hP : ∀ p, #(P p) < lam) (z : ι → X)
      (hz : ∀ i ∉ C, z i = 0) (p : ι × ℕ) (hp : p.1 ∉ C),
      ∑[lam] i ∈ pad P p, z i = 0 := by
    intro P hP z hz p hp
    refine LMonoid.lsumOf_eq_zero _ z fun i hi => hz i ?_
    have := hneg P p hp hi
    rw [Set.mem_singleton_iff] at this
    exact this ▸ hp
  refine ⟨{ I := pad d.I
            J := pad d.J
            I_disjoint := hdisj d.I d.I_disjoint
            J_disjoint := hdisj d.J d.J_disjoint
            I_cover := hcov d.I d.I_cover
            J_cover := hcov d.J d.J_cover
            I_small := hsmall d.I d.I_small
            J_small := hsmall d.J d.J_small
            u := padV d.u
            v := padV d.v
            v_limit := fun a => ?_
            hI := fun p => ?_
            hJ := fun p => ?_ }⟩
  · by_cases ha : a ∈ C
    · rw [hVpos d.v (a, 0) ha]
      exact d.v_limit _
    · exact hVneg d.v (a, 0) ha
  · by_cases hp : p.1 ∈ C
    · rw [hsumpos d.I d.I_small x p hp, hVpos d.v p hp, hVpos d.u p hp]
      exact d.hI _
    · rw [hsumneg d.I d.I_small x hx p hp, hVneg d.v p hp, hVneg d.u p hp, add_zero]
  · by_cases hp : p.1 ∈ C
    · rw [hsumpos d.J d.J_small y p hp, hVpos d.v (bsucc p) hp, hVpos d.u p hp]
      exact d.hJ _
    · rw [hsumneg d.J d.J_small y hy p hp, hVneg d.v (bsucc p) hp, hVneg d.u p hp, add_zero]

end Padding

end KappaMonoid
