/-
Part 3 — Section 3.1: universal `κ`-extensions.

Contents:
* auxiliary lemmas on braidings (`IsBraided.reindex`, `IsBraided.prod`, `isBraided_extend`,
  `isBraided_merge`) and on `λ⁻`-homomorphisms (`IsLHom.map_add`, `IsBraided.map_lhom`);
* `KMonoid.extend_lhom` — Proposition 3.9;
* `IsUniversalKExtension` — Definition 3.10;
* `universalExtension` — the construction `Ĥ = X^κ / (λ⁻-braiding)` of Theorem 3.11;
* `theorem_3_11` — Theorem 3.11, **with the hypothesis `IsConical X` added**;
* `isConical_of_isUniversalKExtension` — the reason that hypothesis is needed.

The missing hypothesis
----------------------
Theorem 3.11(1) as printed asserts, for an arbitrary `λ⁻`-monoid `H`, the existence of a
`κ`-monoid `Ĥ ⊇ H` which is a `λ⁻`-overmonoid of `H`.  This cannot hold in general: by
Lemma 2.8(1) every `κ`-monoid is reduced, and a `λ⁻`-submonoid of a reduced monoid is
reduced.  For `λ = ℵ₀` a `λ⁻`-monoid is just a commutative monoid, so e.g. `H = ℤ` admits
no such `Ĥ`.  (For `λ > ℵ₀` the analogue of Lemma 2.8 makes reducedness automatic, so the
gap only concerns `λ = ℵ₀`; the paper's Example 2.3(1) already notes that reducedness is
needed there.)

Adding `IsConical H` repairs the statement, and it is exactly the right hypothesis: it is
also *necessary* (`isConical_of_isUniversalKExtension`), and it is what makes the canonical
map `H → Ĥ` injective — see `UnivExt.of_injective`.

The construction
----------------
`Ĥ = X^κ / (λ⁻-braiding)` carries:
* the *pointwise* addition of families (`UnivExt.addQ`); this descends to the quotient by
  `UnivExt.isBraided_add`, which compares a pointwise sum with the concatenation of the two
  families placed in two disjoint rows of `κ × κ` (`isBraided_merge`);
* the `κ`-sum given by concatenating representatives along a bijection `κ × κ ≃ κ`
  (`UnivExt.ksumQ`); this is well defined because braidings concatenate
  (`IsBraided.prod`), and axioms (A1), (A2) reduce to `isBraided_extend` and to invariance
  of braiding under permutations of the index set (`IsBraided.of_perm`).

Since the `AddCommMonoid` structure is the pointwise one, all monoid axioms are inherited
from `X^κ`; only the two `κ`-monoid axioms need braiding arguments.
-/
import KappaMonoid.Braiding

universe u v w

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
      lsumOf (lam := lam) hS' (fun i : ↥(e ⁻¹' S) => (g ∘ e) i)
        = lsumOf (lam := lam) hS (fun i : S => g i) := by
    intro S hS hS' g
    exact (lsumOf_equiv hS hS' (e.subtypeEquiv (fun _ => Iff.rfl)) (fun i : S => g i)).symm
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
      lsumOf (lam := lam) hS' (fun p : ↥(Prod.mk a '' S) => g (p : A × B).1 (p : A × B).2)
        = lsumOf (lam := lam) hS (fun i : S => g a i) := by
    intro a S hS hS' g
    exact lsumOf_equiv hS' hS (Equiv.Set.image (Prod.mk a) S (hinj a))
      (fun p : ↥(Prod.mk a '' S) => g (p : A × B).1 (p : A × B).2)
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

/-- Zero-padding a family along an embedding of the index type into itself produces a
braided family. -/
theorem isBraided_extend {ι : Type u} (e : ι ↪ ι) (w : ι → X) :
    IsBraided lam (Function.extend e w 0) w := by
  classical
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  have hfin : ∀ S : Set ι, S.Finite → #S < lam := fun S hS =>
    lt_of_lt_of_le (lt_aleph0_iff_set_finite.mpr hS) hlam0
  set R : Set ι := Set.range e with hRdef
  set I : ι × ℕ → Set ι :=
    fun p => if p.2 = 0 then {e p.1} else if p.2 = 1 then {p.1} \ R else ∅ with hIdef
  set J : ι × ℕ → Set ι := fun p => if p.2 = 0 then {p.1} else ∅ with hJdef
  have hI0 : ∀ a : ι, I (a, 0) = {e a} := fun _ => rfl
  have hI1 : ∀ a : ι, I (a, 1) = {a} \ R := fun _ => rfl
  have hI2 : ∀ (a : ι) (m : ℕ), I (a, m + 2) = ∅ := fun _ _ => rfl
  have hJ0 : ∀ a : ι, J (a, 0) = {a} := fun _ => rfl
  have hJn : ∀ (a : ι) (m : ℕ), J (a, m + 1) = ∅ := fun _ _ => rfl
  have hIchar : ∀ (a : ι) (n : ℕ) (i : ι), i ∈ I (a, n) →
      (n = 0 ∧ i = e a) ∨ (n = 1 ∧ i = a ∧ i ∉ R) := by
    intro a n i hi
    match n with
    | 0 => exact Or.inl ⟨rfl, hi⟩
    | 1 => exact Or.inr ⟨rfl, hi.1, hi.2⟩
    | (m + 2) => exact absurd hi (by rw [hI2 a m]; exact Set.notMem_empty i)
  have hIsmall : ∀ p, #(I p) < lam := by
    rintro ⟨a, n⟩
    match n with
    | 0 => rw [hI0 a]; exact hfin _ (Set.finite_singleton _)
    | 1 => rw [hI1 a]; exact hfin _ ((Set.finite_singleton a).subset Set.sdiff_subset)
    | (m + 2) => rw [hI2 a m]; exact hfin _ Set.finite_empty
  have hJsmall : ∀ p, #(J p) < lam := by
    rintro ⟨a, n⟩
    match n with
    | 0 => rw [hJ0 a]; exact hfin _ (Set.finite_singleton _)
    | (m + 1) => rw [hJn a m]; exact hfin _ Set.finite_empty
  have hIdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ hpq
    rw [Set.disjoint_left]
    intro i hi hj
    rcases hIchar a n i hi with ⟨hn, hia⟩ | ⟨hn, hia, hiR⟩ <;>
      rcases hIchar b m i hj with ⟨hm, hib⟩ | ⟨hm, hib, hiR'⟩
    · have hab : a = b := e.injective (hia.symm.trans hib)
      exact hpq (by subst hn; subst hm; subst hab; rfl)
    · exact hiR' ⟨a, hia.symm⟩
    · exact hiR ⟨b, hib.symm⟩
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
    by_cases hi : i ∈ R
    · obtain ⟨a, ha⟩ := hi
      exact Set.mem_iUnion.mpr ⟨(a, 0), by rw [hI0 a]; exact ha.symm⟩
    · exact Set.mem_iUnion.mpr ⟨(i, 1), by rw [hI1 i]; exact ⟨rfl, hi⟩⟩
  have hJcover : (⋃ p, J p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    exact Set.mem_iUnion.mpr ⟨(i, 0), by rw [hJ0 i]; rfl⟩
  refine IsBraided.of_partition I J hIdisj hJdisj hIcover hJcover hIsmall hJsmall ?_
  rintro ⟨a, n⟩
  match n with
  | 0 =>
    letI : Unique ↥(I (a, 0)) := Set.uniqueSingleton (e a)
    letI : Unique ↥(J (a, 0)) := Set.uniqueSingleton a
    rw [lsumOf_unique (hIsmall (a, 0)) (fun i : I (a, 0) => Function.extend e w 0 i),
      lsumOf_unique (hJsmall (a, 0)) (fun i : J (a, 0) => w i)]
    show Function.extend e w 0 (e a) = w a
    exact e.injective.extend_apply w 0 a
  | 1 =>
    have hL : lsumOf (lam := lam) (hIsmall (a, 1))
        (fun i : I (a, 1) => Function.extend e w 0 i) = 0 := by
      refine LMonoid.lsumOf_eq_zero (hIsmall (a, 1)) (Function.extend e w 0) (fun i hi => ?_)
      rw [hI1 a] at hi
      exact Function.extend_apply' w (0 : ι → X) i (fun ⟨c, hc⟩ => hi.2 ⟨c, hc⟩)
    have hR : lsumOf (lam := lam) (hJsmall (a, 1)) (fun i : J (a, 1) => w i) = 0 :=
      LMonoid.lsumOf_eq_zero (hJsmall (a, 1)) w (fun i hi => absurd hi (Set.notMem_empty i))
    rw [hL, hR]
  | (m + 2) =>
    have hL : lsumOf (lam := lam) (hIsmall (a, m + 2))
        (fun i : I (a, m + 2) => Function.extend e w 0 i) = 0 :=
      LMonoid.lsumOf_eq_zero (hIsmall (a, m + 2)) (Function.extend e w 0)
        (fun i hi => absurd hi (Set.notMem_empty i))
    have hR : lsumOf (lam := lam) (hJsmall (a, m + 2)) (fun i : J (a, m + 2) => w i) = 0 :=
      LMonoid.lsumOf_eq_zero (hJsmall (a, m + 2)) w (fun i hi => absurd hi (Set.notMem_empty i))
    rw [hL, hR]

/-- Merging two families along embeddings with disjoint ranges realises their pointwise
sum. -/
theorem isBraided_merge {ι : Type u} (e₀ e₁ : ι ↪ ι) (hdisj : ∀ i j, e₀ i ≠ e₁ j)
    (x y : ι → X) :
    IsBraided lam (fun i => x i + y i)
      (fun j => Function.extend e₀ x 0 j + Function.extend e₁ y 0 j) := by
  classical
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  have hfin : ∀ S : Set ι, S.Finite → #S < lam := fun S hS =>
    lt_of_lt_of_le (lt_aleph0_iff_set_finite.mpr hS) hlam0
  set M : ι → X := fun j => Function.extend e₀ x 0 j + Function.extend e₁ y 0 j with hMdef
  set R : Set ι := Set.range e₀ ∪ Set.range e₁ with hRdef
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
  have hMout : ∀ j, j ∉ R → M j = 0 := by
    intro j hj
    show Function.extend e₀ x 0 j + Function.extend e₁ y 0 j = 0
    rw [Function.extend_apply' x (0 : ι → X) j (fun ⟨c, hc⟩ => hj (Or.inl ⟨c, hc⟩)),
      Function.extend_apply' y (0 : ι → X) j (fun ⟨c, hc⟩ => hj (Or.inr ⟨c, hc⟩))]
    exact add_zero _
  set I : ι × ℕ → Set ι := fun p => if p.2 = 0 then {p.1} else ∅ with hIdef
  set J : ι × ℕ → Set ι :=
    fun p => if p.2 = 0 then {e₀ p.1, e₁ p.1} else if p.2 = 1 then {p.1} \ R else ∅ with hJdef
  have hI0 : ∀ a : ι, I (a, 0) = {a} := fun _ => rfl
  have hIn : ∀ (a : ι) (m : ℕ), I (a, m + 1) = ∅ := fun _ _ => rfl
  have hJ0 : ∀ a : ι, J (a, 0) = {e₀ a, e₁ a} := fun _ => rfl
  have hJ1 : ∀ a : ι, J (a, 1) = {a} \ R := fun _ => rfl
  have hJ2 : ∀ (a : ι) (m : ℕ), J (a, m + 2) = ∅ := fun _ _ => rfl
  have hJchar : ∀ (a : ι) (n : ℕ) (i : ι), i ∈ J (a, n) →
      (n = 0 ∧ (i = e₀ a ∨ i = e₁ a)) ∨ (n = 1 ∧ i = a ∧ i ∉ R) := by
    intro a n i hi
    match n with
    | 0 => exact Or.inl ⟨rfl, hi⟩
    | 1 => exact Or.inr ⟨rfl, hi.1, hi.2⟩
    | (m + 2) => exact absurd hi (Set.notMem_empty i)
  have hIsmall : ∀ p, #(I p) < lam := by
    rintro ⟨a, n⟩
    match n with
    | 0 => rw [hI0 a]; exact hfin _ (Set.finite_singleton _)
    | (m + 1) => rw [hIn a m]; exact hfin _ Set.finite_empty
  have hJsmall : ∀ p, #(J p) < lam := by
    rintro ⟨a, n⟩
    match n with
    | 0 => rw [hJ0 a]; exact hfin _ ((Set.finite_singleton _).insert _)
    | 1 => rw [hJ1 a]; exact hfin _ ((Set.finite_singleton a).subset Set.sdiff_subset)
    | (m + 2) => rw [hJ2 a m]; exact hfin _ Set.finite_empty
  have hIdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ hpq
    rw [Set.disjoint_left]
    intro i hi hj
    match n, m with
    | 0, 0 =>
      have hia : i = a := hi
      have hib : i = b := hj
      exact hpq (by subst hia; subst hib; rfl)
    | 0, (m + 1) => exact absurd hj (Set.notMem_empty i)
    | (n + 1), _ => exact absurd hi (Set.notMem_empty i)
  have hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ hpq
    rw [Set.disjoint_left]
    intro i hi hj
    rcases hJchar a n i hi with ⟨hn, hia⟩ | ⟨hn, hia, hiR⟩ <;>
      rcases hJchar b m i hj with ⟨hm, hib⟩ | ⟨hm, hib, hiR'⟩
    · have hab : a = b := by
        rcases hia with hia | hia <;> rcases hib with hib | hib
        · exact e₀.injective (hia.symm.trans hib)
        · exact absurd (hia.symm.trans hib) (hdisj a b)
        · exact absurd (hib.symm.trans hia) (hdisj b a)
        · exact e₁.injective (hia.symm.trans hib)
      exact hpq (by subst hn; subst hm; subst hab; rfl)
    · rcases hia with hia | hia
      · exact hiR' (Or.inl ⟨a, hia.symm⟩)
      · exact hiR' (Or.inr ⟨a, hia.symm⟩)
    · rcases hib with hib | hib
      · exact hiR (Or.inl ⟨b, hib.symm⟩)
      · exact hiR (Or.inr ⟨b, hib.symm⟩)
    · have hab : a = b := hia.symm.trans hib
      exact hpq (by subst hn; subst hm; subst hab; rfl)
  have hIcover : (⋃ p, I p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    exact Set.mem_iUnion.mpr ⟨(i, 0), by rw [hI0 i]; rfl⟩
  have hJcover : (⋃ p, J p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    by_cases hi : i ∈ R
    · rcases hi with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact Set.mem_iUnion.mpr ⟨(a, 0), by rw [hJ0 a]; exact Or.inl ha.symm⟩
      · exact Set.mem_iUnion.mpr ⟨(a, 0), by rw [hJ0 a]; exact Or.inr ha.symm⟩
    · exact Set.mem_iUnion.mpr ⟨(i, 1), by rw [hJ1 i]; exact ⟨rfl, hi⟩⟩
  refine IsBraided.of_partition I J hIdisj hJdisj hIcover hJcover hIsmall hJsmall ?_
  rintro ⟨a, n⟩
  match n with
  | 0 =>
    letI : Unique ↥(I (a, 0)) := Set.uniqueSingleton a
    rw [lsumOf_unique (hIsmall (a, 0)) (fun i : I (a, 0) => x i + y i)]
    have hpair : lsumOf (lam := lam) (hJsmall (a, 0)) (fun i : J (a, 0) => M i)
        = M (e₀ a) + M (e₁ a) :=
      LMonoid.lsumOf_pair (hdisj a a) (hJsmall (a, 0)) M
    rw [hpair, hM0 a, hM1 a]
    rfl
  | 1 =>
    have hL : lsumOf (lam := lam) (hIsmall (a, 1)) (fun i : I (a, 1) => x i + y i) = 0 :=
      LMonoid.lsumOf_eq_zero (hIsmall (a, 1)) (fun i => x i + y i)
        (fun i hi => absurd hi (Set.notMem_empty i))
    have hR : lsumOf (lam := lam) (hJsmall (a, 1)) (fun i : J (a, 1) => M i) = 0 := by
      refine LMonoid.lsumOf_eq_zero (hJsmall (a, 1)) M (fun i hi => ?_)
      rw [hJ1 a] at hi
      exact hMout i hi.2
    rw [hL, hR]
  | (m + 2) =>
    have hL : lsumOf (lam := lam) (hIsmall (a, m + 2)) (fun i : I (a, m + 2) => x i + y i) = 0 :=
      LMonoid.lsumOf_eq_zero (hIsmall (a, m + 2)) (fun i => x i + y i)
        (fun i hi => absurd hi (Set.notMem_empty i))
    have hR : lsumOf (lam := lam) (hJsmall (a, m + 2)) (fun i : J (a, m + 2) => M i) = 0 :=
      LMonoid.lsumOf_eq_zero (hJsmall (a, m + 2)) M
        (fun i hi => absurd hi (Set.notMem_empty i))
    rw [hL, hR]

/-- Variant of `isBraided_of_small_support` where the supports are replaced by arbitrary
small sets containing them. -/
theorem isBraided_of_small_sets {ι : Type u} {x y : ι → X} {S T : Set ι}
    (hS : #S < lam) (hT : #T < lam) (hx : ∀ i ∉ S, x i = 0) (hy : ∀ i ∉ T, y i = 0)
    (h : lsumOf (lam := lam) hS (fun i : S => x i)
      = lsumOf (lam := lam) hT (fun i : T => y i)) :
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
theorem IsLHom.map_add (hlk : lam ≤ κ) {f : X → H} (hf : IsLHom hlk f) (a b : X) :
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
  rw [h1, h2, sumOf_two (f a) (f b) (hUB.le.trans hlk)]

/-- A `λ⁻`-homomorphism carries braided families to braided families. -/
theorem IsBraided.map_lhom (hlk : lam ≤ κ) {f : X → H} (hf : IsLHom hlk f) {ι : Type u}
    {x y : ι → X} (h : IsBraided lam x y) :
    letI := KMonoid.toLMonoidOfLE H (‹LMonoid lam X›.isRegular) hlk
    IsBraided lam (f ∘ x) (f ∘ y) := by
  have hlam : lam.IsRegular := ‹LMonoid lam X›.isRegular
  letI := KMonoid.toLMonoidOfLE H hlam hlk
  obtain ⟨d⟩ := h
  have hpush : ∀ {S : Set ι} (hS : #S < lam) (g : ι → X),
      lsumOf (lam := lam) hS (fun i : S => (f ∘ g) i) = f (lsumOf (lam := lam) hS (fun i : S => g i)) := by
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

/-- The telescoping principle in the form needed for Proposition 3.9: a `λ⁻`-homomorphism
into a `κ`-monoid takes braided families to families with equal `κ`-sums. -/
theorem sumOf_map_eq_of_isBraided (hlk : lam ≤ κ) {f : X → H} (hf : IsLHom hlk f)
    {ι : Type u} (hι : #ι ≤ κ) {x y : ι → X} (h : IsBraided lam x y) :
    sumOf (κ := κ) hι (f ∘ x) = sumOf (κ := κ) hι (f ∘ y) := by
  letI := KMonoid.toLMonoidOfLE H (‹LMonoid lam X›.isRegular) hlk
  exact sumOf_eq_of_isBraided (‹LMonoid lam X›.isRegular) hlk hι _ _ (h.map_lhom hlk hf)

end AuxHom

/-! ## Proposition 3.9 -/

variable {lam κ : Cardinal.{u}}

/-- Proposition 3.9: if the `κ`-monoid `H` is `λ⁻`-braided over `X`, then every
`λ⁻`-homomorphism from `X` to a `κ`-monoid `K` extends uniquely to a `κ`-homomorphism on
`H`.

Paper proof: uniqueness is clear since `X` generates `H`.  For existence, well-definedness
of `φ̄ (Σᵢ xᵢ) := Σᵢ φ (xᵢ)` follows by telescoping along a braiding of two representations
`Σᵢ xᵢ = Σⱼ yⱼ`. -/
theorem extend_lhom {X : Type v} {H : Type w} [LMonoid lam X] [KMonoid κ H]
    (hlk : lam ≤ κ) (f : X → H) (hbr : IsBraidedOver lam κ X H hlk f)
    {K : Type w} [KMonoid κ K] (φ : X → K) (hφ : IsLHom hlk φ) :
    ∃! ψ : H → K, IsKHom κ ψ ∧ ∀ x, ψ (f x) = φ x := by
  classical
  have hκ : ℵ₀ ≤ κ := KMonoid.aleph0_le (κ := κ) (H := H)
  have hIdx : #(Idx κ) ≤ κ := le_of_eq (mk_Idx κ)
  choose rep hrep using hbr.generates
  set ψ : H → K := fun h => ksum (κ := κ) (fun i => φ (rep h i)) with hψdef
  -- `ψ` may be computed from an arbitrary representation.
  have key : ∀ (h : H) (x : Idx κ → X), h = ksum (κ := κ) (fun i => f (x i)) →
      ψ h = ksum (κ := κ) (fun i => φ (x i)) := by
    intro h x hx
    have hb : IsBraided lam (rep h) x := hbr.braided _ _ (by rw [← hrep h, ← hx])
    have := sumOf_map_eq_of_isBraided (H := K) hlk hφ hIdx hb
    rwa [sumOf_Idx, sumOf_Idx] at this
  -- `ψ` extends `φ`
  have hext : ∀ a : X, ψ (f a) = φ a := by
    intro a
    obtain ⟨i₀⟩ := nonempty_Idx hκ
    have hrepr : f a = ksum (κ := κ) (fun i => f (if i = i₀ then a else 0)) := by
      have : (fun i => f (if i = i₀ then a else 0)) = fun i => if i = i₀ then f a else 0 := by
        funext i
        by_cases hi : i = i₀ <;> simp [hi, hbr.isLHom.1]
      rw [this, ksum_single i₀ _ (fun i hi => if_neg hi), if_pos rfl]
    rw [key (f a) _ hrepr]
    have : (fun i => φ (if i = i₀ then a else 0)) = fun i => if i = i₀ then φ a else 0 := by
      funext i
      by_cases hi : i = i₀ <;> simp [hi, hφ.1]
    rw [this, ksum_single i₀ _ (fun i hi => if_neg hi), if_pos rfl]
  refine ⟨ψ, ⟨⟨?_, ?_⟩, hext⟩, ?_⟩
  · -- `ψ 0 = 0`
    have h0 : (0 : H) = ksum (κ := κ) (fun _ : Idx κ => f 0) := by
      simp [hbr.isLHom.1, ksum_zero]
    rw [key 0 _ h0]
    simp [hφ.1, ksum_zero]
  · -- `ψ` commutes with `κ`-sums
    intro h
    set x : Idx κ → Idx κ → X := fun i => rep (h i) with hxdef
    set π : Idx κ × Idx κ ≃ Idx κ := pairEquiv hκ with hπdef
    have hflat : ksum (κ := κ) h
        = ksum (κ := κ) (fun k => f (x (π.symm k).1 (π.symm k).2)) := by
      have h1 : (fun i => h i) = fun i => ksum (κ := κ) (fun j => f (x i j)) := by
        funext i; exact hrep (h i)
      calc ksum (κ := κ) h = ksum (κ := κ) (fun i => ksum (κ := κ) (fun j => f (x i j))) := by
            rw [← h1]
        _ = ksum (κ := κ) (fun k => f (x (π.symm k).1 (π.symm k).2)) :=
            ksum_sigma (fun i j => f (x i j)) π
    rw [key _ _ hflat]
    have h2 : (ψ ∘ h) = fun i => ksum (κ := κ) (fun j => φ (x i j)) := by
      funext i
      exact key (h i) (x i) (hrep (h i))
    rw [h2]
    exact (ksum_sigma (fun i j => φ (x i j)) π).symm
  · -- uniqueness
    rintro ψ' ⟨hhom', hext'⟩
    funext h
    have hr := hrep h
    calc ψ' h = ψ' (ksum (κ := κ) (fun i => f (rep h i))) := by rw [← hr]
      _ = ksum (κ := κ) (fun i => ψ' (f (rep h i))) := hhom'.2 _
      _ = ksum (κ := κ) (fun i => φ (rep h i)) := by
          congr 1; funext i; exact hext' _
      _ = ψ h := rfl


/-! ## Definition 3.10 -/

/-- Definition 3.10: `Ĥ` (with structure map `f`) is a *universal `κ`-extension* of the
`λ⁻`-monoid `X`. -/
structure IsUniversalKExtension (lam κ : Cardinal.{u}) (X : Type v) (Hh : Type w)
    [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ κ) (f : X → Hh) : Prop where
  isLHom : IsLHom hlk f
  universal : ∀ (K : Type w) [KMonoid κ K] (φ : X → K), IsLHom hlk φ →
    ∃! ψ : Hh → K, IsKHom κ ψ ∧ ∀ x, ψ (f x) = φ x

/-- A universal `κ`-extension is unique up to a unique isomorphism, as for any object
defined by a universal property. -/
theorem isUniversalKExtension_unique {X : Type v} {H₁ H₂ : Type w}
    [LMonoid lam X] [KMonoid κ H₁] [KMonoid κ H₂] (hlk : lam ≤ κ)
    {f₁ : X → H₁} {f₂ : X → H₂}
    (h₁ : IsUniversalKExtension lam κ X H₁ hlk f₁)
    (h₂ : IsUniversalKExtension lam κ X H₂ hlk f₂) :
    ∃! e : H₁ → H₂, IsKHom κ e ∧ (∀ x, e (f₁ x) = f₂ x) ∧ Function.Bijective e := by
  have hcomp : ∀ {A B C : Type w} [KMonoid κ A] [KMonoid κ B] [KMonoid κ C] (g : A → B) (h : B → C),
      IsKHom κ g → IsKHom κ h → IsKHom κ (fun a => h (g a)) := by
    intro A B C _ _ _ g h hg hh
    refine ⟨by show h (g 0) = 0; rw [hg.1, hh.1], fun x => ?_⟩
    show h (g (ksum (κ := κ) x)) = ksum (κ := κ) (fun i => h (g (x i)))
    rw [hg.2 x, hh.2 (g ∘ x)]
    rfl
  have hid : ∀ {A : Type w} [KMonoid κ A], IsKHom κ (fun a : A => a) :=
    fun {A} _ => ⟨rfl, fun _ => rfl⟩
  obtain ⟨e12, ⟨he12hom, he12⟩, hu12⟩ := h₁.universal H₂ f₂ h₂.isLHom
  obtain ⟨e21, ⟨he21hom, he21⟩, _⟩ := h₂.universal H₁ f₁ h₁.isLHom
  obtain ⟨w₁, _, hw₁⟩ := h₁.universal H₁ f₁ h₁.isLHom
  obtain ⟨w₂, _, hw₂⟩ := h₂.universal H₂ f₂ h₂.isLHom
  have hleft : ∀ a, e21 (e12 a) = a := by
    have hA : (fun a => e21 (e12 a)) = w₁ :=
      hw₁ _ ⟨hcomp e12 e21 he12hom he21hom, fun x => by
        show e21 (e12 (f₁ x)) = f₁ x
        rw [he12 x, he21 x]⟩
    have hB : (fun a : H₁ => a) = w₁ := hw₁ _ ⟨hid, fun _ => rfl⟩
    exact fun a => congrFun (hA.trans hB.symm) a
  have hright : ∀ b, e12 (e21 b) = b := by
    have hA : (fun b => e12 (e21 b)) = w₂ :=
      hw₂ _ ⟨hcomp e21 e12 he21hom he12hom, fun x => by
        show e12 (e21 (f₂ x)) = f₂ x
        rw [he21 x, he12 x]⟩
    have hB : (fun b : H₂ => b) = w₂ := hw₂ _ ⟨hid, fun _ => rfl⟩
    exact fun b => congrFun (hA.trans hB.symm) b
  refine ⟨e12, ⟨he12hom, he12, Function.bijective_iff_has_inverse.mpr ⟨e21, hleft, hright⟩⟩, ?_⟩
  rintro e ⟨hehom, hecomm, -⟩
  exact hu12 e ⟨hehom, hecomm⟩

/-- A homomorphism of `λ⁻`-monoids carries braided families to braided families: keep the
partitions and push `u` and `v` forward. -/
theorem IsBraided.map_lmonoidHom {X : Type v} {Y : Type w} [LMonoid lam X] [LMonoid lam Y]
    {g : X → Y} (hg : IsLMonoidHom lam g) {ι : Type u} {x y : ι → X}
    (h : IsBraided lam x y) : IsBraided lam (fun i => g (x i)) (fun i => g (y i)) := by
  obtain ⟨d⟩ := h
  exact ⟨{ I := d.I
           J := d.J
           I_disjoint := d.I_disjoint
           J_disjoint := d.J_disjoint
           I_cover := d.I_cover
           J_cover := d.J_cover
           I_small := d.I_small
           J_small := d.J_small
           u := fun p => g (d.u p)
           v := fun p => g (d.v p)
           v_limit := fun a => by rw [d.v_limit a, hg.map_zero]
           hI := fun p => by
             rw [← hg.map_add, ← d.hI p, hg (d.I_small p) fun i : d.I p => x i]
             rfl
           hJ := fun p => by
             rw [← hg.map_add, ← d.hJ p, hg (d.J_small p) fun j : d.J p => y j]
             rfl }⟩

/-- Braidedness over the base transports along an isomorphism of the base: if `H` is
`λ⁻`-braided over `X₁` and `g : X₂ → X₁` is an isomorphism of `λ⁻`-monoids, then `H` is
`λ⁻`-braided over `X₂` along `f ∘ g`. -/
theorem IsBraidedOver.of_base_iso {X₁ X₂ : Type v} {H : Type w} [LMonoid lam X₁]
    [LMonoid lam X₂] [KMonoid κ H] (hlk : lam ≤ κ) {f : X₁ → H}
    (hbr : IsBraidedOver lam κ X₁ H hlk f) {g : X₂ → X₁} {g' : X₁ → X₂}
    (hg : IsLMonoidHom lam g) (hg' : IsLMonoidHom lam g')
    (hgg' : ∀ x, g' (g x) = x) (hg'g : ∀ x, g (g' x) = x) :
    IsBraidedOver lam κ X₂ H hlk (fun x => f (g x)) where
  isLHom := by
    refine ⟨show f (g 0) = 0 by rw [hg.map_zero, hbr.isLHom.1], fun {ι} h x => ?_⟩
    show f (g (lsumOf (lam := lam) h x)) = _
    rw [hg h x, hbr.isLHom.2 h (g ∘ x)]
    rfl
  injective := fun a b hab => by
    rw [← hgg' a, ← hgg' b, hbr.injective hab]
  generates := fun h => by
    obtain ⟨x, hx⟩ := hbr.generates h
    refine ⟨fun i => g' (x i), ?_⟩
    rw [hx]
    exact congrArg _ (funext fun i => by rw [hg'g (x i)])
  braided := fun x y hxy => by
    have h := (hbr.braided (fun i => g (x i)) (fun i => g (y i)) hxy).map_lmonoidHom hg'
    simpa only [hgg'] using h

/-- Braidedness transports along an isomorphism of extensions: if `H₁` is `λ⁻`-braided over `X`
and `e : H₁ → H₂` is a bijective `κ`-homomorphism commuting with the two structure maps, then
`H₂` is `λ⁻`-braided over `X` as well. -/
theorem IsBraidedOver.of_iso {X : Type v} {H₁ H₂ : Type w} [LMonoid lam X] [KMonoid κ H₁]
    [KMonoid κ H₂] (hlk : lam ≤ κ) {f₁ : X → H₁} {f₂ : X → H₂}
    (hbr : IsBraidedOver lam κ X H₁ hlk f₁) {e : H₁ → H₂} (he : IsKHom κ e)
    (hbij : Function.Bijective e) (hcomm : ∀ x, e (f₁ x) = f₂ x) :
    IsBraidedOver lam κ X H₂ hlk f₂ where
  isLHom := by
    refine ⟨by rw [← hcomm 0, hbr.isLHom.1, he.1], fun {ι} h x => ?_⟩
    rw [← hcomm (lsumOf (lam := lam) h x), hbr.isLHom.2 h x,
      he.map_sumOf (h.le.trans hlk) (f₁ ∘ x)]
    exact congrArg _ (funext fun i => hcomm (x i))
  injective := fun a b hab => hbr.injective (hbij.1 (by rw [hcomm a, hcomm b]; exact hab))
  generates := fun h => by
    obtain ⟨h₁, rfl⟩ := hbij.2 h
    obtain ⟨x, hx⟩ := hbr.generates h₁
    refine ⟨x, ?_⟩
    rw [hx, he.2 (fun i => f₁ (x i))]
    exact congrArg _ (funext fun i => hcomm (x i))
  braided := fun x y hxy => by
    refine hbr.braided x y (hbij.1 ?_)
    rw [he.2 (fun i => f₁ (x i)), he.2 (fun i => f₁ (y i)),
      show (e ∘ fun i => f₁ (x i)) = (fun i => f₂ (x i)) from funext fun i => hcomm (x i),
      show (e ∘ fun i => f₁ (y i)) = (fun i => f₂ (y i)) from funext fun i => hcomm (y i)]
    exact hxy

/-- Being `λ⁻`-braided over `X` implies being the universal `κ`-extension of `X`
(the second half of Theorem 3.11(2)); it is immediate from Proposition 3.9. -/
theorem IsBraidedOver.isUniversalKExtension {X : Type v} {H : Type w}
    [LMonoid lam X] [KMonoid κ H] (hlk : lam ≤ κ) {f : X → H}
    (hbr : IsBraidedOver lam κ X H hlk f) :
    IsUniversalKExtension lam κ X H hlk f :=
  { isLHom := hbr.isLHom
    universal := fun K _ φ hφ => extend_lhom hlk f hbr φ hφ }

/-! ## The construction `Ĥ = X^κ / (λ⁻-braiding)` -/

section Construction

variable (lam κ) (X : Type v) [LMonoid lam X]

/-- The underlying type of the universal `κ`-extension: `κ`-indexed families over `X`
modulo `λ⁻`-braiding (Theorem 3.11(1)). -/
def UnivExt : Type (max u v) := Quotient (braidingSetoid lam κ X)

namespace UnivExt

variable {lam κ X}

/-- The class of a family. -/
def mk (x : Idx κ → X) : UnivExt lam κ X := Quotient.mk _ x

theorem mk_eq_mk {x y : Idx κ → X} : mk (lam := lam) x = mk y ↔ IsBraided lam x y :=
  Quotient.eq (r := braidingSetoid lam κ X)

/-- A chosen representative of a class. -/
noncomputable def rep (q : UnivExt lam κ X) : Idx κ → X := Quotient.out q

@[simp] theorem mk_rep (q : UnivExt lam κ X) : mk (rep q) = q := Quotient.out_eq q

theorem rep_braided (x : Idx κ → X) : IsBraided lam (rep (mk (lam := lam) x)) x :=
  Quotient.exact (mk_rep (mk (lam := lam) x))

/-- Concatenation of a `κ`-indexed family of `κ`-indexed families, using a fixed bijection
`Idx κ × Idx κ ≃ Idx κ`.  This is the operation on `Ĥ`; it is well defined because braidings
can be concatenated (and independent of the bijection by Lemma 3.6(1)). -/
noncomputable def concat (hκ : ℵ₀ ≤ κ) (F : Idx κ → Idx κ → X) : Idx κ → X :=
  fun k => F ((pairEquiv hκ).symm k).1 ((pairEquiv hκ).symm k).2

/-- The embedding of the `i₀`-th row `{i₀} × κ` of `κ × κ` into `κ`. -/
noncomputable def slot (hκ : ℵ₀ ≤ κ) (i₀ : Idx κ) : Idx κ ↪ Idx κ :=
  ⟨fun j => pairEquiv hκ (i₀, j), fun _a _b hab => congrArg Prod.snd ((pairEquiv hκ).injective hab)⟩

/-- The embedding of the `j₀`-th column `κ × {j₀}` of `κ × κ` into `κ`. -/
noncomputable def coslot (hκ : ℵ₀ ≤ κ) (j₀ : Idx κ) : Idx κ ↪ Idx κ :=
  ⟨fun a => pairEquiv hκ (a, j₀), fun _a _b hab => congrArg Prod.fst ((pairEquiv hκ).injective hab)⟩

theorem slot_ne_slot (hκ : ℵ₀ ≤ κ) {i₀ i₁ : Idx κ} (hne : i₀ ≠ i₁) (i j : Idx κ) :
    slot hκ i₀ i ≠ slot hκ i₁ j := by
  intro h
  exact hne (congrArg Prod.fst ((pairEquiv hκ).injective h))

theorem extend_slot (hκ : ℵ₀ ≤ κ) (i₀ : Idx κ) (a : Idx κ → X) (k : Idx κ) :
    Function.extend (slot hκ i₀) a 0 k =
      if ((pairEquiv hκ).symm k).1 = i₀ then a ((pairEquiv hκ).symm k).2 else 0 := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p : Idx κ × Idx κ, pairEquiv hκ p = k :=
    ⟨(pairEquiv hκ).symm k, Equiv.apply_symm_apply _ _⟩
  rw [Equiv.symm_apply_apply]
  by_cases h : p.1 = i₀
  · have hk : slot hκ i₀ p.2 = pairEquiv hκ p := by
      show pairEquiv hκ (i₀, p.2) = pairEquiv hκ p
      rw [← h]
    rw [← hk, (slot hκ i₀).injective.extend_apply, if_pos h]
  · rw [Function.extend_apply' a (0 : Idx κ → X) _ ?_, if_neg h]
    · rfl
    · rintro ⟨j, hj⟩
      exact h ((congrArg Prod.fst ((pairEquiv hκ).injective hj)).symm)

theorem extend_coslot (hκ : ℵ₀ ≤ κ) (j₀ : Idx κ) (w : Idx κ → X) (k : Idx κ) :
    Function.extend (coslot hκ j₀) w 0 k =
      if ((pairEquiv hκ).symm k).2 = j₀ then w ((pairEquiv hκ).symm k).1 else 0 := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p : Idx κ × Idx κ, pairEquiv hκ p = k :=
    ⟨(pairEquiv hκ).symm k, Equiv.apply_symm_apply _ _⟩
  rw [Equiv.symm_apply_apply]
  by_cases h : p.2 = j₀
  · have hk : coslot hκ j₀ p.1 = pairEquiv hκ p := by
      show pairEquiv hκ (p.1, j₀) = pairEquiv hκ p
      rw [← h]
    rw [← hk, (coslot hκ j₀).injective.extend_apply, if_pos h]
  · rw [Function.extend_apply' w (0 : Idx κ → X) _ ?_, if_neg h]
    · rfl
    · rintro ⟨j, hj⟩
      exact h ((congrArg Prod.snd ((pairEquiv hκ).injective hj)).symm)

theorem concat_slot (hκ : ℵ₀ ≤ κ) (i₀ : Idx κ) (a : Idx κ → X) :
    concat hκ (fun i => if i = i₀ then a else 0) = Function.extend (slot hκ i₀) a 0 := by
  classical
  funext k
  rw [extend_slot]
  show (if ((pairEquiv hκ).symm k).1 = i₀ then a else 0) ((pairEquiv hκ).symm k).2 = _
  by_cases h : ((pairEquiv hκ).symm k).1 = i₀
  · simp only [if_pos h]
  · simp only [if_neg h, Pi.zero_apply]

theorem concat_coslot (hκ : ℵ₀ ≤ κ) (j₀ : Idx κ) (w : Idx κ → X) :
    concat hκ (fun i j => if j = j₀ then w i else 0) = Function.extend (coslot hκ j₀) w 0 := by
  classical
  funext k
  rw [extend_coslot]
  show (if ((pairEquiv hκ).symm k).2 = j₀ then w ((pairEquiv hκ).symm k).1 else 0) = _
  rfl

theorem concat_pair (hκ : ℵ₀ ≤ κ) {i₀ i₁ : Idx κ} (hne : i₀ ≠ i₁) (a b : Idx κ → X) :
    concat hκ (fun i => if i = i₀ then a else if i = i₁ then b else 0)
      = fun k => Function.extend (slot hκ i₀) a 0 k + Function.extend (slot hκ i₁) b 0 k := by
  classical
  funext k
  rw [extend_slot, extend_slot]
  show (if ((pairEquiv hκ).symm k).1 = i₀ then a
      else if ((pairEquiv hκ).symm k).1 = i₁ then b else 0) ((pairEquiv hκ).symm k).2 = _
  by_cases h0 : ((pairEquiv hκ).symm k).1 = i₀
  · have h1 : ¬ ((pairEquiv hκ).symm k).1 = i₁ := by rw [h0]; exact hne
    simp only [if_pos h0, if_neg h1, add_zero]
  · by_cases h1 : ((pairEquiv hκ).symm k).1 = i₁
    · simp only [if_neg h0, if_pos h1, zero_add]
    · simp only [if_neg h0, if_neg h1, Pi.zero_apply, add_zero]

/-- Braidings can be concatenated. -/
theorem mk_concat_congr (hκ : ℵ₀ ≤ κ) {x y : Idx κ → Idx κ → X}
    (h : ∀ i, IsBraided lam (x i) (y i)) :
    mk (lam := lam) (concat hκ x) = mk (concat hκ y) :=
  mk_eq_mk.mpr ((IsBraided.prod h).reindex (pairEquiv hκ).symm)

/-- The `κ`-sum on `Ĥ`. -/
noncomputable def ksumQ (hκ : ℵ₀ ≤ κ) (A : Idx κ → UnivExt lam κ X) : UnivExt lam κ X :=
  mk (concat hκ fun i => rep (A i))

theorem ksumQ_mk (hκ : ℵ₀ ≤ κ) (x : Idx κ → Idx κ → X) :
    ksumQ (lam := lam) hκ (fun i => mk (x i)) = mk (concat hκ x) :=
  mk_concat_congr hκ fun i => rep_braided (x i)

/-- Pointwise addition is compatible with braiding. -/
theorem isBraided_add (hκ : ℵ₀ ≤ κ) {x x' y y' : Idx κ → X}
    (hx : IsBraided lam x x') (hy : IsBraided lam y y') :
    IsBraided lam (fun i => x i + y i) (fun i => x' i + y' i) := by
  classical
  have hnt : Nontrivial (Idx κ) := by
    rw [← Cardinal.one_lt_iff_nontrivial, mk_Idx]
    exact lt_of_lt_of_le one_lt_aleph0 hκ
  obtain ⟨i₀, i₁, hne⟩ := hnt.exists_pair_ne
  have key : ∀ a b : Idx κ → X, mk (lam := lam) (fun i => a i + b i)
      = mk (concat hκ (fun i => if i = i₀ then a else if i = i₁ then b else 0)) := by
    intro a b
    rw [concat_pair hκ hne a b]
    exact mk_eq_mk.mpr (isBraided_merge (slot hκ i₀) (slot hκ i₁) (slot_ne_slot hκ hne) a b)
  rw [← mk_eq_mk, key x y, key x' y']
  refine mk_concat_congr hκ fun i => ?_
  by_cases h0 : i = i₀
  · simp only [if_pos h0]; exact hx
  · by_cases h1 : i = i₁
    · simp only [if_neg h0, if_pos h1]; exact hy
    · simp only [if_neg h0, if_neg h1]; exact IsBraided.refl _

/-- Addition on `Ĥ`, induced by pointwise addition of families. -/
noncomputable def addQ (hκ : ℵ₀ ≤ κ) :
    UnivExt lam κ X → UnivExt lam κ X → UnivExt lam κ X :=
  Quotient.map₂ (fun x y i => x i + y i) fun _ _ hx _ _ hy => isBraided_add hκ hx hy

/-- The commutative monoid structure on `Ĥ`, induced by the pointwise one on `X^κ`. -/
@[instance_reducible]
noncomputable def instAddCommMonoid (hκ : ℵ₀ ≤ κ) : AddCommMonoid (UnivExt lam κ X) :=
  letI : Zero (UnivExt lam κ X) := ⟨mk 0⟩
  letI : Add (UnivExt lam κ X) := ⟨addQ hκ⟩
  { zero := mk 0
    add := addQ hκ
    nsmul := nsmulRec
    nsmul_zero := fun _ => rfl
    nsmul_succ := fun _ _ => rfl
    add_assoc := Quotient.ind fun x => Quotient.ind fun y => Quotient.ind fun z =>
      congrArg mk (funext fun i => add_assoc (x i) (y i) (z i))
    zero_add := Quotient.ind fun x => congrArg mk (funext fun i => zero_add (x i))
    add_zero := Quotient.ind fun x => congrArg mk (funext fun i => add_zero (x i))
    add_comm := Quotient.ind fun x => Quotient.ind fun y =>
      congrArg mk (funext fun i => add_comm (x i) (y i)) }

/-- Axiom (A1) for `Ĥ`. -/
theorem ksumQ_single (hκ : ℵ₀ ≤ κ) (i₀ : Idx κ) (A : Idx κ → UnivExt lam κ X)
    (hA : ∀ i, i ≠ i₀ → A i = mk 0) : ksumQ hκ A = A i₀ := by
  classical
  have h1 : ksumQ hκ A = mk (concat hκ (fun i => if i = i₀ then rep (A i₀) else 0)) := by
    show mk (concat hκ fun i => rep (A i)) = _
    refine mk_concat_congr hκ fun i => ?_
    by_cases h : i = i₀
    · subst h
      simp only [↓reduceIte]
      exact IsBraided.refl _
    · simp only [hA i h, if_neg h]
      exact rep_braided (lam := lam) (0 : Idx κ → X)
  rw [h1, concat_slot, mk_eq_mk.mpr (isBraided_extend (slot hκ i₀) (rep (A i₀))), mk_rep]

/-- Axiom (A2) for `Ĥ`: concatenating in two steps or in one gives braided families. -/
theorem ksumQ_sigma (hκ : ℵ₀ ≤ κ) (A : Idx κ → Idx κ → UnivExt lam κ X)
    (π : Idx κ × Idx κ ≃ Idx κ) :
    ksumQ hκ (fun i => ksumQ hκ (A i))
      = ksumQ hκ (fun k => A (π.symm k).1 (π.symm k).2) := by
  set P := pairEquiv hκ with hPdef
  set x : Idx κ → Idx κ → Idx κ → X := fun i j => rep (A i j) with hxdef
  have hL : ksumQ hκ (fun i => ksumQ hκ (A i)) = mk (concat hκ (fun i => concat hκ (x i))) := by
    show mk (concat hκ fun i => rep (ksumQ hκ (A i))) = _
    exact mk_concat_congr hκ fun i => rep_braided (concat hκ (x i))
  have hR : ksumQ hκ (fun k => A (π.symm k).1 (π.symm k).2)
      = mk (concat hκ (fun k => x (π.symm k).1 (π.symm k).2)) := rfl
  rw [hL, hR]
  set e₁ : Idx κ ≃ Idx κ × Idx κ × Idx κ :=
    P.symm.trans ((Equiv.refl (Idx κ)).prodCongr P.symm) with he₁
  set e₂ : Idx κ ≃ Idx κ × Idx κ × Idx κ :=
    P.symm.trans ((π.symm.prodCongr (Equiv.refl (Idx κ))).trans (Equiv.prodAssoc _ _ _)) with he₂
  set F : Idx κ × Idx κ × Idx κ → X := fun t => x t.1 t.2.1 t.2.2 with hFdef
  have hLe : concat hκ (fun i => concat hκ (x i)) = F ∘ e₁ := rfl
  have hRe : concat hκ (fun k => x (π.symm k).1 (π.symm k).2) = F ∘ e₂ := rfl
  rw [hLe, hRe]
  have hcomp : (F ∘ e₂) ∘ (e₁.trans e₂.symm) = F ∘ e₁ := by
    funext k
    show F (e₂ (e₂.symm (e₁ k))) = F (e₁ k)
    rw [Equiv.apply_symm_apply]
  have hbr : IsBraided lam (F ∘ e₂) (F ∘ e₁) := by
    have h := IsBraided.of_perm (lam := lam) (F ∘ e₂) (e₁.trans e₂.symm)
    rwa [hcomp] at h
  exact (mk_eq_mk.mpr hbr).symm

/-- Compatibility of the `κ`-sum on `Ĥ` with its binary addition. -/
theorem ksumQ_two (hκ : ℵ₀ ≤ κ) (a b : UnivExt lam κ X) (i₀ i₁ : Idx κ) (hne : i₀ ≠ i₁) :
    ksumQ hκ (fun i => if i = i₀ then a else if i = i₁ then b else mk 0) = addQ hκ a b := by
  classical
  have h1 : ksumQ hκ (fun i => if i = i₀ then a else if i = i₁ then b else mk 0)
      = mk (concat hκ (fun i => if i = i₀ then rep a else if i = i₁ then rep b else 0)) := by
    show mk (concat hκ fun i => rep _) = _
    refine mk_concat_congr hκ fun i => ?_
    by_cases h0 : i = i₀
    · simp only [if_pos h0]
      exact IsBraided.refl _
    · by_cases h1 : i = i₁
      · simp only [if_neg h0, if_pos h1]
        exact IsBraided.refl _
      · simp only [if_neg h0, if_neg h1]
        exact rep_braided (lam := lam) (0 : Idx κ → X)
  have h2 : addQ hκ a b = mk (fun i => rep a i + rep b i) := by
    conv_lhs => rw [← mk_rep a, ← mk_rep b]
    rfl
  rw [h1, concat_pair hκ hne, h2]
  exact (mk_eq_mk.mpr (isBraided_merge (slot hκ i₀) (slot hκ i₁) (slot_ne_slot hκ hne)
    (rep a) (rep b))).symm

/-- The `κ`-monoid structure on `Ĥ` (Theorem 3.11(1)). -/
@[instance_reducible]
noncomputable def instKMonoid (hlam : lam.IsRegular) (hlk : lam ≤ κ) :
    KMonoid κ (UnivExt lam κ X) :=
  letI hκ : ℵ₀ ≤ κ := hlam.aleph0_le.trans hlk
  letI := instAddCommMonoid (lam := lam) (κ := κ) (X := X) hκ
  KMonoid.ofKsum
    { aleph0_le := hκ
      ksum := ksumQ hκ
      ksum_single := fun i₀ A hA => ksumQ_single hκ i₀ A hA
      ksum_sigma := fun A π => ksumQ_sigma hκ A π }
    fun a b i₀ i₁ hne => ksumQ_two hκ a b i₀ i₁ hne

/-- The `κ`-sum on `Ĥ` is the concatenation operation `ksumQ`. -/
@[simp] theorem instKMonoid_ksum (hlam : lam.IsRegular) (hlk : lam ≤ κ)
    (A : Idx κ → UnivExt lam κ X) :
    letI := instKMonoid (lam := lam) (κ := κ) (X := X) hlam hlk
    ksum (κ := κ) A = ksumQ (hlam.aleph0_le.trans hlk) A := by
  letI hκ : ℵ₀ ≤ κ := hlam.aleph0_le.trans hlk
  letI := instAddCommMonoid (lam := lam) (κ := κ) (X := X) hκ
  exact KMonoid.ofKsum_ksum
    { aleph0_le := hκ
      ksum := ksumQ hκ
      ksum_single := fun i₀ A hA => ksumQ_single hκ i₀ A hA
      ksum_sigma := fun A π => ksumQ_sigma hκ A π }
    (fun a b i₀ i₁ hne => ksumQ_two hκ a b i₀ i₁ hne) A

/-- The canonical `λ⁻`-homomorphism `X → Ĥ`, sending `x` to the class of the family
concentrated at one index. -/
noncomputable def of (i₀ : Idx κ) (x : X) : UnivExt lam κ X :=
  mk (fun i => if i = i₀ then x else 0)

theorem of_zero (i₀ : Idx κ) : of (lam := lam) i₀ (0 : X) = mk 0 :=
  congrArg mk (funext fun _ => ite_self 0)

/-- Every class is the `κ`-sum of the images of the entries of any representative. -/
theorem ksumQ_of (hκ : ℵ₀ ≤ κ) (i₀ : Idx κ) (w : Idx κ → X) :
    ksumQ (lam := lam) hκ (fun i => of i₀ (w i)) = mk w := by
  show ksumQ hκ (fun i => mk (fun j => if j = i₀ then w i else 0)) = _
  rw [ksumQ_mk hκ, concat_coslot hκ i₀ w]
  exact mk_eq_mk.mpr (isBraided_extend (coslot hκ i₀) w)

end UnivExt

end Construction

/-! ## Theorem 3.11 -/

/-- **Injectivity of the canonical map**, and the reason reducedness is the right
hypothesis: over a reduced `λ⁻`-monoid `X`, two families concentrated at a single index are
`λ⁻`-braided only if they have the same entry.

Paper-style proof: in a braiding of `(x,0,0,…)` and `(y,0,0,…)`, reducedness forces
`u μ = v μ = 0` for all but at most one index, and the remaining equations give `x = y`.
(Neither the regularity of `λ` nor `λ ≤ κ` is used; the two hypotheses are kept for
uniformity with the rest of the section.) -/
theorem UnivExt.of_injective (_hlam : lam.IsRegular) (_hlk : lam ≤ κ) {X : Type v}
    [LMonoid lam X] (hred : IsConical X) (i₀ : Idx κ) :
    Function.Injective (UnivExt.of (lam := lam) (κ := κ) (X := X) i₀) := by
  classical
  intro a b hab
  obtain ⟨d⟩ := UnivExt.mk_eq_mk.mp hab
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  have hsingle : #({i₀} : Set (Idx κ)) < lam := by
    rw [Cardinal.mk_singleton]; exact lt_of_lt_of_le one_lt_aleph0 hlam0
  -- partial sums of a family concentrated at `i₀`
  have hsum : ∀ (S : Set (Idx κ)) (hS : #S < lam) (c : X), i₀ ∈ S →
      lsumOf (lam := lam) hS (fun i : S => (if (i : Idx κ) = i₀ then c else 0)) = c := by
    intro S hS c hmem
    rw [LMonoid.lsumOf_of_subset hS hsingle (Set.singleton_subset_iff.mpr hmem)
      (fun i => if i = i₀ then c else 0)
      (fun i _ hi => if_neg (fun h : i = i₀ => hi (by rw [h]; rfl)))]
    letI : Unique ({i₀} : Set (Idx κ)) := Set.uniqueSingleton i₀
    rw [lsumOf_unique hsingle (fun i : ({i₀} : Set (Idx κ)) => (if (i : Idx κ) = i₀ then c else 0))]
    exact if_pos rfl
  have hsum0 : ∀ (S : Set (Idx κ)) (hS : #S < lam) (c : X), i₀ ∉ S →
      lsumOf (lam := lam) hS (fun i : S => (if (i : Idx κ) = i₀ then c else 0)) = 0 :=
    fun S hS c hmem =>
      LMonoid.lsumOf_eq_zero hS (fun i => if i = i₀ then c else 0)
        (fun i hi => if_neg (fun h : i = i₀ => hmem (h ▸ hi)))
  set p₀ := IsBraided.blockOf d.I d.I_cover i₀ with hp₀def
  set q₀ := IsBraided.blockOf d.J d.J_cover i₀ with hq₀def
  have hp₀mem : i₀ ∈ d.I p₀ := IsBraided.mem_blockOf d.I d.I_cover i₀
  have hq₀mem : i₀ ∈ d.J q₀ := IsBraided.mem_blockOf d.J d.J_cover i₀
  have hIeq : ∀ p, d.v p + d.u p = if p = p₀ then a else 0 := by
    intro p
    rw [← d.hI p]
    by_cases h : p = p₀
    · subst h
      rw [if_pos rfl]
      exact hsum _ _ a hp₀mem
    · rw [if_neg h]
      refine hsum0 _ _ a (fun hmem => h ?_)
      exact (IsBraided.blockOf_eq d.I_disjoint d.I_cover hmem).symm
  have hJeq : ∀ p, d.v (bsucc p) + d.u p = if p = q₀ then b else 0 := by
    intro p
    rw [← d.hJ p]
    by_cases h : p = q₀
    · subst h
      rw [if_pos rfl]
      exact hsum _ _ b hq₀mem
    · rw [if_neg h]
      refine hsum0 _ _ b (fun hmem => h ?_)
      exact (IsBraided.blockOf_eq d.J_disjoint d.J_cover hmem).symm
  -- reducedness forces the braiding families to vanish away from the two special positions
  have hA : ∀ r, r ≠ p₀ → d.v r = 0 ∧ d.u r = 0 := by
    intro r hr
    exact hred _ _ (by rw [hIeq r, if_neg hr])
  have hB : ∀ r, r ≠ q₀ → d.v (bsucc r) = 0 ∧ d.u r = 0 := by
    intro r hr
    exact hred _ _ (by rw [hJeq r, if_neg hr])
  have hvzero : ∀ r, r ≠ bsucc q₀ → d.v r = 0 := by
    intro r hr
    by_cases h0 : r.2 = 0
    · have hr0 : r = (r.1, 0) := by rw [← h0]
      rw [hr0]
      exact d.v_limit r.1
    · have hpred : bsucc (r.1, r.2 - 1) = r := IsBraided.bsucc_prev h0
      have hne : (r.1, r.2 - 1) ≠ q₀ := fun hcon => hr (by rw [← hpred, hcon])
      have hv := (hB _ hne).1
      rwa [hpred] at hv
  have ha : d.v p₀ + d.u p₀ = a := by rw [hIeq p₀, if_pos rfl]
  have hb : d.v (bsucc q₀) + d.u q₀ = b := by rw [hJeq q₀, if_pos rfl]
  by_cases hpq : p₀ = q₀
  · have h1 : d.v p₀ = 0 := hvzero p₀ (by rw [← hpq]; exact IsBraided.bsucc_ne_self p₀)
    have h2 : d.v (bsucc q₀) = 0 :=
      (hA _ (by rw [← hpq]; exact Ne.symm (IsBraided.bsucc_ne_self p₀))).1
    calc a = d.v p₀ + d.u p₀ := ha.symm
      _ = d.u p₀ := by rw [h1, zero_add]
      _ = d.u q₀ := by rw [hpq]
      _ = d.v (bsucc q₀) + d.u q₀ := by rw [h2, zero_add]
      _ = b := hb
  · have hu1 : d.u p₀ = 0 := (hB p₀ hpq).2
    have hu2 : d.u q₀ = 0 := (hA q₀ (Ne.symm hpq)).2
    by_cases hbq : p₀ = bsucc q₀
    · calc a = d.v p₀ + d.u p₀ := ha.symm
        _ = d.v p₀ := by rw [hu1, add_zero]
        _ = d.v (bsucc q₀) := by rw [hbq]
        _ = d.v (bsucc q₀) + d.u q₀ := by rw [hu2, add_zero]
        _ = b := hb
    · have h1 : d.v p₀ = 0 := hvzero p₀ hbq
      have h2 : d.v (bsucc q₀) = 0 := (hA _ (fun hc => hbq hc.symm)).1
      calc a = d.v p₀ + d.u p₀ := ha.symm
        _ = d.v p₀ := by rw [hu1, add_zero]
        _ = 0 := h1
        _ = d.v (bsucc q₀) := h2.symm
        _ = d.v (bsucc q₀) + d.u q₀ := by rw [hu2, add_zero]
        _ = b := hb

/-- **Theorem 3.11** (with the hypothesis `IsConical X` added, cf. the module docstring).

Let `λ ≤ κ` with `λ` regular and let `X` be a *reduced* `λ⁻`-monoid.  Then there is a
`κ`-monoid `Ĥ` containing `X` as a `λ⁻`-submonoid such that

1. `Ĥ` is `λ⁻`-braided over `X`, and
2. `Ĥ` is the universal `κ`-extension of `X`. -/
theorem theorem_3_11 (hlam : lam.IsRegular) (hlk : lam ≤ κ) (X : Type v) [LMonoid lam X]
    (hred : IsConical X) :
    ∃ (Hh : Type (max u v)) (_ : KMonoid κ Hh) (f : X → Hh),
      Function.Injective f ∧
      IsBraidedOver lam κ X Hh hlk f ∧
      IsUniversalKExtension lam κ X Hh hlk f := by
  classical
  have hκ : ℵ₀ ≤ κ := hlam.aleph0_le.trans hlk
  obtain ⟨i₀⟩ := nonempty_Idx hκ
  letI inst : KMonoid κ (UnivExt lam κ X) := UnivExt.instKMonoid hlam hlk
  have hgen : ∀ w : Idx κ → X,
      ksum (κ := κ) (fun i => UnivExt.of (lam := lam) i₀ (w i)) = UnivExt.mk w :=
    fun w => (UnivExt.instKMonoid_ksum hlam hlk _).trans (UnivExt.ksumQ_of hκ i₀ w)
  have hof0 : UnivExt.of (lam := lam) (κ := κ) (X := X) i₀ 0 = 0 := UnivExt.of_zero i₀
  have hbraided : IsBraidedOver lam κ X (UnivExt lam κ X) hlk (UnivExt.of i₀) := by
    refine ⟨⟨hof0, ?_⟩, UnivExt.of_injective hlam hlk hred i₀, ?_, ?_⟩
    · -- `of i₀` is a `λ⁻`-homomorphism
      intro ι h z
      have hg : #ι ≤ κ := h.le.trans hlk
      set g : ι ↪ Idx κ := emb hg with hgdef
      have hfam : Function.extend g (fun i => UnivExt.of (lam := lam) i₀ (z i)) 0
          = fun a => UnivExt.of (lam := lam) i₀ (Function.extend g z 0 a) := by
        funext a
        by_cases ha : ∃ i, g i = a
        · obtain ⟨i, rfl⟩ := ha
          rw [g.injective.extend_apply, g.injective.extend_apply]
        · rw [Function.extend_apply' _ _ _ ha, Function.extend_apply' _ _ _ ha]
          show (0 : UnivExt lam κ X) = UnivExt.of i₀ (0 : X)
          rw [hof0]
      show UnivExt.of i₀ (lsumOf h z)
        = sumOf (κ := κ) hg (fun i => UnivExt.of (lam := lam) i₀ (z i))
      rw [KMonoid.sumOf_eq_extend hg g, hfam, hgen (Function.extend g z 0)]
      -- both sides are classes of families with small support and equal sums
      refine UnivExt.mk_eq_mk.mpr ?_
      have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
      have hsingle : #({i₀} : Set (Idx κ)) < lam := by
        rw [Cardinal.mk_singleton]; exact lt_of_lt_of_le one_lt_aleph0 hlam0
      have hrange : #(Set.range g : Set (Idx κ)) < lam := by
        rw [Cardinal.mk_range_eq g g.injective]; exact h
      refine isBraided_of_small_sets hsingle hrange (fun i hi => if_neg (fun hc => hi hc))
        (fun j hj => Function.extend_apply' z (0 : Idx κ → X) j (fun ⟨i, hi⟩ => hj ⟨i, hi⟩)) ?_
      letI : Unique ({i₀} : Set (Idx κ)) := Set.uniqueSingleton i₀
      rw [lsumOf_unique hsingle
        (fun i : ({i₀} : Set (Idx κ)) => (if (i : Idx κ) = i₀ then lsumOf h z else 0))]
      have hdef : ((default : ({i₀} : Set (Idx κ))) : Idx κ) = i₀ := rfl
      rw [hdef, if_pos rfl]
      have hcomp : (fun j : Set.range g => Function.extend g z 0 (j : Idx κ))
          ∘ (Equiv.ofInjective (g : ι → Idx κ) g.injective) = z := by
        funext i
        exact g.injective.extend_apply z 0 i
      rw [lsumOf_equiv hrange h (Equiv.ofInjective (g : ι → Idx κ) g.injective)
        (fun j : Set.range g => Function.extend g z 0 (j : Idx κ)), hcomp]
    · -- `Ĥ` is generated by the image of `X`
      intro q
      exact ⟨UnivExt.rep q, by rw [hgen (UnivExt.rep q), UnivExt.mk_rep]⟩
    · -- families with equal `κ`-sums are braided
      intro x y hxy
      rw [hgen x, hgen y] at hxy
      exact UnivExt.mk_eq_mk.mp hxy
  exact ⟨UnivExt lam κ X, inst, UnivExt.of i₀, UnivExt.of_injective hlam hlk hred i₀, hbraided,
    hbraided.isUniversalKExtension hlk⟩

/-- **Theorem 3.11** for `λ > ℵ₀`, exactly as printed in the paper: there the hypothesis added
to `theorem_3_11` is automatic, since a `λ⁻`-monoid with `ℵ₀ < λ` is reduced by
`LMonoid.isConical` (the analogue of Lemma 2.8(1) for `λ⁻`-monoids).

So the deviation from the paper is confined to `λ = ℵ₀`, where a `λ⁻`-monoid is an arbitrary
commutative monoid and the hypothesis is genuinely necessary — see
`isConical_of_isUniversalKExtension` and the counterexample `ℤ` below. -/
theorem theorem_3_11_of_aleph0_lt (hlam : lam.IsRegular) (hlk : lam ≤ κ) (hlam0 : ℵ₀ < lam)
    (X : Type v) [LMonoid lam X] :
    ∃ (Hh : Type (max u v)) (_ : KMonoid κ Hh) (f : X → Hh),
      Function.Injective f ∧
      IsBraidedOver lam κ X Hh hlk f ∧
      IsUniversalKExtension lam κ X Hh hlk f :=
  theorem_3_11 hlam hlk X (LMonoid.isConical hlam0)

/-- **Theorem 3.11 as an equivalence**: a universal `κ`-extension of a reduced `λ⁻`-monoid `X` is
`λ⁻`-braided over `X`.  Together with `IsBraidedOver.isUniversalKExtension` this is the paper's
remark after Definition 3.10 that "`Ĥ` is `λ⁻`-braided over `H`" and "`Ĥ` is the universal
`κ`-extension of `H`" are two descriptions of the same thing.

Proof: `theorem_3_11` produces *some* extension that is both braided and universal, uniqueness of
universal extensions identifies it with the given one, and braidedness transports along that
isomorphism (`IsBraidedOver.of_iso`).

The universe `Type (max u v)` is where `theorem_3_11` puts its extension, and uniqueness compares
two extensions in the same universe; for `X : Type u` this is no restriction, and for
`X : Type (u+1)` — the case of `F_κ` and its powers — it reads `Type (u+1)`. -/
theorem isBraidedOver_of_isUniversalKExtension (hlam : lam.IsRegular) (hlk : lam ≤ κ)
    {X : Type v} [LMonoid lam X] (hred : IsConical X) {H : Type (max u v)} [KMonoid κ H]
    {f : X → H} (hu : IsUniversalKExtension lam κ X H hlk f) :
    IsBraidedOver lam κ X H hlk f := by
  obtain ⟨Hh, _, g, _, hgbr, hgu⟩ := theorem_3_11 hlam hlk X hred
  obtain ⟨e, ⟨hehom, hecomm, hebij⟩, -⟩ := isUniversalKExtension_unique hlk hgu hu
  exact hgbr.of_iso hlk hehom hebij hecomm

/-- Conversely, a `λ⁻`-monoid admitting a universal `κ`-extension into which it embeds must
be reduced; so the hypothesis added in `theorem_3_11` cannot be dropped. -/
theorem isConical_of_isUniversalKExtension {X : Type v} {Hh : Type w}
    [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ κ) {f : X → Hh}
    (hf : Function.Injective f) (hhom : IsLHom hlk f) : IsConical X :=
  LMonoid.isConical_of_injective (lam := lam) (κ := κ) f hf hhom.1
    (fun a b => IsLHom.map_add hlk hhom a b)

/-- A concrete counterexample to Theorem 3.11 as printed: `ℤ` is an `ℵ₀⁻`-monoid (i.e. a
commutative monoid) that is not reduced, hence embeds into no `κ`-monoid.

Note that the `ℵ₀⁻`-monoid structure on `ULift ℤ` has to be the canonical one of
`LMonoid.ofAddCommMonoid`: for an arbitrary `LMonoid ℵ₀ (ULift ℤ)` instance the underlying
addition is arbitrary as well, and then `1 + (-1) = 0` is not available. -/
example (hlk : (ℵ₀ : Cardinal.{u}) ≤ κ) {Hh : Type w} [KMonoid κ Hh]
    (f : ULift.{u} ℤ → Hh) (hf : Function.Injective f)
    (hhom : letI := LMonoid.ofAddCommMonoid (ULift.{u} ℤ); IsLHom hlk f) : False := by
  letI := LMonoid.ofAddCommMonoid (ULift.{u} ℤ)
  have hcon := isConical_of_isUniversalKExtension (lam := ℵ₀) hlk hf hhom
  have h0 : (⟨1⟩ : ULift.{u} ℤ) + ⟨(-1 : ℤ)⟩ = 0 := by
    apply ULift.ext
    show (1 : ℤ) + (-1) = 0
    ring
  have h1 := congrArg ULift.down (hcon ⟨1⟩ ⟨(-1 : ℤ)⟩ h0).1
  exact one_ne_zero h1

end KappaMonoid
