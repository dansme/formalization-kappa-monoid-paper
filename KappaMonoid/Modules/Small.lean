/-
**Definition 4.1**: `λ⁻`-small modules, and `dsPart` — the part of a direct sum supported on a
set of indices — which is how smallness is witnessed throughout §4.
-/
import KappaMonoid.Braiding
import Mathlib

universe u v w

open Cardinal Function Set DirectSum
open scoped Classical

namespace KappaMonoid

open KMonoid LMonoid

variable (R : Type u) [Ring R]


/-! ## Definition 4.1: `λ⁻`-small modules -/

variable (R : Type u) [Ring R]

section DsPart

variable {ι : Type u} (N : ι → Type u) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- The submodule of `⨁ i, N i` consisting of the elements supported in `s`; this is the
internal direct sum `⨁_{i ∈ s} N i`. -/
def dsPart (s : Set ι) : Submodule R (⨁ i, N i) where
  carrier := {m | ∀ i ∉ s, m i = 0}
  add_mem' := by
    intro a b ha hb i hi
    show a i + b i = 0
    rw [ha i hi, hb i hi, add_zero]
  zero_mem' := by intro i _; rfl
  smul_mem' := by
    intro c a ha i hi
    show c • a i = 0
    rw [ha i hi, smul_zero]

theorem mem_dsPart {s : Set ι} {m : ⨁ i, N i} : m ∈ dsPart R N s ↔ ∀ i ∉ s, m i = 0 := Iff.rfl

theorem dsPart_mono {s t : Set ι} (h : s ⊆ t) : dsPart R N s ≤ dsPart R N t :=
  fun _ hm i hi => hm i fun hs => hi (h hs)

@[simp] theorem dsPart_univ : dsPart R N Set.univ = ⊤ :=
  eq_top_iff.mpr fun _ _ i hi => absurd (Set.mem_univ i) hi

theorem dsPart_eq_top_of_subsingleton {s : Set ι} (h : ∀ i ∉ s, Subsingleton (N i)) :
    dsPart R N s = ⊤ :=
  eq_top_iff.mpr fun _ _ i hi => @Subsingleton.elim _ (h i hi) _ _

theorem lof_mem_dsPart {s : Set ι} {i : ι} (hi : i ∈ s) (v : N i) :
    lof R ι N i v ∈ dsPart R N s := by
  intro j hj
  have hne : j ≠ i := fun h => hj (h ▸ hi)
  rw [lof_eq_of R]
  exact DirectSum.of_eq_of_ne i j v hne

theorem dsPart_disjoint {s t : Set ι} (h : Disjoint s t) :
    Disjoint (dsPart R N s) (dsPart R N t) := by
  rw [Submodule.disjoint_def]
  intro m hms hmt
  refine DirectSum.ext (β := N) fun i => ?_
  show m i = 0
  by_cases hi : i ∈ s
  · exact hmt i fun hit => Set.disjoint_left.mp h hi hit
  · exact hms i hi

theorem dsPart_iUnion {J : Type w} (s : J → Set ι) :
    dsPart R N (⋃ j, s j) = ⨆ j, dsPart R N (s j) := by
  refine le_antisymm (fun m hm => ?_) (iSup_le fun j => dsPart_mono R N (Set.subset_iUnion s j))
  rw [← DirectSum.sum_support_of m]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hmi : m i ≠ 0 := DFinsupp.mem_support_iff.mp hi
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (show i ∈ ⋃ j, s j by
    by_contra h
    exact hmi (hm i h))
  rw [← lof_eq_of R]
  exact Submodule.mem_iSup_of_mem j (lof_mem_dsPart R N hj (m i))

theorem dsPart_union (s t : Set ι) :
    dsPart R N (s ∪ t) = dsPart R N s ⊔ dsPart R N t := by
  refine le_antisymm (fun m hm => ?_)
    (sup_le (dsPart_mono R N Set.subset_union_left) (dsPart_mono R N Set.subset_union_right))
  rw [← DirectSum.sum_support_of m]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hmi : m i ≠ 0 := DFinsupp.mem_support_iff.mp hi
  have hmem : i ∈ s ∪ t := by by_contra h; exact hmi (hm i h)
  rw [← lof_eq_of R]
  rcases hmem with h | h
  · exact Submodule.mem_sup_left (lof_mem_dsPart R N h (m i))
  · exact Submodule.mem_sup_right (lof_mem_dsPart R N h (m i))

/-! ### `dsPart s` is the direct sum over `s` -/

/-- The canonical map `⨁_{i ∈ s} N i → ⨁_{i} N i`. -/
noncomputable def dsIncl (s : Set ι) : (⨁ i : s, N i.1) →ₗ[R] ⨁ i, N i :=
  DirectSum.toModule R s _ fun i => lof R ι N i.1

theorem dsIncl_lof (s : Set ι) (i : s) (v : N i.1) :
    dsIncl R N s (lof R (↥s) (fun i : s => N i.1) i v) = lof R ι N i.1 v := by
  unfold dsIncl
  exact DirectSum.toModule_lof (M := fun i : ↥s => N i.1) R i v

theorem dsIncl_apply_val (s : Set ι) (z : ⨁ i : s, N i.1) (i : s) :
    (dsIncl R N s z) i.1 = z i := by
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero]; rfl
  | of j v =>
      rw [← lof_eq_of R, dsIncl_lof R N s j v]
      by_cases hji : j = i
      · subst hji
        rw [lof_eq_of R, lof_eq_of R, DirectSum.of_eq_same, DirectSum.of_eq_same]
      · have hval : (j : ι) ≠ (i : ι) := fun h => hji (Subtype.ext h)
        rw [lof_eq_of R, lof_eq_of R,
          DirectSum.of_eq_of_ne (β := N) (j : ι) (i : ι) v (Ne.symm hval)]
        exact (DirectSum.of_eq_of_ne (β := fun p : ↥s => N p.1) j i v (Ne.symm hji)).symm
  | add a b ha hb =>
      rw [map_add]
      show (dsIncl R N s a) i.1 + (dsIncl R N s b) i.1 = a i + b i
      rw [ha, hb]

theorem dsIncl_injective (s : Set ι) : Function.Injective (dsIncl R N s) := by
  intro z w h
  refine DirectSum.ext (β := fun i : s => N i.1) fun i => ?_
  rw [← dsIncl_apply_val R N s z i, ← dsIncl_apply_val R N s w i, h]

theorem dsIncl_range (s : Set ι) : LinearMap.range (dsIncl R N s) = dsPart R N s := by
  apply le_antisymm
  · rintro m ⟨z, rfl⟩
    induction z using DirectSum.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | of j v =>
        rw [← lof_eq_of R, dsIncl_lof R N s j v]
        exact lof_mem_dsPart R N j.2 v
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro m hm
    rw [← DirectSum.sum_support_of m]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hmi : m i ≠ 0 := DFinsupp.mem_support_iff.mp hi
    have hmem : i ∈ s := by by_contra h; exact hmi (hm i h)
    refine ⟨lof R (↥s) (fun i : s => N i.1) ⟨i, hmem⟩ (m i), ?_⟩
    rw [dsIncl_lof R N s ⟨i, hmem⟩ (m i), lof_eq_of R]

/-- `dsPart R N s` is (canonically isomorphic to) the direct sum of the `N i` for `i ∈ s`. -/
noncomputable def dsPartIso (s : Set ι) : ↥(dsPart R N s) ≃ₗ[R] ⨁ i : s, N i.1 :=
  (LinearEquiv.ofEq _ _ (dsIncl_range R N s)).symm.trans
    (LinearEquiv.ofInjective _ (dsIncl_injective R N s)).symm

/-- A direct sum all but one of whose summands is trivial *is* that summand. -/
noncomputable def directSumEquivOfSubsingleton (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → Subsingleton (N i)) : (⨁ i, N i) ≃ₗ[R] N i₀ := by
  classical
  refine LinearEquiv.ofLinearMap (DirectSum.component R ι N i₀) (DirectSum.lof R ι N i₀) ?_ ?_
  · apply LinearMap.ext
    intro m
    simp
  · refine DirectSum.linearMap_ext R (fun i => LinearMap.ext fun m => ?_)
    by_cases hi : i = i₀
    · subst hi
      simp
    · have := h i hi
      have hm : m = 0 := Subsingleton.elim m 0
      subst hm
      simp

/-- Summands outside a set `T` that are trivial may be dropped from a direct sum. -/
theorem dsum_restrict_iso (T : Set ι) (h : ∀ i ∉ T, Subsingleton (N i)) :
    Nonempty ((⨁ i, N i) ≃ₗ[R] ⨁ i : T, N i.1) :=
  ⟨((LinearEquiv.ofEq _ _ (dsPart_eq_top_of_subsingleton R N h)).trans
    Submodule.topEquiv).symm.trans (dsPartIso R N T)⟩

/-- `ULift Bool ≃ Option PUnit`, sending `true` to `none`. -/
def uliftBoolOptionEquiv : ULift.{u} Bool ≃ Option PUnit.{u + 1} where
  toFun p := if p.down then none else some PUnit.unit
  invFun o := match o with | none => ⟨true⟩ | some _ => ⟨false⟩
  left_inv := by rintro ⟨(_ | _)⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/-- A direct sum over a two-element index type is a product. -/
noncomputable def dsumUliftBoolProdIso {P : ULift.{u} Bool → Type u}
    [∀ p, AddCommGroup (P p)] [∀ p, Module R (P p)] :
    (⨁ p, P p) ≃ₗ[R] P ⟨true⟩ × P ⟨false⟩ :=
  (DirectSum.lequivCongrLeft R uliftBoolOptionEquiv).trans
    ((DirectSum.lequivProdDirectSum R
        (α := fun o => P (uliftBoolOptionEquiv.symm o))).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl R (P ⟨true⟩))
        (DirectSum.lid R (P ⟨false⟩) PUnit.{u + 1})))

end DsPart

/-- Definition 4.1: `M` is `λ⁻`-*small* if every homomorphism from `M` into a direct sum
lands in a sub-sum indexed by strictly fewer than `λ` indices. -/
def IsLambdaSmall (lam : Cardinal.{u}) (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∀ {ι : Type u} (N : ι → Type u) (_ : ∀ i, AddCommGroup (N i)) (_ : ∀ i, Module R (N i))
    (f : M →ₗ[R] (⨁ i, N i)),
    ∃ s : Set ι, #s < lam ∧ ∀ (m : M) (i : ι), i ∉ s → (DirectSum.component R ι N i) (f m) = 0

/-- Example 4.2(2): a module generated by strictly fewer than `λ` elements is `λ⁻`-small. -/
theorem isLambdaSmall_of_span {lam : Cardinal.{u}} (hlam : lam.IsRegular)
    (M : Type u) [AddCommGroup M] [Module R M] (s : Set M) (hs : #s < lam)
    (hspan : Submodule.span R s = ⊤) : IsLambdaSmall R lam M := by
  intro ι N _ _ f
  refine ⟨⋃ x : s, {i | (f x.1) i ≠ 0}, ?_, ?_⟩
  · rw [Cardinal.card_iUnion_lt_iff_forall_of_isRegular hlam hs]
    intro x
    refine lt_of_lt_of_le ?_ hlam.aleph0_le
    rw [Cardinal.lt_aleph0_iff_set_finite]
    refine Set.Finite.subset (f x.1).support.finite_toSet ?_
    intro i hi
    exact Finset.mem_coe.mpr (DFinsupp.mem_support_iff.mpr hi)
  · -- the set of elements whose image is supported in the union is a submodule containing `s`
    have hmem : ∀ m : M, f m ∈ dsPart R N (⋃ x : s, {i | (f x.1) i ≠ 0}) := by
      have hle : Submodule.span R s ≤ (dsPart R N (⋃ x : s, {i | (f x.1) i ≠ 0})).comap f := by
        refine Submodule.span_le.mpr fun x hx => ?_
        show f x ∈ dsPart R N _
        intro i hi
        by_contra hne
        exact hi (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hne⟩)
      intro m
      exact hle (hspan ▸ Submodule.mem_top)
    intro m i hi
    exact hmem m i hi

/-- Example 4.2(2): finitely generated modules are `ℵ₀⁻`-small. -/
theorem isLambdaSmall_aleph0_of_fg (M : Type u) [AddCommGroup M] [Module R M]
    (h : Module.Finite R M) : IsLambdaSmall R ℵ₀ M := by
  obtain ⟨s, hs⟩ := h.fg_top
  refine isLambdaSmall_of_span R Cardinal.isRegular_aleph0 M (↑s) ?_ hs
  rw [Cardinal.lt_aleph0_iff_set_finite]
  exact s.finite_toSet


section SmallTools

variable {R}

/-- `λ⁻`-smallness is monotone in `λ`. -/
theorem IsLambdaSmall.mono {lam lam' : Cardinal.{u}} (h : lam ≤ lam') {M : Type u}
    [AddCommGroup M] [Module R M] (hM : IsLambdaSmall R lam M) : IsLambdaSmall R lam' M := by
  intro ι N i1 i2 f
  obtain ⟨s, hs, hf⟩ := hM N i1 i2 f
  exact ⟨s, hs.trans_le h, hf⟩

theorem isLambdaSmall_of_subsingleton {lam : Cardinal.{u}} (hlam : 0 < lam) (M : Type u)
    [AddCommGroup M] [Module R M] [Subsingleton M] : IsLambdaSmall R lam M := by
  intro ι N _ _ f
  refine ⟨∅, ?_, fun m i _ => ?_⟩
  · rwa [Cardinal.mk_eq_zero]
  · rw [Subsingleton.elim m 0, map_zero]
    rfl

/-- A direct summand of a `λ⁻`-small module is `λ⁻`-small. -/
theorem IsLambdaSmall.of_prod_left {lam : Cardinal.{u}} {M M' : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (h : IsLambdaSmall R lam (M × M')) :
    IsLambdaSmall R lam M := by
  intro ι N i1 i2 f
  obtain ⟨s, hs, hf⟩ := h N i1 i2 (f.comp (LinearMap.fst R M M'))
  refine ⟨s, hs, fun m i hi => ?_⟩
  have hval := hf (m, 0) i hi
  simpa using hval

/-! ## `<λ`-generated modules

Corollary 4.4 and Corollary 4.5 are stated for the subclass `Cλ⁻` of modules *generated by*
strictly fewer than `λ` elements, which is the hypothesis Example 4.2(3) checks against
Definition 4.1.  `IsLambdaSmall` is the weaker Definition 4.1; the implication between them is
`IsLambdaGenerated.isLambdaSmall` (Example 4.2(2)). -/

variable (R)

/-- A module is **`<λ`-generated** if it is spanned by a set of fewer than `λ` elements. -/
def IsLambdaGenerated (lam : Cardinal.{u}) (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∃ s : Set M, #s < lam ∧ Submodule.span R s = ⊤

variable {R}

/-- **Example 4.2(2)**: a `<λ`-generated module is `λ⁻`-small. -/
theorem IsLambdaGenerated.isLambdaSmall {lam : Cardinal.{u}} (hlam : lam.IsRegular)
    {M : Type u} [AddCommGroup M] [Module R M] (h : IsLambdaGenerated R lam M) :
    IsLambdaSmall R lam M := by
  obtain ⟨s, hs, hspan⟩ := h
  exact isLambdaSmall_of_span R hlam M s hs hspan

/-- `<λ`-generation is monotone in `λ`. -/
theorem IsLambdaGenerated.mono {lam lam' : Cardinal.{u}} (hl : lam ≤ lam') {M : Type u}
    [AddCommGroup M] [Module R M] (h : IsLambdaGenerated R lam M) :
    IsLambdaGenerated R lam' M := by
  obtain ⟨s, hs, hspan⟩ := h
  exact ⟨s, lt_of_lt_of_le hs hl, hspan⟩

/-- A surjective image of a `<λ`-generated module is `<λ`-generated. -/
theorem IsLambdaGenerated.of_surjective {lam : Cardinal.{u}} {M M' : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (h : IsLambdaGenerated R lam M)
    (f : M →ₗ[R] M') (hf : Function.Surjective f) : IsLambdaGenerated R lam M' := by
  obtain ⟨s, hs, hspan⟩ := h
  refine ⟨f '' s, lt_of_le_of_lt Cardinal.mk_image_le hs, ?_⟩
  rw [← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

/-- `<λ`-generation transfers along an isomorphism. -/
theorem IsLambdaGenerated.of_equiv {lam : Cardinal.{u}} {M M' : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (h : IsLambdaGenerated R lam M)
    (e : M ≃ₗ[R] M') : IsLambdaGenerated R lam M' :=
  h.of_surjective (e : M →ₗ[R] M') e.surjective

/-- At `λ = ℵ₀`, `< λ`-generated is finitely generated. -/
theorem IsLambdaGenerated.finite_aleph0 {M : Type u} [AddCommGroup M] [Module R M]
    (h : IsLambdaGenerated R ℵ₀ M) : Module.Finite R M := by
  obtain ⟨s, hs, hspan⟩ := h
  exact ⟨Submodule.fg_def.mpr ⟨s, Cardinal.lt_aleph0_iff_set_finite.mp hs, hspan⟩⟩

/-- … and conversely. -/
theorem isLambdaGenerated_aleph0_of_finite {M : Type u} [AddCommGroup M] [Module R M]
    (h : Module.Finite R M) : IsLambdaGenerated R ℵ₀ M := by
  obtain ⟨t, ht⟩ := h.fg_top
  exact ⟨(↑t : Set M), by rw [Cardinal.lt_aleph0_iff_set_finite]; exact t.finite_toSet, ht⟩

/-- A direct sum of fewer than `λ` many `<λ`-generated modules is `<λ`-generated: the union of
the images of the generating sets works, and is small by regularity of `λ`. -/
theorem isLambdaGenerated_dsum {lam : Cardinal.{u}} (hlam : lam.IsRegular) {ι' : Type u}
    (hι' : #ι' < lam) (Q : ι' → Type u) [∀ i, AddCommGroup (Q i)] [∀ i, Module R (Q i)]
    (h : ∀ i, IsLambdaGenerated R lam (Q i)) : IsLambdaGenerated R lam (⨁ i, Q i) := by
  classical
  choose s hs hspan using h
  refine ⟨⋃ i', (DirectSum.lof R ι' Q i') '' (s i'), ?_, ?_⟩
  · rw [Cardinal.card_iUnion_lt_iff_forall_of_isRegular hlam hι']
    exact fun i' => lt_of_le_of_lt Cardinal.mk_image_le (hs i')
  · -- every element is a finite sum of terms `lof i' q`, and each such term is in the span
    refine eq_top_iff.mpr fun z _ => ?_
    induction z using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of i' q =>
        have hq : q ∈ Submodule.span R (s i') := (hspan i') ▸ Submodule.mem_top
        have := Submodule.apply_mem_span_image_of_mem_span (DirectSum.lof R ι' Q i') hq
        exact Submodule.span_mono (Set.subset_iUnion _ i') this
    | add a b ha hb => exact Submodule.add_mem _ (ha trivial) (hb trivial)

/-- A direct sum of fewer than `λ` many `λ⁻`-small modules is `λ⁻`-small. -/
theorem isLambdaSmall_dsum {lam : Cardinal.{u}} (hlam : lam.IsRegular) {ι' : Type u}
    (hι' : #ι' < lam) (Q : ι' → Type u) [∀ i, AddCommGroup (Q i)] [∀ i, Module R (Q i)]
    (h : ∀ i, IsLambdaSmall R lam (Q i)) : IsLambdaSmall R lam (⨁ i, Q i) := by
  intro ι N i1 i2 f
  choose s hs hf using fun i' => h i' N i1 i2 (f.comp (DirectSum.lof R ι' Q i'))
  refine ⟨⋃ i', s i', ?_, ?_⟩
  · rw [Cardinal.card_iUnion_lt_iff_forall_of_isRegular hlam hι']
    exact hs
  · have hmem : ∀ m : ⨁ i, Q i, f m ∈ dsPart R N (⋃ i', s i') := by
      intro m
      induction m using DirectSum.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | of i' q =>
          intro i hi
          rw [← lof_eq_of R]
          have := hf i' q i (fun hs => hi (Set.mem_iUnion.mpr ⟨i', hs⟩))
          exact this
      | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    intro m i hi
    exact hmem m i hi

end SmallTools

end KappaMonoid
