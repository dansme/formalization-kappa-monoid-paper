/-
Part 4 — Section 4: `κ`-monoids of modules, and Theorem 4.3.

Modelling "a class of modules whose isomorphism classes form a set"
------------------------------------------------------------------
In Lean there is no type of all `R`-modules, so we present a class `C` of modules by the
data of

* a type `carrier` of isomorphism classes,
* a chosen representative module `rep a` for each `a : carrier`,
* the requirement that non-equal classes are non-isomorphic (`eq_of_iso`),
* closure operations witnessing that `C` is closed under `κ`-indexed direct sums and under
  direct summands.

`V^κ(C)` is then `carrier`, and the `κ`-monoid axioms (A1) and (A2) hold because direct sums
satisfy them up to isomorphism.  This is `ModuleClass.instKMonoid` below.
-/
import KappaMonoid.Universal

universe u v w

open Cardinal Function Set DirectSum
open scoped Classical

namespace KappaMonoid

open KMonoid LMonoid

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
  refine LinearEquiv.ofLinear (DirectSum.component R ι N i₀) (DirectSum.lof R ι N i₀) ?_ ?_
  · apply LinearMap.ext
    intro m
    simp
  · refine DirectSum.linearMap_ext R (fun i => LinearMap.ext fun m => ?_)
    by_cases hi : i = i₀
    · subst hi
      simp
    · haveI := h i hi
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
  · rwa [Cardinal.mk_emptyCollection]
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

/-! ## The internal direct sum of a family of submodules -/

section DsSub

variable {ι : Type u} (N : ι → Type u) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- The internal direct sum `⨁ i, P i` of a family of submodules `P i ≤ N i`, as a submodule
of `⨁ i, N i`. -/
def dsSub (P : ∀ i, Submodule R (N i)) : Submodule R (⨁ i, N i) where
  carrier := {m | ∀ i, m i ∈ P i}
  add_mem' := by
    intro a b ha hb i
    show a i + b i ∈ P i
    exact (P i).add_mem (ha i) (hb i)
  zero_mem' := fun i => (P i).zero_mem
  smul_mem' := by
    intro c a ha i
    show c • a i ∈ P i
    exact (P i).smul_mem c (ha i)

theorem mem_dsSub {P : ∀ i, Submodule R (N i)} {m : ⨁ i, N i} :
    m ∈ dsSub R N P ↔ ∀ i, m i ∈ P i := Iff.rfl

theorem lmap_subtype_range (P : ∀ i, Submodule R (N i)) :
    LinearMap.range (DirectSum.lmap (fun i => (P i).subtype)) = dsSub R N P := by
  apply le_antisymm
  · rintro m ⟨x, rfl⟩ i
    rw [DirectSum.lmap_apply]
    exact (x i).2
  · intro m hm
    rw [← DirectSum.sum_support_of m]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine ⟨lof R ι (fun i => ↥(P i)) i ⟨m i, hm i⟩, ?_⟩
    rw [DirectSum.lmap_lof, lof_eq_of R]
    rfl

theorem lmap_subtype_injective (P : ∀ i, Submodule R (N i)) :
    Function.Injective (DirectSum.lmap (fun i => (P i).subtype)) :=
  (DirectSum.lmap_injective _).mpr fun _ => Subtype.val_injective

/-- `⨁ i, P i` really is the direct sum of the `P i`. -/
noncomputable def dsSubIso (P : ∀ i, Submodule R (N i)) :
    ↥(dsSub R N P) ≃ₗ[R] ⨁ i, ↥(P i) :=
  (LinearEquiv.ofEq _ _ (lmap_subtype_range R N P)).symm.trans
    (LinearEquiv.ofInjective _ (lmap_subtype_injective R N P)).symm

theorem dsSub_isCompl {P Q : ∀ i, Submodule R (N i)} (h : ∀ i, IsCompl (P i) (Q i)) :
    IsCompl (dsSub R N P) (dsSub R N Q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro m hmP hmQ
    refine DirectSum.ext (β := N) fun i => ?_
    show m i = 0
    exact Submodule.disjoint_def.mp (h i).disjoint (m i) (hmP i) (hmQ i)
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    set y : ⨁ i, N i :=
      DirectSum.lmap (fun i => (P i).projection (Q i) (h i)) m with hydef
    have hyi : ∀ i, y i = (P i).projection (Q i) (h i) (m i) := fun i =>
      DirectSum.lmap_apply _ m i
    have hyP : y ∈ dsSub R N P := by
      intro i
      rw [hyi i]
      exact Submodule.projection_apply_mem (h i) (m i)
    have hyQ : m - y ∈ dsSub R N Q := by
      intro i
      show m i - y i ∈ Q i
      rw [hyi i]
      refine (Submodule.projection_apply_eq_zero_iff (h i)).mp ?_
      rw [map_sub, Submodule.projection_apply_of_mem_left (h i)
        (Submodule.projection_apply_mem (h i) (m i)), sub_self]
    have : m = y + (m - y) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hyP) (Submodule.mem_sup_right hyQ)

end DsSub

/-! ## Classes of modules and `V^κ(C)` -/

/-- A class of `R`-modules, closed under `κ`-indexed direct sums, direct summands and
isomorphisms, and whose isomorphism classes form the set `carrier` (Definition 2.4). -/
structure ModuleClass (κ : Cardinal.{u}) where
  /-- The set of isomorphism classes; this is `V^κ(C)`. -/
  carrier : Type u
  /-- A chosen representative for each isomorphism class. -/
  rep : carrier → Type u
  addCommGroup : ∀ a, AddCommGroup (rep a)
  module : ∀ a, Module R (rep a)
  /-- Distinct classes are non-isomorphic. -/
  eq_of_iso : ∀ {a b : carrier},
    letI := addCommGroup a; letI := addCommGroup b; letI := module a; letI := module b
    (rep a ≃ₗ[R] rep b) → a = b
  /-- The zero module belongs to the class. -/
  zero : carrier
  subsingleton_rep_zero : Subsingleton (rep zero)
  /-- Closure under `κ`-indexed direct sums. -/
  dsum : (Idx κ → carrier) → carrier
  dsum_iso : ∀ f : Idx κ → carrier,
    letI := fun i => addCommGroup (f i); letI := fun i => module (f i)
    letI := addCommGroup (dsum f); letI := module (dsum f)
    Nonempty (rep (dsum f) ≃ₗ[R] (⨁ i, rep (f i)))

namespace ModuleClass

variable {R} {κ : Cardinal.{u}} (C : ModuleClass R κ)

attribute [instance] ModuleClass.addCommGroup ModuleClass.module

/-- **Closure under direct summands.**

Definition 2.4 asks only for closure under isomorphism and `κ`-indexed direct sums, which is all
`V^κ(C)` needs in order to be a `κ`-monoid; that is what `ModuleClass` records.  Section 4 needs
the class to be closed under direct summands as well, but §2.3's class of *free* modules is not —
a direct summand of a free module is projective, not free.  Closure under summands is therefore a
separate property rather than a field of `ModuleClass`.

It is a class so that it threads through the transfinite recursion of Theorem 4.3 by instance
resolution instead of by hand. -/
class IsSummandClosed : Prop where
  /-- A direct summand of a representative is again represented by a class. -/
  exists_of_isCompl : ∀ (a : C.carrier) (N K : Submodule R (C.rep a)), IsCompl N K →
    ∃ b, Nonempty (C.rep b ≃ₗ[R] ↥N)

/-- The bare `κ`-monoid data on `V^κ(C)`: (A1) and (A2) hold because direct sums do. -/
noncomputable def bareKMonoid (hκ : ℵ₀ ≤ κ) : @BareKMonoid κ C.carrier ⟨C.zero⟩ := by
  classical
  letI : Zero C.carrier := ⟨C.zero⟩
  refine
    { aleph0_le := hκ
      ksum := C.dsum
      ksum_single := ?_
      ksum_sigma := ?_ }
  · -- (A1): all but one summand is the zero module
    intro i₀ x hx
    refine C.eq_of_iso ?_
    have hsub : ∀ i, i ≠ i₀ → Subsingleton (C.rep (x i)) := by
      intro i hi
      have h1 : C.rep (x i) = C.rep C.zero := congrArg C.rep (hx i hi)
      rw [h1]
      exact C.subsingleton_rep_zero
    exact (C.dsum_iso x).some.trans (directSumEquivOfSubsingleton R (fun i => C.rep (x i)) i₀ hsub)
  · -- (A2): `⨁ᵢ ⨁ⱼ ≅ ⨁_{(i,j)} ≅ ⨁_k`
    intro x π
    refine C.eq_of_iso ?_
    set h : (Σ _ : Idx κ, Idx κ) ≃ Idx κ :=
      (Equiv.sigmaEquivProd (Idx κ) (Idx κ)).trans π with hhdef
    have e1 := (C.dsum_iso (fun i => C.dsum (x i))).some
    have e2 : (⨁ i, C.rep (C.dsum (x i))) ≃ₗ[R] ⨁ i, ⨁ j, C.rep (x i j) :=
      DirectSum.congrLinearEquiv (fun i => (C.dsum_iso (x i)).some)
    have e3 : (⨁ p : (Σ _ : Idx κ, Idx κ), C.rep (x p.1 p.2)) ≃ₗ[R] ⨁ i, ⨁ j, C.rep (x i j) :=
      DirectSum.sigmaLcurryEquiv (R := R) (ι := Idx κ) (α := fun _ => Idx κ)
        (δ := fun i j => C.rep (x i j))
    have e4 : (⨁ p : (Σ _ : Idx κ, Idx κ), C.rep (x p.1 p.2))
        ≃ₗ[R] ⨁ k, C.rep (x (π.symm k).1 (π.symm k).2) := DirectSum.lequivCongrLeft R h
    have e5 := (C.dsum_iso (fun k => x (π.symm k).1 (π.symm k).2)).some
    exact e1.trans (e2.trans (e3.symm.trans (e4.trans e5.symm)))

/-- `V^κ(C)` is a `κ`-monoid (Examples 2.3(4)); by Lemma 2.5 (`KMonoid.ofBare`) the additive
structure is determined by the direct sum. -/
@[instance_reducible]
noncomputable def instKMonoid (hκ : ℵ₀ ≤ κ) : KMonoid κ C.carrier :=
  @KMonoid.ofBare κ C.carrier ⟨C.zero⟩ (C.bareKMonoid hκ)

/-- The `κ`-sum on `V^κ(C)` is the direct sum. -/
theorem instKMonoid_ksum (hκ : ℵ₀ ≤ κ) (x : Idx κ → C.carrier) :
    letI := C.instKMonoid hκ
    ksum (κ := κ) x = C.dsum x :=
  @KMonoid.ofBare_ksum κ C.carrier ⟨C.zero⟩ (C.bareKMonoid hκ) x

/-- The zero of `V^κ(C)` is the class of the zero module. -/
theorem instKMonoid_zero (hκ : ℵ₀ ≤ κ) :
    letI := C.instKMonoid hκ
    (0 : C.carrier) = C.zero := rfl

/-- Equal isomorphism classes have isomorphic representatives. -/
theorem iso_of_eq {a b : C.carrier} (h : a = b) : Nonempty (C.rep a ≃ₗ[R] C.rep b) := by
  subst h
  exact ⟨LinearEquiv.refl R _⟩

/-- Equal `κ`-sums in `V^κ(C)` mean isomorphic direct sums: this is the module-theoretic
form of the hypothesis of Theorem 4.3. -/
theorem iso_of_dsum_eq (x y : Idx κ → C.carrier) (h : C.dsum x = C.dsum y) :
    Nonempty ((⨁ i, C.rep (x i)) ≃ₗ[R] ⨁ j, C.rep (y j)) :=
  ⟨(C.dsum_iso x).some.symm.trans (((C.iso_of_eq h).some).trans (C.dsum_iso y).some)⟩

/-- `Cλ⁻`: the subclass of `λ⁻`-small members of `C`. -/
def lambdaSmallPart (lam : Cardinal.{u}) : Set C.carrier :=
  {a | IsLambdaSmall R lam (C.rep a)}

end ModuleClass

/-! ## The module-theoretic core of Theorem 4.3

`(M1)` and `(M2)` are the two elementary facts used in the proof. -/

section ModuleFacts

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- (M1): complements of the *same* submodule are isomorphic (both are `M / A`). -/
theorem iso_of_isCompl_left {A B C' : Submodule R M} (h₁ : IsCompl A B) (h₂ : IsCompl A C') :
    Nonempty (B ≃ₗ[R] C') :=
  ⟨(Submodule.quotientEquivOfIsCompl A B h₁).symm.trans
    (Submodule.quotientEquivOfIsCompl A C' h₂)⟩

end ModuleFacts

/-! ## Machinery for Theorem 4.3

The module-theoretic core of Theorem 4.3 is a transfinite construction inside a module `M`
presented in two ways as a `κ`-indexed direct sum.  We first develop the sub-sums
`⨁_{i ∈ s} A i` of such a presentation (`dsPart`, `Decomp.P`), the elementary lattice facts
about internal direct sums, and the dictionary between direct summands of `M` and classes in
`V^κ(C)`; the construction itself is `DoubleDecomp.fam`.

A `DoubleDecomp` is exactly the situation of the proof: a module `M` written in two ways as a
`κ`-indexed direct sum of modules whose classes lie in a subclass `S` of `λ⁻`-small ones. -/

section ModuleCore

variable {R}

/-! ## Submodules of a direct sum spanned by a set of indices

`dsPart R N s` is the internal direct sum `⨁_{i ∈ s} N i` inside `⨁ i, N i`. -/


/-! ## Elementary facts about internal direct sums of submodules -/

section Lattice

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- (M2): a direct summand of `M` contained in `D` is a direct summand of `D`. -/
theorem relCompl_of_isCompl {A B : Submodule R M} (h : IsCompl A B) {D : Submodule R M}
    (hAD : A ≤ D) : Disjoint A (B ⊓ D) ∧ A ⊔ (B ⊓ D) = D := by
  refine ⟨h.disjoint.mono_right inf_le_left, le_antisymm (sup_le hAD inf_le_right) ?_⟩
  intro m hm
  have hmem : m ∈ A ⊔ B := by rw [h.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  have hbD : b ∈ D := by
    have hbe : b = m - a := by rw [← hab]; abel
    rw [hbe]
    exact Submodule.sub_mem _ hm (hAD ha)
  exact Submodule.mem_sup.mpr ⟨a, ha, b, ⟨hb, hbD⟩, hab⟩

theorem isCompl_comap_subtype {A B D : Submodule R M} (hd : Disjoint A B) (hs : A ⊔ B = D) :
    IsCompl (A.comap D.subtype) (B.comap D.subtype) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    exact Subtype.ext (Submodule.disjoint_def.mp hd (x : M) hx1 hx2)
  · rw [codisjoint_iff, eq_top_iff]
    rintro x -
    have hx : (x : M) ∈ A ⊔ B := by rw [hs]; exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    have haD : a ∈ D := by rw [← hs]; exact Submodule.mem_sup_left ha
    have hbD : b ∈ D := by rw [← hs]; exact Submodule.mem_sup_right hb
    exact Submodule.mem_sup.mpr ⟨⟨a, haD⟩, ha, ⟨b, hbD⟩, hb, Subtype.ext hab⟩

/-- (M1), relative form: two complements of `A` inside `D` are isomorphic. -/
theorem iso_of_relCompl {A B B' D : Submodule R M} (hd : Disjoint A B) (hs : A ⊔ B = D)
    (hd' : Disjoint A B') (hs' : A ⊔ B' = D) : Nonempty (B ≃ₗ[R] B') := by
  obtain ⟨f⟩ := iso_of_isCompl_left R (isCompl_comap_subtype hd hs) (isCompl_comap_subtype hd' hs')
  have e1 : (B.comap D.subtype) ≃ₗ[R] B :=
    Submodule.comapSubtypeEquivOfLe (hs ▸ le_sup_right)
  have e2 : (B'.comap D.subtype) ≃ₗ[R] B' :=
    Submodule.comapSubtypeEquivOfLe (hs' ▸ le_sup_right)
  exact ⟨e1.symm.trans (f.trans e2)⟩

/-- An internal direct sum of two submodules is the external one. -/
noncomputable def relProdEquiv {A B D : Submodule R M} (hd : Disjoint A B) (hs : A ⊔ B = D) :
    (A × B) ≃ₗ[R] D :=
  (LinearEquiv.prodCongr (Submodule.comapSubtypeEquivOfLe (hs ▸ le_sup_left : A ≤ D)).symm
      (Submodule.comapSubtypeEquivOfLe (hs ▸ le_sup_right : B ≤ D)).symm).trans
    (Submodule.prodEquivOfIsCompl _ _ (isCompl_comap_subtype hd hs))

/-- Isomorphic complements: transporting a complemented pair along a linear equivalence. -/
theorem isCompl_map_equiv {M' : Type u} [AddCommGroup M'] [Module R M'] (f : M ≃ₗ[R] M')
    {A B : Submodule R M} (h : IsCompl A B) :
    IsCompl (A.map (f : M →ₗ[R] M')) (B.map (f : M →ₗ[R] M')) :=
  (Submodule.orderIsoMapComap f).isCompl h

end Lattice

/-- `λ⁻`-smallness only depends on the isomorphism class. -/
theorem IsLambdaSmall.of_equiv {lam : Cardinal.{u}} {M M' : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (h : IsLambdaSmall R lam M) (e : M ≃ₗ[R] M') : IsLambdaSmall R lam M' := by
  intro ι N inst1 inst2 f
  obtain ⟨s, hs, hf⟩ := h N inst1 inst2 (f.comp (e : M →ₗ[R] M'))
  refine ⟨s, hs, fun m i hi => ?_⟩
  have hval := hf (e.symm m) i hi
  simpa using hval

/-! ## Classes of direct sums and of direct summands -/

namespace ModuleClass

variable {κ : Cardinal.{u}} (C : ModuleClass R κ)

theorem eq_zero_of_subsingleton {b : C.carrier} (h : Subsingleton (C.rep b)) : b = C.zero :=
  haveI := h; haveI := C.subsingleton_rep_zero
  C.eq_of_iso (LinearEquiv.ofSubsingleton _ _)

theorem subsingleton_rep_of_eq_zero {b : C.carrier} (h : b = C.zero) :
    Subsingleton (C.rep b) := by
  rw [h]; exact C.subsingleton_rep_zero

/-- A direct sum all of whose summands outside the range of `e` are trivial is the direct sum
indexed by the domain of `e`. -/
theorem restrict_iso {ι : Type u} (g : Idx κ → C.carrier) (e : ι ↪ Idx κ)
    (h : ∀ k, k ∉ Set.range e → Subsingleton (C.rep (g k))) :
    Nonempty ((⨁ k, C.rep (g k)) ≃ₗ[R] ⨁ i : ι, C.rep (g (e i))) :=
  ⟨(dsum_restrict_iso R _ (Set.range e) h).some.trans
    (DirectSum.lequivCongrLeft R (Equiv.ofInjective e e.injective).symm)⟩

/-- The representative of a `κ`-sum of classes is the direct sum of the representatives. -/
theorem rep_sumOf (hκ : ℵ₀ ≤ κ) {ι : Type u} (hι : #ι ≤ κ) (a : ι → C.carrier) :
    letI := C.instKMonoid hκ
    Nonempty (C.rep (sumOf (κ := κ) hι a) ≃ₗ[R] ⨁ i, C.rep (a i)) := by
  letI := C.instKMonoid hκ
  set g : Idx κ → C.carrier := Function.extend (emb hι) a (0 : Idx κ → C.carrier) with hgdef
  have hge : ∀ i, g (emb hι i) = a i :=
    fun i => (emb hι).injective.extend_apply a (0 : Idx κ → C.carrier) i
  have hg0 : ∀ k, k ∉ Set.range (emb hι) → g k = 0 := by
    intro k hk
    exact Function.extend_apply' a (0 : Idx κ → C.carrier) k (fun ⟨i, hi⟩ => hk ⟨i, hi⟩)
  have hsub : ∀ k, k ∉ Set.range (emb hι) → Subsingleton (C.rep (g k)) := by
    intro k hk
    refine C.subsingleton_rep_of_eq_zero ?_
    rw [hg0 k hk]
    exact C.instKMonoid_zero hκ
  have hsum : sumOf (κ := κ) hι a = C.dsum g :=
    (KMonoid.sumOf_eq_extend hι (emb hι) a).trans (C.instKMonoid_ksum hκ g)
  rw [hsum]
  obtain ⟨e1⟩ := C.dsum_iso g
  obtain ⟨e2⟩ := C.restrict_iso g (emb hι) hsub
  have e3 : (⨁ i, C.rep (g (emb hι i))) ≃ₗ[R] ⨁ i, C.rep (a i) :=
    DirectSum.congrLinearEquiv fun i => (C.iso_of_eq (hge i)).some
  exact ⟨e1.trans (e2.trans e3)⟩

/-- The representative of a sum of two classes is the direct sum of the representatives. -/
theorem rep_add (hκ : ℵ₀ ≤ κ) (b b' : C.carrier) :
    letI := C.instKMonoid hκ
    Nonempty (C.rep (b + b') ≃ₗ[R] C.rep b × C.rep b') := by
  letI := C.instKMonoid hκ
  have hUB : #(ULift.{u} Bool) ≤ κ := KMonoid.mk_uLift_bool_le κ C.carrier
  rw [← sumOf_two b b' hUB]
  obtain ⟨e1⟩ := C.rep_sumOf hκ hUB fun p : ULift.{u} Bool => if p.down then b else b'
  exact ⟨e1.trans (dsumUliftBoolProdIso R)⟩

/-- Closure under direct summands, in the form we use it: a direct summand of a module
isomorphic to a representative is again represented by a class. -/
theorem exists_class_of_summand [C.IsSummandClosed] {W : Type u} [AddCommGroup W] [Module R W]
    (A : C.carrier) (φ : C.rep A ≃ₗ[R] W) {N K : Submodule R W} (h : IsCompl N K) :
    ∃ b : C.carrier, Nonempty (C.rep b ≃ₗ[R] ↥N) := by
  have h' := ((Submodule.orderIsoMapComap (φ : C.rep A ≃ₗ[R] W)).symm).isCompl h
  rw [Submodule.orderIsoMapComap_symm_apply, Submodule.orderIsoMapComap_symm_apply] at h'
  obtain ⟨b, hb⟩ := ModuleClass.IsSummandClosed.exists_of_isCompl A _ _ h'
  have hcm : N.comap (φ : C.rep A →ₗ[R] W) = N.map (φ.symm : W →ₗ[R] C.rep A) :=
    Submodule.comap_equiv_eq_map_symm φ N
  exact ⟨b, ⟨hb.some.trans ((LinearEquiv.ofEq _ _ hcm).trans (φ.symm.submoduleMap N).symm)⟩⟩

/-- A relative direct summand is represented by a class. -/
theorem exists_class_of_relCompl [C.IsSummandClosed] {M : Type u} [AddCommGroup M] [Module R M]
    (A : C.carrier) {Y Z E : Submodule R M} (hd : Disjoint Y Z) (hs : Y ⊔ Z = E)
    (φ : C.rep A ≃ₗ[R] ↥E) :
    ∃ b : C.carrier, Nonempty (C.rep b ≃ₗ[R] ↥Y) := by
  obtain ⟨b, hb⟩ := C.exists_class_of_summand A φ (isCompl_comap_subtype hd hs)
  exact ⟨b, ⟨hb.some.trans (Submodule.comapSubtypeEquivOfLe (hs ▸ le_sup_left))⟩⟩

/-- The class of a relative internal direct sum is the sum of the classes. -/
theorem add_eq_of_relCompl (hκ : ℵ₀ ≤ κ) {M : Type u} [AddCommGroup M] [Module R M]
    {Y Z E : Submodule R M} (hd : Disjoint Y Z) (hs : Y ⊔ Z = E) {b c A : C.carrier}
    (hb : Nonempty (C.rep b ≃ₗ[R] ↥Y)) (hc : Nonempty (C.rep c ≃ₗ[R] ↥Z))
    (hA : Nonempty (C.rep A ≃ₗ[R] ↥E)) :
    letI := C.instKMonoid hκ
    b + c = A := by
  letI := C.instKMonoid hκ
  have e : C.rep (b + c) ≃ₗ[R] C.rep A :=
    (C.rep_add hκ b c).some.trans
      ((LinearEquiv.prodCongr hb.some hc.some).trans ((relProdEquiv hd hs).trans hA.some.symm))
  exact C.eq_of_iso e

end ModuleClass

/-! ## Decompositions of a module indexed by `Idx κ` -/

/-- A decomposition of `M` as a direct sum of representatives of the classes `a i`. -/
structure Decomp {κ : Cardinal.{u}} (C : ModuleClass R κ) (M : Type u)
    [AddCommGroup M] [Module R M] (a : Idx κ → C.carrier) where
  iso : M ≃ₗ[R] ⨁ i, C.rep (a i)

namespace Decomp

variable {κ : Cardinal.{u}} {C : ModuleClass R κ} {M : Type u}
  [AddCommGroup M] [Module R M] {a : Idx κ → C.carrier} (D : Decomp C M a)

/-- The submodule `⨁_{i ∈ s} rep (a i)` of `M`. -/
def P (s : Set (Idx κ)) : Submodule R M :=
  (dsPart R (fun i => C.rep (a i)) s).comap (D.iso : M →ₗ[R] ⨁ i, C.rep (a i))

theorem P_eq_orderIso (s : Set (Idx κ)) :
    D.P s = (Submodule.orderIsoMapComap (D.iso : M ≃ₗ[R] ⨁ i, C.rep (a i))).symm
      (dsPart R (fun i => C.rep (a i)) s) := by
  rw [Submodule.orderIsoMapComap_symm_apply]
  rfl

theorem P_mono {s t : Set (Idx κ)} (h : s ⊆ t) : D.P s ≤ D.P t :=
  Submodule.comap_mono (dsPart_mono R _ h)

@[simp] theorem P_univ : D.P Set.univ = ⊤ := by
  rw [P, dsPart_univ, Submodule.comap_top]

theorem P_iUnion {J : Type u} (s : J → Set (Idx κ)) : D.P (⋃ j, s j) = ⨆ j, D.P (s j) := by
  simp only [P_eq_orderIso]
  rw [dsPart_iUnion, OrderIso.map_iSup]

theorem P_union (s t : Set (Idx κ)) : D.P (s ∪ t) = D.P s ⊔ D.P t := by
  simp only [P_eq_orderIso]
  rw [dsPart_union, OrderIso.map_sup]

theorem P_disjoint {s t : Set (Idx κ)} (h : Disjoint s t) : Disjoint (D.P s) (D.P t) := by
  rw [Submodule.disjoint_def]
  intro m hms hmt
  have h0 : D.iso m = 0 :=
    Submodule.disjoint_def.mp (dsPart_disjoint R (fun i => C.rep (a i)) h) (D.iso m) hms hmt
  exact (LinearEquiv.map_eq_zero_iff D.iso).mp h0

theorem P_isCompl (s : Set (Idx κ)) : IsCompl (D.P s) (D.P sᶜ) := by
  refine ⟨D.P_disjoint disjoint_compl_right, ?_⟩
  rw [codisjoint_iff, ← D.P_union, Set.union_compl_self, D.P_univ]

theorem P_iso (s : Set (Idx κ)) :
    Nonempty (↥(D.P s) ≃ₗ[R] ⨁ i : s, C.rep (a i.1)) := by
  have hcm : (dsPart R (fun i => C.rep (a i)) s).comap (D.iso : M →ₗ[R] ⨁ i, C.rep (a i))
      = (dsPart R (fun i => C.rep (a i)) s).map
        (D.iso.symm : (⨁ i, C.rep (a i)) →ₗ[R] M) :=
    Submodule.comap_equiv_eq_map_symm D.iso _
  exact ⟨((LinearEquiv.ofEq _ _ hcm).trans
    ((D.iso.symm.submoduleMap (dsPart R (fun i => C.rep (a i)) s)).symm)).trans
      (dsPartIso R (fun i => C.rep (a i)) s)⟩

/-- `⨁_{i ∈ s} rep (a i)` represents the class `Σ_{i ∈ s} a i`. -/
theorem P_class (hκ : ℵ₀ ≤ κ) (s : Set (Idx κ)) (hs : #s ≤ κ) :
    letI := C.instKMonoid hκ
    Nonempty (C.rep (sumOf (κ := κ) hs (fun i : s => a i.1)) ≃ₗ[R] ↥(D.P s)) := by
  letI := C.instKMonoid hκ
  exact ⟨(C.rep_sumOf hκ hs (fun i : s => a i.1)).some.trans (D.P_iso s).some.symm⟩

/-- `λ⁻`-smallness in action: a `λ⁻`-small submodule is contained in a sub-sum indexed by
`< λ` many indices, which moreover may be taken disjoint from any prescribed set. -/
theorem exists_small_cover {lam : Cardinal.{u}} {T : Submodule R M}
    (hT : IsLambdaSmall R lam ↥T) (s₀ : Set (Idx κ)) :
    ∃ t : Set (Idx κ), #t < lam ∧ Disjoint t s₀ ∧ T ≤ D.P (s₀ ∪ t) := by
  obtain ⟨s, hs, hcomp⟩ := hT (fun i => C.rep (a i)) _ _
    ((D.iso : M →ₗ[R] ⨁ i, C.rep (a i)).comp T.subtype)
  refine ⟨s \ s₀, lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset Set.sdiff_subset) hs,
    Set.disjoint_left.mpr fun i hi hi₀ => hi.2 hi₀, ?_⟩
  intro m hm
  show D.iso m ∈ dsPart R (fun i => C.rep (a i)) (s₀ ∪ (s \ s₀))
  intro i hi
  have hi₀ : i ∉ s₀ := fun h => hi (Or.inl h)
  have his : i ∉ s := fun h => hi (Or.inr ⟨h, hi₀⟩)
  exact hcomp ⟨m, hm⟩ i his

end Decomp

/-! ## The canonical well-order on `Idx κ`

`Idx κ = κ.ord.ToType` is well-ordered with all proper initial segments of cardinality `< κ`;
this is what makes the "adjoin `min I'`" device of the proof of Theorem 4.3 work. -/

section IdxOrder

variable {κ : Cardinal.{u}}

theorem mk_Iio_Idx_lt (i : Idx κ) : #(Set.Iio i) < κ := by
  have h1 : Cardinal.ord #(Idx κ) = @Ordinal.type (Idx κ) (· < ·) inferInstance := by
    rw [mk_Idx, Ordinal.type_toType]
  simpa using Cardinal.mk_Iio_lt i h1

theorem mk_Iic_Idx_lt (hκ : ℵ₀ ≤ κ) (i : Idx κ) : #(Set.Iic i) < κ := by
  have hsub : Set.Iic i ⊆ Set.Iio i ∪ {i} := by
    intro j hj
    rcases lt_or_eq_of_le (Set.mem_Iic.mp hj) with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hsub) ?_
  refine lt_of_le_of_lt (Cardinal.mk_union_le _ _) ?_
  rw [Cardinal.mk_singleton]
  exact Cardinal.add_lt_of_lt hκ (mk_Iio_Idx_lt i) (one_lt_aleph0.trans_le hκ)

/-- The least element of a nonempty subset of `Idx κ`. -/
noncomputable def wfMin (s : Set (Idx κ)) (h : s.Nonempty) : Idx κ :=
  (IsWellFounded.wf (r := ((· < ·) : Idx κ → Idx κ → Prop))).min s h

theorem wfMin_mem (s : Set (Idx κ)) (h : s.Nonempty) : wfMin s h ∈ s :=
  (IsWellFounded.wf (r := ((· < ·) : Idx κ → Idx κ → Prop))).min_mem s h

theorem wfMin_le (s : Set (Idx κ)) (h : s.Nonempty) {i : Idx κ} (hi : i ∈ s) : wfMin s h ≤ i :=
  not_lt.mp ((IsWellFounded.wf (r := ((· < ·) : Idx κ → Idx κ → Prop))).not_lt_min s hi)

end IdxOrder

/-! ## Theorem 4.3: the setting -/

/-- `T` is a representative of the class `b`. -/
def IsRep {κ : Cardinal.{u}} (C : ModuleClass R κ) {M : Type u}
    [AddCommGroup M] [Module R M] (b : C.carrier) (T : Submodule R M) : Prop :=
  Nonempty (C.rep b ≃ₗ[R] ↥T)

/-- All the data and hypotheses of the module-theoretic core of Theorem 4.3: a module `M`
written in two ways as a `κ`-indexed direct sum of modules whose classes lie in the subclass
`S` of `λ⁻`-small modules. -/
structure DoubleDecomp {κ : Cardinal.{u}} (C : ModuleClass R κ)
    (lam : Cardinal.{u}) (M : Type u) [AddCommGroup M] [Module R M] where
  hκ : ℵ₀ ≤ κ
  hlam : lam.IsRegular
  hlk : lam ≤ κ
  S : Set C.carrier
  hsmall : ∀ b ∈ S, IsLambdaSmall R lam (C.rep b)
  hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S
  hSsummand : letI := C.instKMonoid hκ; ∀ b ∈ S, ∀ c : C.carrier, (∃ d, c + d = b) → c ∈ S
  a₁ : Idx κ → C.carrier
  a₂ : Idx κ → C.carrier
  ha₁ : ∀ i, a₁ i ∈ S
  ha₂ : ∀ i, a₂ i ∈ S
  D₁ : Decomp C M a₁
  D₂ : Decomp C M a₂

namespace DoubleDecomp

variable {κ : Cardinal.{u}} {C : ModuleClass R κ} {lam : Cardinal.{u}}
  {M : Type u} [AddCommGroup M] [Module R M] (B : DoubleDecomp C lam M)

theorem zero_mem_S : C.zero ∈ B.S := by
  letI := C.instKMonoid B.hκ
  have h := B.hSsub.zero_mem
  rwa [C.instKMonoid_zero B.hκ] at h

theorem isRep_zero : IsRep C C.zero (⊥ : Submodule R M) :=
  haveI := C.subsingleton_rep_zero
  ⟨LinearEquiv.ofSubsingleton (R := R) (C.rep C.zero) ↥(⊥ : Submodule R M)⟩

theorem empty_small (hlam : lam.IsRegular) : #(∅ : Set (Idx κ)) < lam := by
  have h0 : #(∅ : Set (Idx κ)) = 0 := Cardinal.mk_emptyCollection _
  rw [h0]
  exact lt_of_lt_of_le zero_lt_one (one_le_aleph0.trans (Cardinal.IsRegular.aleph0_le hlam))

/-- One stage of the transfinite construction: the two index blocks, the two submodules and
their classes. -/
structure Step where
  Iset : Set (Idx κ)
  Jset : Set (Idx κ)
  Ssub : Submodule R M
  Tsub : Submodule R M
  uc : C.carrier
  tc : C.carrier
  Ismall : #Iset < lam
  Jsmall : #Jset < lam
  ucS : uc ∈ B.S
  tcS : tc ∈ B.S
  urep : IsRep C uc Ssub
  trep : IsRep C tc Tsub

/-- The trivial stage, used where the construction has nothing left to do. -/
def defaultStep : B.Step where
  Iset := ∅
  Jset := ∅
  Ssub := ⊥
  Tsub := ⊥
  uc := C.zero
  tc := C.zero
  Ismall := empty_small B.hlam
  Jsmall := empty_small B.hlam
  ucS := B.zero_mem_S
  tcS := B.zero_mem_S
  urep := isRep_zero
  trep := isRep_zero

instance : Inhabited B.Step := ⟨B.defaultStep⟩

/-- What one stage of the construction achieves, relative to the blocks `Uidx`, `Jidx` used so
far and the module `Told` (the paper's `T_α`) that has to be absorbed. -/
structure StepProps (Uidx Jidx : Set (Idx κ)) (Told : Submodule R M) (vc : C.carrier)
    (st : B.Step) : Prop where
  /-- The new blocks are fresh. -/
  Isub : st.Iset ⊆ Uidxᶜ
  Jsub : st.Jset ⊆ Jidxᶜ
  /-- The least unused index is used; this forces the blocks to exhaust `Idx κ`. -/
  minMem : ∀ h : (Uidxᶜ).Nonempty, wfMin Uidxᶜ h ∈ st.Iset
  ToldLe : Told ≤ B.D₁.P (Uidx ∪ st.Iset)
  Tdisj : Disjoint st.Tsub (B.D₁.P (Uidx ∪ st.Iset))
  Teq : st.Tsub ⊔ B.D₁.P (Uidx ∪ st.Iset) = B.D₂.P (Jidx ∪ st.Jset)
  hI : letI := C.instKMonoid B.hκ
    sumOf (κ := κ) (st.Ismall.le.trans B.hlk) (fun i : st.Iset => B.a₁ i.1) = vc + st.uc
  hJ : letI := C.instKMonoid B.hκ
    sumOf (κ := κ) (st.Jsmall.le.trans B.hlk) (fun j : st.Jset => B.a₂ j.1) = st.tc + st.uc

/-! From here on the class must be closed under direct summands: the recursion splits off
complements at every step.  See `ModuleClass.IsSummandClosed`. -/

variable [C.IsSummandClosed]

/-- **The recursion step of Theorem 4.3.**  Given that `Told ⊕ ⨁_{i ∈ Uidx} A i` is the
internal sum `⨁_{j ∈ Jidx} B j`, we find fresh blocks `I_α`, `J_α` of size `< λ` and modules
`S_α`, `T_{α+1}` continuing the two decompositions. -/
theorem exists_step (Uidx Jidx : Set (Idx κ)) (Told : Submodule R M) (vc : C.carrier)
    (hvcS : vc ∈ B.S) (hvrep : IsRep C vc Told)
    (hdisj : Disjoint Told (B.D₁.P Uidx))
    (heq : Told ⊔ B.D₁.P Uidx = B.D₂.P Jidx) :
    ∃ st : B.Step, B.StepProps Uidx Jidx Told vc st := by
  letI := C.instKMonoid B.hκ
  have hlam0 : ℵ₀ ≤ lam := Cardinal.IsRegular.aleph0_le B.hlam
  have hlam1 : (1 : Cardinal) < lam := lt_of_lt_of_le one_lt_aleph0 hlam0
  by_cases hUc : (Uidxᶜ : Set (Idx κ)).Nonempty
  · -- the main case
    have hi₀ : wfMin Uidxᶜ hUc ∈ Uidxᶜ := wfMin_mem _ hUc
    -- `T_α` is `λ⁻`-small, so it lands in a sub-sum indexed by `< λ` fresh indices
    have hTsmall : IsLambdaSmall R lam ↥Told := IsLambdaSmall.of_equiv (B.hsmall vc hvcS) hvrep.some
    obtain ⟨t, ht_lt, ht_disj, ht_le⟩ := B.D₁.exists_small_cover hTsmall Uidx
    have hIset_lt : #((t ∪ {wfMin Uidxᶜ hUc} : Set (Idx κ))) < lam := by
      refine lt_of_le_of_lt (Cardinal.mk_union_le _ _) ?_
      rw [Cardinal.mk_singleton]
      exact Cardinal.add_lt_of_lt hlam0 ht_lt hlam1
    have hIsub : (t ∪ {wfMin Uidxᶜ hUc} : Set (Idx κ)) ⊆ Uidxᶜ := by
      rintro i (hi | hi)
      · exact fun hU => Set.disjoint_left.mp ht_disj hi hU
      · rw [Set.mem_singleton_iff.mp hi]; exact hi₀
    have hUdisjI : Disjoint Uidx (t ∪ {wfMin Uidxᶜ hUc} : Set (Idx κ)) :=
      Set.disjoint_left.mpr fun i hi hi' => hIsub hi' hi
    have hToldLe : Told ≤ B.D₁.P (Uidx ∪ (t ∪ {wfMin Uidxᶜ hUc})) :=
      ht_le.trans (B.D₁.P_mono (Set.union_subset_union_right _ Set.subset_union_left))
    -- (M2): split off `S_α` inside `⨁_{μ ≤ α} ⨁_{i ∈ I_μ} A i`
    have hPJ_le : B.D₂.P Jidx ≤ B.D₁.P (Uidx ∪ (t ∪ {wfMin Uidxᶜ hUc})) := by
      rw [← heq]
      exact sup_le hToldLe (B.D₁.P_mono Set.subset_union_left)
    obtain ⟨hd1, hs1⟩ := relCompl_of_isCompl (B.D₂.P_isCompl Jidx) hPJ_le
    set Ssub : Submodule R M :=
      B.D₂.P Jidxᶜ ⊓ B.D₁.P (Uidx ∪ (t ∪ {wfMin Uidxᶜ hUc})) with hSsubdef
    have hSsub_le : Ssub ≤ B.D₁.P (Uidx ∪ (t ∪ {wfMin Uidxᶜ hUc})) := by
      rw [hSsubdef]; exact inf_le_right
    have hTold_le_PJ : Told ≤ B.D₂.P Jidx := heq ▸ le_sup_left
    have hdTS : Disjoint Told Ssub := hd1.mono_left hTold_le_PJ
    -- (M1): `S_α ⊕ T_α ≅ ⨁_{i ∈ I_α} A i`
    have hd_U_TS : Disjoint (B.D₁.P Uidx) (Told ⊔ Ssub) := by
      refine hdisj.symm.disjoint_sup_right_of_disjoint_sup_left ?_
      rw [sup_comm]
      exact hd1.mono_left (le_of_eq heq)
    have hs_U_TS : B.D₁.P Uidx ⊔ (Told ⊔ Ssub)
        = B.D₁.P (Uidx ∪ (t ∪ {wfMin Uidxᶜ hUc})) := by
      rw [← sup_assoc, sup_comm (B.D₁.P Uidx) Told, heq, hs1]
    obtain ⟨eTS⟩ := iso_of_relCompl hd_U_TS hs_U_TS (B.D₁.P_disjoint hUdisjI)
      (B.D₁.P_union _ _).symm
    have hIle : #((t ∪ {wfMin Uidxᶜ hUc} : Set (Idx κ))) ≤ κ := hIset_lt.le.trans B.hlk
    have hA₁rep : Nonempty (C.rep (sumOf (κ := κ) hIle
        (fun i : (t ∪ {wfMin Uidxᶜ hUc} : Set (Idx κ)) => B.a₁ i.1)) ≃ₗ[R]
          ↥(Told ⊔ Ssub)) :=
      ⟨(B.D₁.P_class B.hκ _ hIle).some.trans eTS.symm⟩
    obtain ⟨uc, hucrep⟩ := C.exists_class_of_relCompl _ hdTS.symm (sup_comm Ssub Told) hA₁rep.some
    have hA₁S : sumOf (κ := κ) hIle
        (fun i : (t ∪ {wfMin Uidxᶜ hUc} : Set (Idx κ)) => B.a₁ i.1) ∈ B.S :=
      B.hSsub.sumOf_mem hIset_lt _ (fun i => B.ha₁ i.1)
    have hIsum : vc + uc = sumOf (κ := κ) hIle
        (fun i : (t ∪ {wfMin Uidxᶜ hUc} : Set (Idx κ)) => B.a₁ i.1) :=
      C.add_eq_of_relCompl B.hκ hdTS rfl hvrep hucrep hA₁rep
    have hucS : uc ∈ B.S := B.hSsummand _ hA₁S uc ⟨vc, by rw [add_comm]; exact hIsum⟩
    -- now the same on the second decomposition
    have hSsmall : IsLambdaSmall R lam ↥Ssub := IsLambdaSmall.of_equiv (B.hsmall uc hucS) hucrep.some
    obtain ⟨t', ht'_lt, ht'_disj, ht'_le⟩ := B.D₂.exists_small_cover hSsmall Jidx
    have hP1_le : B.D₁.P (Uidx ∪ (t ∪ {wfMin Uidxᶜ hUc})) ≤ B.D₂.P (Jidx ∪ t') := by
      rw [← hs1]
      exact sup_le (B.D₂.P_mono Set.subset_union_left) ht'_le
    obtain ⟨hd2, hs2⟩ :=
      relCompl_of_isCompl (B.D₁.P_isCompl (Uidx ∪ (t ∪ {wfMin Uidxᶜ hUc}))) hP1_le
    set Tsub : Submodule R M :=
      B.D₁.P (Uidx ∪ (t ∪ {wfMin Uidxᶜ hUc}))ᶜ ⊓ B.D₂.P (Jidx ∪ t') with hTsubdef
    have hd_S_T : Disjoint Ssub Tsub := hd2.mono_left hSsub_le
    have hd_J_ST : Disjoint (B.D₂.P Jidx) (Ssub ⊔ Tsub) := by
      refine hd1.disjoint_sup_right_of_disjoint_sup_left ?_
      rw [hs1]; exact hd2
    have hs_J_ST : B.D₂.P Jidx ⊔ (Ssub ⊔ Tsub) = B.D₂.P (Jidx ∪ t') := by
      rw [← sup_assoc, hs1, hs2]
    obtain ⟨eST⟩ := iso_of_relCompl hd_J_ST hs_J_ST
      (B.D₂.P_disjoint ht'_disj.symm) (B.D₂.P_union _ _).symm
    have hJle : #((t' : Set (Idx κ))) ≤ κ := ht'_lt.le.trans B.hlk
    have hA₂rep : Nonempty (C.rep (sumOf (κ := κ) hJle (fun j : (t' : Set (Idx κ)) => B.a₂ j.1))
        ≃ₗ[R] ↥(Tsub ⊔ Ssub)) :=
      ⟨((B.D₂.P_class B.hκ _ hJle).some.trans eST.symm).trans
        (LinearEquiv.ofEq _ _ (sup_comm Ssub Tsub))⟩
    obtain ⟨tc, htcrep⟩ := C.exists_class_of_relCompl _ hd_S_T.symm rfl hA₂rep.some
    have hA₂S : sumOf (κ := κ) hJle (fun j : (t' : Set (Idx κ)) => B.a₂ j.1) ∈ B.S :=
      B.hSsub.sumOf_mem ht'_lt _ (fun j => B.ha₂ j.1)
    have hJsum : tc + uc = sumOf (κ := κ) hJle (fun j : (t' : Set (Idx κ)) => B.a₂ j.1) :=
      C.add_eq_of_relCompl B.hκ hd_S_T.symm rfl htcrep hucrep hA₂rep
    have htcS : tc ∈ B.S := B.hSsummand _ hA₂S tc ⟨uc, hJsum⟩
    refine ⟨{ Iset := t ∪ {wfMin Uidxᶜ hUc}, Jset := t', Ssub := Ssub, Tsub := Tsub
              uc := uc, tc := tc, Ismall := hIset_lt, Jsmall := ht'_lt, ucS := hucS
              tcS := htcS, urep := hucrep, trep := htcrep },
      { Isub := hIsub
        Jsub := fun j hj hJ => Set.disjoint_left.mp ht'_disj hj hJ
        minMem := fun h => Set.mem_union_right _ (Set.mem_singleton_iff.mpr rfl)
        ToldLe := hToldLe
        Tdisj := hd2.symm
        Teq := by rw [sup_comm]; exact hs2
        hI := hIsum.symm
        hJ := hJsum.symm }⟩
  · -- degenerate case: all indices of the first decomposition are already used
    have hUuniv : Uidx = Set.univ := by
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hUc
      exact hUc
    have hPtop : B.D₁.P Uidx = ⊤ := by rw [hUuniv, B.D₁.P_univ]
    have hTold : Told = ⊥ := disjoint_top.mp (hPtop ▸ hdisj)
    haveI hsubT : Subsingleton ↥Told := by rw [hTold]; infer_instance
    have hvc0 : vc = C.zero :=
      C.eq_zero_of_subsingleton (Equiv.subsingleton hvrep.some.toEquiv)
    refine ⟨B.defaultStep, ?_⟩
    refine
      { Isub := Set.empty_subset _
        Jsub := Set.empty_subset _
        minMem := ?_
        ToldLe := ?_
        Tdisj := disjoint_bot_left
        Teq := ?_
        hI := ?_
        hJ := ?_ }
    · intro h
      exact absurd h (by rw [Set.not_nonempty_iff_eq_empty, hUuniv, Set.compl_univ])
    · rw [hTold]; exact bot_le
    · show (⊥ : Submodule R M) ⊔ B.D₁.P (Uidx ∪ ∅) = B.D₂.P (Jidx ∪ ∅)
      rw [Set.union_empty, Set.union_empty, ← heq, hTold]
    · show sumOf (κ := κ) _ (fun i : (∅ : Set (Idx κ)) => B.a₁ i.1) = vc + C.zero
      rw [hvc0, ← C.instKMonoid_zero B.hκ, add_zero]
      exact KMonoid.sumOf_of_isEmpty _ _
    · show sumOf (κ := κ) _ (fun j : (∅ : Set (Idx κ)) => B.a₂ j.1) = C.zero + C.zero
      rw [← C.instKMonoid_zero B.hκ, add_zero]
      exact KMonoid.sumOf_of_isEmpty _ _

/-- The step as a function; junk outside the intended domain. -/
noncomputable def stepCore (Uidx Jidx : Set (Idx κ)) (Told : Submodule R M) (vc : C.carrier) :
    B.Step :=
  if h : vc ∈ B.S ∧ IsRep C vc Told ∧ Disjoint Told (B.D₁.P Uidx) ∧
      Told ⊔ B.D₁.P Uidx = B.D₂.P Jidx then
    (B.exists_step Uidx Jidx Told vc h.1 h.2.1 h.2.2.1 h.2.2.2).choose
  else B.defaultStep

theorem stepCore_spec {Uidx Jidx : Set (Idx κ)} {Told : Submodule R M} {vc : C.carrier}
    (h1 : vc ∈ B.S) (h2 : IsRep C vc Told) (h3 : Disjoint Told (B.D₁.P Uidx))
    (h4 : Told ⊔ B.D₁.P Uidx = B.D₂.P Jidx) :
    B.StepProps Uidx Jidx Told vc (B.stepCore Uidx Jidx Told vc) := by
  have heq : B.stepCore Uidx Jidx Told vc
      = (B.exists_step Uidx Jidx Told vc h1 h2 h3 h4).choose := by
    unfold stepCore
    rw [dif_pos (⟨h1, h2, h3, h4⟩ : vc ∈ B.S ∧ IsRep C vc Told ∧ Disjoint Told (B.D₁.P Uidx) ∧
      Told ⊔ B.D₁.P Uidx = B.D₂.P Jidx)]
  rw [heq]
  exact (B.exists_step Uidx Jidx Told vc h1 h2 h3 h4).choose_spec

/-! ### The transfinite recursion -/

open IsBraided in
/-- The indices of the first decomposition used strictly before `μ`. -/
def UidxOf (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : Set (Idx κ) :=
  ⋃ ν ∈ {ν | kOrd (Idx κ) ν μ}, (F ν).Iset

open IsBraided in
/-- The indices of the second decomposition used strictly before `μ`. -/
def JidxOf (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : Set (Idx κ) :=
  ⋃ ν ∈ {ν | kOrd (Idx κ) ν μ}, (F ν).Jset

/-- The paper's `T_μ`: the module carried over from the preceding stage; `0` at limits. -/
def TmOf (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : Submodule R M :=
  if μ.2 = 0 then ⊥ else (F (μ.1, μ.2 - 1)).Tsub

/-- The class of `T_μ`. -/
def vcOf (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : C.carrier :=
  if μ.2 = 0 then C.zero else (F (μ.1, μ.2 - 1)).tc

theorem vcOf_mem (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : B.vcOf F μ ∈ B.S := by
  unfold vcOf
  by_cases h : μ.2 = 0
  · rw [if_pos h]; exact B.zero_mem_S
  · rw [if_neg h]; exact (F (μ.1, μ.2 - 1)).tcS

theorem vcOf_rep (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : IsRep C (B.vcOf F μ) (B.TmOf F μ) := by
  unfold vcOf TmOf
  by_cases h : μ.2 = 0
  · rw [if_pos h, if_pos h]; exact isRep_zero
  · rw [if_neg h, if_neg h]; exact (F (μ.1, μ.2 - 1)).trep

noncomputable def stepOf (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : B.Step :=
  B.stepCore (B.UidxOf F μ) (B.JidxOf F μ) (B.TmOf F μ) (B.vcOf F μ)

open IsBraided in
theorem stepOf_congr {F G : Idx κ × ℕ → B.Step} {μ : Idx κ × ℕ}
    (h : ∀ ν, kOrd (Idx κ) ν μ → F ν = G ν) : B.stepOf F μ = B.stepOf G μ := by
  have hU : B.UidxOf F μ = B.UidxOf G μ := by
    unfold UidxOf
    exact Set.iUnion₂_congr fun ν hν => by rw [h ν hν]
  have hJ : B.JidxOf F μ = B.JidxOf G μ := by
    unfold JidxOf
    exact Set.iUnion₂_congr fun ν hν => by rw [h ν hν]
  have hT : B.TmOf F μ = B.TmOf G μ := by
    unfold TmOf
    by_cases hμ : μ.2 = 0
    · rw [if_pos hμ, if_pos hμ]
    · rw [if_neg hμ, if_neg hμ, h _ (kOrd_pred hμ)]
  have hv : B.vcOf F μ = B.vcOf G μ := by
    unfold vcOf
    by_cases hμ : μ.2 = 0
    · rw [if_pos hμ, if_pos hμ]
    · rw [if_neg hμ, if_neg hμ, h _ (kOrd_pred hμ)]
  unfold stepOf
  rw [hU, hJ, hT, hv]

open IsBraided in
noncomputable def stepFun (μ : Idx κ × ℕ) (prev : ∀ ν, kOrd (Idx κ) ν μ → B.Step) : B.Step :=
  B.stepOf (fun ν => if h : kOrd (Idx κ) ν μ then prev ν h else B.defaultStep) μ

open IsBraided in
/-- The transfinite construction of Theorem 4.3, run along the limit well-order `kOrd`. -/
noncomputable def fam : Idx κ × ℕ → B.Step := (kOrd_wf (ι := Idx κ)).fix B.stepFun

open IsBraided in
theorem fam_eq (μ : Idx κ × ℕ) : B.fam μ = B.stepOf B.fam μ := by
  show (kOrd_wf (ι := Idx κ)).fix B.stepFun μ = _
  rw [WellFounded.fix_eq]
  unfold stepFun
  exact B.stepOf_congr fun ν hν => by rw [dif_pos hν]; rfl

/-- The paper's `⨁_{μ < α} ⨁_{i ∈ I_μ} A i`, on the index side. -/
noncomputable def Uidx (μ : Idx κ × ℕ) : Set (Idx κ) := B.UidxOf B.fam μ

/-- The paper's `⨁_{μ < α} ⨁_{j ∈ J_μ} B j`, on the index side. -/
noncomputable def Jidx (μ : Idx κ × ℕ) : Set (Idx κ) := B.JidxOf B.fam μ

/-- The paper's `T_α`. -/
noncomputable def Tm (μ : Idx κ × ℕ) : Submodule R M := B.TmOf B.fam μ

/-- The class of the paper's `T_α`. -/
noncomputable def vcm (μ : Idx κ × ℕ) : C.carrier := B.vcOf B.fam μ

theorem fam_spec (μ : Idx κ × ℕ) (h3 : Disjoint (B.Tm μ) (B.D₁.P (B.Uidx μ)))
    (h4 : B.Tm μ ⊔ B.D₁.P (B.Uidx μ) = B.D₂.P (B.Jidx μ)) :
    B.StepProps (B.Uidx μ) (B.Jidx μ) (B.Tm μ) (B.vcm μ) (B.fam μ) := by
  rw [B.fam_eq μ]
  exact B.stepCore_spec (B.vcOf_mem B.fam μ) (B.vcOf_rep B.fam μ) h3 h4

open IsBraided in
theorem mem_Uidx {μ : Idx κ × ℕ} {i : Idx κ} :
    i ∈ B.Uidx μ ↔ ∃ ν, kOrd (Idx κ) ν μ ∧ i ∈ (B.fam ν).Iset := by
  unfold Uidx UidxOf
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

open IsBraided in
theorem mem_Jidx {μ : Idx κ × ℕ} {j : Idx κ} :
    j ∈ B.Jidx μ ↔ ∃ ν, kOrd (Idx κ) ν μ ∧ j ∈ (B.fam ν).Jset := by
  unfold Jidx JidxOf
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

open IsBraided in
theorem Uidx_bsucc (μ : Idx κ × ℕ) : B.Uidx (bsucc μ) = B.Uidx μ ∪ (B.fam μ).Iset := by
  ext i
  simp only [B.mem_Uidx, Set.mem_union]
  constructor
  · rintro ⟨ν, hν, hi⟩
    rcases kOrd_lt_bsucc_iff.mp hν with h | rfl
    · exact Or.inl ⟨ν, h, hi⟩
    · exact Or.inr hi
  · rintro (⟨ν, hν, hi⟩ | hi)
    · exact ⟨ν, kOrd_trans hν (kOrd_bsucc μ), hi⟩
    · exact ⟨μ, kOrd_bsucc μ, hi⟩

open IsBraided in
theorem Jidx_bsucc (μ : Idx κ × ℕ) : B.Jidx (bsucc μ) = B.Jidx μ ∪ (B.fam μ).Jset := by
  ext j
  simp only [B.mem_Jidx, Set.mem_union]
  constructor
  · rintro ⟨ν, hν, hj⟩
    rcases kOrd_lt_bsucc_iff.mp hν with h | rfl
    · exact Or.inl ⟨ν, h, hj⟩
    · exact Or.inr hj
  · rintro (⟨ν, hν, hj⟩ | hj)
    · exact ⟨ν, kOrd_trans hν (kOrd_bsucc μ), hj⟩
    · exact ⟨μ, kOrd_bsucc μ, hj⟩

theorem Tm_bsucc (μ : Idx κ × ℕ) : B.Tm (bsucc μ) = (B.fam μ).Tsub := by
  unfold Tm TmOf
  rw [if_neg (bsucc_snd_ne_zero μ)]
  rfl

theorem vcm_bsucc (μ : Idx κ × ℕ) : B.vcm (bsucc μ) = (B.fam μ).tc := by
  unfold vcm vcOf
  rw [if_neg (bsucc_snd_ne_zero μ)]
  rfl

theorem Tm_limit {μ : Idx κ × ℕ} (h : μ.2 = 0) : B.Tm μ = ⊥ := by
  unfold Tm TmOf; rw [if_pos h]

theorem vcm_limit {μ : Idx κ × ℕ} (h : μ.2 = 0) : B.vcm μ = C.zero := by
  unfold vcm vcOf; rw [if_pos h]

open IsBraided in
theorem Uidx_mono {ρ μ : Idx κ × ℕ} (h : kOrd (Idx κ) ρ μ) : B.Uidx ρ ⊆ B.Uidx μ := by
  intro i hi
  obtain ⟨ν, hν, hiν⟩ := B.mem_Uidx.mp hi
  exact B.mem_Uidx.mpr ⟨ν, kOrd_trans hν h, hiν⟩

open IsBraided in
theorem Jidx_mono {ρ μ : Idx κ × ℕ} (h : kOrd (Idx κ) ρ μ) : B.Jidx ρ ⊆ B.Jidx μ := by
  intro j hj
  obtain ⟨ν, hν, hjν⟩ := B.mem_Jidx.mp hj
  exact B.mem_Jidx.mpr ⟨ν, kOrd_trans hν h, hjν⟩

/-! ### The invariant -/

open IsBraided in
/-- At a limit position the blocks used so far are the union of those used before any earlier
position. -/
theorem Uidx_limit_eq {μ : Idx κ × ℕ} (h : μ.2 = 0) :
    B.Uidx μ = ⋃ ρ : {ρ : Idx κ × ℕ // kOrd (Idx κ) ρ μ}, B.Uidx ρ.1 := by
  apply Set.eq_of_subset_of_subset
  · intro i hi
    obtain ⟨ν, hν, hiν⟩ := B.mem_Uidx.mp hi
    have hsucc : kOrd (Idx κ) (bsucc ν) μ := by
      rw [kOrd_iff] at hν ⊢
      rcases hν with h1 | ⟨_, h2⟩
      · exact Or.inl h1
      · omega
    refine Set.mem_iUnion.mpr ⟨⟨bsucc ν, hsucc⟩, ?_⟩
    rw [B.Uidx_bsucc ν]
    exact Or.inr hiν
  · intro i hi
    obtain ⟨ρ, hiρ⟩ := Set.mem_iUnion.mp hi
    exact B.Uidx_mono ρ.2 hiρ

open IsBraided in
theorem Jidx_limit_eq {μ : Idx κ × ℕ} (h : μ.2 = 0) :
    B.Jidx μ = ⋃ ρ : {ρ : Idx κ × ℕ // kOrd (Idx κ) ρ μ}, B.Jidx ρ.1 := by
  apply Set.eq_of_subset_of_subset
  · intro j hj
    obtain ⟨ν, hν, hjν⟩ := B.mem_Jidx.mp hj
    have hsucc : kOrd (Idx κ) (bsucc ν) μ := by
      rw [kOrd_iff] at hν ⊢
      rcases hν with h1 | ⟨_, h2⟩
      · exact Or.inl h1
      · omega
    refine Set.mem_iUnion.mpr ⟨⟨bsucc ν, hsucc⟩, ?_⟩
    rw [B.Jidx_bsucc ν]
    exact Or.inr hjν
  · intro j hj
    obtain ⟨ρ, hjρ⟩ := Set.mem_iUnion.mp hj
    exact B.Jidx_mono ρ.2 hjρ

open IsBraided in
/-- The invariant of the construction: `T_α ⊕ ⨁_{μ<α} ⨁_{i ∈ I_μ} A i = ⨁_{μ<α} ⨁_{j ∈ J_μ} B j`
(the paper's `(eq:limit-sum-finite)`). -/
theorem inv (μ : Idx κ × ℕ) : Disjoint (B.Tm μ) (B.D₁.P (B.Uidx μ)) ∧
    B.Tm μ ⊔ B.D₁.P (B.Uidx μ) = B.D₂.P (B.Jidx μ) := by
  induction μ using (kOrd_wf (ι := Idx κ)).induction with
  | _ μ ih =>
    by_cases hμ : μ.2 = 0
    · -- limit position: take unions of the invariant at all earlier positions
      refine ⟨by rw [B.Tm_limit hμ]; exact disjoint_bot_left, ?_⟩
      rw [B.Tm_limit hμ, bot_sup_eq]
      rw [B.Uidx_limit_eq hμ, B.Jidx_limit_eq hμ, B.D₁.P_iUnion, B.D₂.P_iUnion]
      refine le_antisymm (iSup_le fun ρ => ?_) (iSup_le fun ρ => ?_)
      · -- `⨁_{i ∈ Uidx ρ} A i ≤ ⨁_{j ∈ Jidx ρ} B j ≤ ⨆ …`
        refine le_trans ?_ (le_iSup (fun ρ : {ρ : Idx κ × ℕ // kOrd (Idx κ) ρ μ} =>
          B.D₂.P (B.Jidx ρ.1)) ρ)
        rw [← (ih ρ.1 ρ.2).2]
        exact le_sup_right
      · -- conversely `T_ρ ≤ ⨁_{i ∈ Uidx (bsucc ρ)} A i`
        rw [← (ih ρ.1 ρ.2).2]
        refine sup_le ?_ ?_
        · have hsucc : kOrd (Idx κ) (bsucc ρ.1) μ := by
            have hν := ρ.2
            rw [kOrd_iff] at hν ⊢
            rcases hν with h1 | ⟨_, h2⟩
            · exact Or.inl h1
            · omega
          refine le_trans ?_ (le_iSup
            (fun j : {ρ : Idx κ × ℕ // kOrd (Idx κ) ρ μ} => B.D₁.P (B.Uidx j.1))
            (⟨bsucc ρ.1, hsucc⟩ : {ρ : Idx κ × ℕ // kOrd (Idx κ) ρ μ}))
          rw [show B.Uidx (bsucc ρ.1) = B.Uidx ρ.1 ∪ (B.fam ρ.1).Iset from B.Uidx_bsucc ρ.1]
          exact (B.fam_spec ρ.1 (ih ρ.1 ρ.2).1 (ih ρ.1 ρ.2).2).ToldLe
        · exact le_iSup (fun ρ : {ρ : Idx κ × ℕ // kOrd (Idx κ) ρ μ} => B.D₁.P (B.Uidx ρ.1)) ρ
    · -- successor position
      set ρ : Idx κ × ℕ := (μ.1, μ.2 - 1) with hρdef
      have hbs : bsucc ρ = μ := bsucc_prev hμ
      have hlt : kOrd (Idx κ) ρ μ := kOrd_pred hμ
      have hsp := B.fam_spec ρ (ih ρ hlt).1 (ih ρ hlt).2
      rw [← hbs, B.Uidx_bsucc ρ, B.Jidx_bsucc ρ, B.Tm_bsucc ρ]
      exact ⟨hsp.Tdisj, hsp.Teq⟩

/-! ### The two index families are partitions -/

open IsBraided in
/-- The construction satisfies its own hypotheses at every position. -/
theorem spec (μ : Idx κ × ℕ) :
    B.StepProps (B.Uidx μ) (B.Jidx μ) (B.Tm μ) (B.vcm μ) (B.fam μ) :=
  B.fam_spec μ (B.inv μ).1 (B.inv μ).2

open IsBraided in
theorem Iset_subset_Uidx {ν μ : Idx κ × ℕ} (h : kOrd (Idx κ) ν μ) :
    (B.fam ν).Iset ⊆ B.Uidx μ := fun _ hi => B.mem_Uidx.mpr ⟨ν, h, hi⟩

open IsBraided in
theorem Jset_subset_Jidx {ν μ : Idx κ × ℕ} (h : kOrd (Idx κ) ν μ) :
    (B.fam ν).Jset ⊆ B.Jidx μ := fun _ hj => B.mem_Jidx.mpr ⟨ν, h, hj⟩

open IsBraided in
theorem Iset_disjoint {μ ρ : Idx κ × ℕ} (h : μ ≠ ρ) :
    Disjoint (B.fam μ).Iset (B.fam ρ).Iset := by
  rcases trichotomous_of (kOrd (Idx κ)) μ ρ with h1 | h1 | h1
  · exact Set.disjoint_left.mpr fun i hi hi' => (B.spec ρ).Isub hi' (B.Iset_subset_Uidx h1 hi)
  · exact absurd h1 h
  · exact Set.disjoint_left.mpr fun i hi hi' => (B.spec μ).Isub hi (B.Iset_subset_Uidx h1 hi')

open IsBraided in
theorem Jset_disjoint {μ ρ : Idx κ × ℕ} (h : μ ≠ ρ) :
    Disjoint (B.fam μ).Jset (B.fam ρ).Jset := by
  rcases trichotomous_of (kOrd (Idx κ)) μ ρ with h1 | h1 | h1
  · exact Set.disjoint_left.mpr fun j hj hj' => (B.spec ρ).Jsub hj' (B.Jset_subset_Jidx h1 hj)
  · exact absurd h1 h
  · exact Set.disjoint_left.mpr fun j hj hj' => (B.spec μ).Jsub hj (B.Jset_subset_Jidx h1 hj')

open IsBraided in
theorem Uidx_subset_iUnion (μ : Idx κ × ℕ) : B.Uidx μ ⊆ ⋃ ν, (B.fam ν).Iset := by
  intro i hi
  obtain ⟨ν, _, hiν⟩ := B.mem_Uidx.mp hi
  exact Set.mem_iUnion.mpr ⟨ν, hiν⟩

open IsBraided in
theorem Uidx_iUnion : (⋃ μ, B.Uidx μ) = ⋃ ν, (B.fam ν).Iset := by
  apply Set.eq_of_subset_of_subset
  · exact Set.iUnion_subset fun μ => B.Uidx_subset_iUnion μ
  · refine Set.iUnion_subset fun ν i hi => Set.mem_iUnion.mpr ⟨bsucc ν, ?_⟩
    exact B.Iset_subset_Uidx (kOrd_bsucc ν) hi

open IsBraided in
theorem Jidx_iUnion : (⋃ μ, B.Jidx μ) = ⋃ ν, (B.fam ν).Jset := by
  apply Set.eq_of_subset_of_subset
  · refine Set.iUnion_subset fun μ j hj => ?_
    obtain ⟨ν, _, hjν⟩ := B.mem_Jidx.mp hj
    exact Set.mem_iUnion.mpr ⟨ν, hjν⟩
  · refine Set.iUnion_subset fun ν j hj => Set.mem_iUnion.mpr ⟨bsucc ν, ?_⟩
    exact B.Jset_subset_Jidx (kOrd_bsucc ν) hj

/-- The blocks `I_μ` exhaust `Idx κ`: this is the point of always adjoining `min I'`. -/
theorem Iset_cover : (⋃ μ, (B.fam μ).Iset) = Set.univ := by
  by_contra hne
  obtain ⟨i₀, hi₀⟩ : ((⋃ μ, (B.fam μ).Iset)ᶜ).Nonempty := Set.nonempty_compl.mpr hne
  have hne_μ : ∀ μ, ((B.Uidx μ)ᶜ).Nonempty :=
    fun μ => ⟨i₀, fun h => hi₀ (B.Uidx_subset_iUnion μ h)⟩
  set f : Idx κ × ℕ → Idx κ := fun μ => wfMin ((B.Uidx μ)ᶜ) (hne_μ μ) with hfdef
  have hfI : ∀ μ, f μ ∈ (B.fam μ).Iset := fun μ => (B.spec μ).minMem (hne_μ μ)
  have hfle : ∀ μ, f μ ∈ Set.Iic i₀ := fun μ =>
    Set.mem_Iic.mpr (wfMin_le _ _ (fun h => hi₀ (B.Uidx_subset_iUnion μ h)))
  have hinj : Function.Injective (fun μ : Idx κ × ℕ => (⟨f μ, hfle μ⟩ : Set.Iic i₀)) := by
    intro μ ρ h
    by_contra hne'
    have hval : f μ = f ρ := congrArg Subtype.val h
    exact Set.disjoint_left.mp (B.Iset_disjoint hne') (hfI μ) (hval ▸ hfI ρ)
  have h1 : #(Idx κ × ℕ) ≤ #(Set.Iic i₀) := Cardinal.mk_le_of_injective hinj
  have h2 : κ ≤ #(Idx κ × ℕ) := by
    have hinj2 : Function.Injective (fun i : Idx κ => (i, (0 : ℕ))) :=
      fun i j h => (Prod.ext_iff.mp h).1
    calc κ = #(Idx κ) := (mk_Idx κ).symm
      _ ≤ #(Idx κ × ℕ) := Cardinal.mk_le_of_injective hinj2
  exact absurd ((h2.trans h1).trans_lt (mk_Iic_Idx_lt B.hκ i₀)) (lt_irrefl κ)

/-- Consequently the second decomposition is exhausted as well. -/
theorem P₂_iUnion_eq_top : B.D₂.P (⋃ ν, (B.fam ν).Jset) = ⊤ := by
  have h1 : B.D₂.P (⋃ ν, (B.fam ν).Jset) = ⨆ μ, B.D₂.P (B.Jidx μ) := by
    rw [← B.Jidx_iUnion, B.D₂.P_iUnion]
  rw [h1, eq_top_iff, ← B.D₁.P_univ, ← B.Iset_cover, ← B.Uidx_iUnion, B.D₁.P_iUnion]
  refine iSup_le fun μ => le_trans ?_ (le_iSup (fun μ => B.D₂.P (B.Jidx μ)) μ)
  rw [← (B.inv μ).2]
  exact le_sup_right

/-- The classes of the modules with an index outside all `J_μ` are trivial. -/
theorem a₂_eq_zero_of_not_mem {j : Idx κ} (hj : j ∉ ⋃ ν, (B.fam ν).Jset) : B.a₂ j = C.zero := by
  letI := C.instKMonoid B.hκ
  have hbot : B.D₂.P {j} = ⊥ := by
    have h1 : B.D₂.P {j} ≤ B.D₂.P (⋃ ν, (B.fam ν).Jset)ᶜ :=
      B.D₂.P_mono (Set.singleton_subset_iff.mpr hj)
    have h2 : B.D₂.P (⋃ ν, (B.fam ν).Jset)ᶜ = ⊥ := by
      have hc := B.D₂.P_isCompl (⋃ ν, (B.fam ν).Jset)
      have := hc.disjoint
      rw [B.P₂_iUnion_eq_top] at this
      simpa using this
    exact le_bot_iff.mp (h2 ▸ h1)
  have hone : #({j} : Set (Idx κ)) ≤ κ := by
    rw [Cardinal.mk_singleton]
    exact one_le_aleph0.trans B.hκ
  have hclass := (B.D₂.P_class B.hκ {j} hone).some
  have hsum : sumOf (κ := κ) hone (fun i : ({j} : Set (Idx κ)) => B.a₂ i.1) = B.a₂ j := by
    rw [sumOf_unique hone (fun i : ({j} : Set (Idx κ)) => B.a₂ i.1)]
    rw [Set.mem_singleton_iff.mp (default : ↥({j} : Set (Idx κ))).2]
  rw [hsum] at hclass
  have hsubs : Subsingleton ↥(B.D₂.P ({j} : Set (Idx κ))) := by
    rw [hbot]
    exact ⟨fun x y => Subtype.ext (by
      rw [(Submodule.mem_bot R).mp x.2, (Submodule.mem_bot R).mp y.2])⟩
  exact C.eq_zero_of_subsingleton (Equiv.subsingleton hclass.toEquiv)

/-! ### Filling up the second family -/

/-- The leftover indices of the second family, distributed injectively over the positions. -/
theorem exists_extra : ∃ E : Idx κ × ℕ → Set (Idx κ),
    (∀ μ, #(E μ) ≤ 1) ∧ (∀ μ ρ, μ ≠ ρ → Disjoint (E μ) (E ρ)) ∧
      (⋃ μ, E μ) = (⋃ ν, (B.fam ν).Jset)ᶜ ∧
      ∀ μ, E μ ⊆ (⋃ ν, (B.fam ν).Jset)ᶜ := by
  set W : Set (Idx κ) := ⋃ ν, (B.fam ν).Jset with hWdef
  have hprod : κ ≤ #(Idx κ × ℕ) := by
    have hinj2 : Function.Injective (fun i : Idx κ => (i, (0 : ℕ))) :=
      fun i j h => (Prod.ext_iff.mp h).1
    calc κ = #(Idx κ) := (mk_Idx κ).symm
      _ ≤ #(Idx κ × ℕ) := Cardinal.mk_le_of_injective hinj2
  have hcard : #(↥(Wᶜ)) ≤ #(Idx κ × ℕ) :=
    ((Cardinal.mk_set_le _).trans_eq (mk_Idx κ)).trans hprod
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hcard
  refine ⟨fun μ => {j | ∃ h : j ∈ Wᶜ, e ⟨j, h⟩ = μ}, ?_, ?_, ?_, ?_⟩
  · intro μ
    rw [Cardinal.mk_le_one_iff_set_subsingleton]
    rintro j ⟨hj, hje⟩ j' ⟨hj', hje'⟩
    have : (⟨j, hj⟩ : ↥(Wᶜ)) = ⟨j', hj'⟩ := e.injective (by rw [hje, hje'])
    exact congrArg Subtype.val this
  · intro μ ρ hμρ
    refine Set.disjoint_left.mpr ?_
    rintro j ⟨hj, hje⟩ ⟨hj', hje'⟩
    exact hμρ (by rw [← hje, ← hje'])
  · apply Set.eq_of_subset_of_subset
    · exact Set.iUnion_subset fun μ => fun j hj => hj.1
    · intro j hj
      exact Set.mem_iUnion.mpr ⟨e ⟨j, hj⟩, ⟨hj, rfl⟩⟩
  · exact fun μ j hj => hj.1

/-! ### The braiding -/

/-- **Theorem 4.3**, module-theoretic core: the two families of classes are `λ⁻`-braided. -/
theorem isBraided (x y : Idx κ → ↥B.S) (hx : ∀ i, ((x i : C.carrier)) = B.a₁ i)
    (hy : ∀ j, ((y j : C.carrier)) = B.a₂ j) :
    letI := C.instKMonoid B.hκ
    letI := B.hSsub.lmonoid B.hlam
    IsBraided lam x y := by
  letI := C.instKMonoid B.hκ
  letI := B.hSsub.lmonoid B.hlam
  obtain ⟨E, hE1, hE2, hE3, hE4⟩ := B.exists_extra
  have hlam0 : ℵ₀ ≤ lam := Cardinal.IsRegular.aleph0_le B.hlam
  have hlam1 : (1 : Cardinal) < lam := lt_of_lt_of_le one_lt_aleph0 hlam0
  have hJsmall : ∀ p : Idx κ × ℕ, #((B.fam p).Jset ∪ E p : Set (Idx κ)) < lam := by
    intro p
    refine lt_of_le_of_lt (Cardinal.mk_union_le _ _) ?_
    exact Cardinal.add_lt_of_lt hlam0 (B.fam p).Jsmall (lt_of_le_of_lt (hE1 p) hlam1)
  have hzeroS : ∀ b : ↥B.S, (b : C.carrier) = C.zero → b = 0 := by
    intro b hb
    apply Subtype.ext
    show (b : C.carrier) = (0 : C.carrier)
    rw [hb, C.instKMonoid_zero B.hκ]
  refine ⟨{ I := fun p => (B.fam p).Iset
            J := fun p => (B.fam p).Jset ∪ E p
            I_disjoint := fun p q h => B.Iset_disjoint h
            J_disjoint := ?_
            I_cover := B.Iset_cover
            J_cover := ?_
            I_small := fun p => (B.fam p).Ismall
            J_small := hJsmall
            u := fun p => ⟨(B.fam p).uc, (B.fam p).ucS⟩
            v := fun p => ⟨B.vcm p, B.vcOf_mem B.fam p⟩
            v_limit := ?_
            hI := ?_
            hJ := ?_ }⟩
  · -- the second family is pairwise disjoint
    intro p q hpq
    refine Set.disjoint_left.mpr ?_
    rintro j (hj | hj) (hj' | hj')
    · exact Set.disjoint_left.mp (B.Jset_disjoint hpq) hj hj'
    · exact hE4 q hj' (Set.mem_iUnion.mpr ⟨p, hj⟩)
    · exact hE4 p hj (Set.mem_iUnion.mpr ⟨q, hj'⟩)
    · exact Set.disjoint_left.mp (hE2 p q hpq) hj hj'
  · -- the second family covers `Idx κ`
    apply Set.eq_univ_of_forall
    intro j
    by_cases hj : j ∈ ⋃ ν, (B.fam ν).Jset
    · obtain ⟨ν, hν⟩ := Set.mem_iUnion.mp hj
      exact Set.mem_iUnion.mpr ⟨ν, Or.inl hν⟩
    · obtain ⟨μ, hμ⟩ := Set.mem_iUnion.mp (show j ∈ ⋃ μ, E μ by rw [hE3]; exact hj)
      exact Set.mem_iUnion.mpr ⟨μ, Or.inr hμ⟩
  · -- `v` vanishes at limit positions
    intro a
    exact hzeroS _ (B.vcm_limit (show ((a, 0) : Idx κ × ℕ).2 = 0 from rfl))
  · -- the first braiding equation
    intro p
    apply Subtype.ext
    rw [B.hSsub.coe_lsumOf B.hlam (B.fam p).Ismall (fun i : (B.fam p).Iset => x i.1)]
    have hfun : (fun i : ↥((B.fam p).Iset) => ((x i.1 : C.carrier)))
        = fun i : ↥((B.fam p).Iset) => B.a₁ i.1 := funext fun i => hx i.1
    rw [hfun]
    exact (B.spec p).hI
  · -- the second braiding equation
    intro p
    have hzero : ∀ j ∈ ((B.fam p).Jset ∪ E p), j ∉ (B.fam p).Jset → y j = 0 := by
      intro j hjJ hjn
      have hjE : j ∈ E p := by rcases hjJ with h | h; exacts [absurd h hjn, h]
      refine hzeroS _ ?_
      rw [hy j]
      exact B.a₂_eq_zero_of_not_mem (hE4 p hjE)
    rw [LMonoid.lsumOf_of_subset (hJsmall p) (B.fam p).Jsmall Set.subset_union_left y hzero]
    apply Subtype.ext
    rw [B.hSsub.coe_lsumOf B.hlam (B.fam p).Jsmall (fun j : (B.fam p).Jset => y j.1)]
    have hfun : (fun j : ↥((B.fam p).Jset) => ((y j.1 : C.carrier)))
        = fun j : ↥((B.fam p).Jset) => B.a₂ j.1 := funext fun j => hy j.1
    rw [hfun]
    show sumOf (κ := κ) ((B.fam p).Jsmall.le.trans B.hlk)
        (fun j : (B.fam p).Jset => B.a₂ j.1) = B.vcm (bsucc p) + (B.fam p).uc
    rw [B.vcm_bsucc p]
    exact (B.spec p).hJ

end DoubleDecomp

end ModuleCore

/-! ## Theorem 4.3 -/

variable {R}

/-- **Theorem 4.3**, module-theoretic core: a transfinite iteration of the elementary
observation (M1)–(M2) on direct summands.

Let `Cλ⁻ ⊆ C` be a subclass of `λ⁻`-small modules, closed under isomorphisms, direct
summands, and direct sums over index sets of cardinality `< λ`.  If

  `⨁_{i ∈ κ} A i ≅ ⨁_{j ∈ κ} B j`

with all `A i`, `B j` in `Cλ⁻`, then the families of isomorphism classes `[A i]` and `[B j]`
are `λ⁻`-braided over `V^{λ⁻}(Cλ⁻)`.

Paper proof: fix a limit well-order on `κ` and construct, by transfinite recursion on
`α ∈ κ`, index sets `I α`, `J α` of size `< λ` and submodules `S α`, `T α` of
`M = ⨁_i A i` with `T α = 0` at limit elements and

  `⨁_{μ ≤ α} ⨁_{i ∈ I μ} A i = ⨁_{μ ≤ α} (S μ ⊕ T μ)`,
  `⨁_{μ ≤ α} ⨁_{j ∈ J μ} B j = ⨁_{μ ≤ α} (T (μ+1) ⊕ S μ)`.

The recursion step uses `λ⁻`-smallness of `T α` to find `I α`, then (M2) to split off
`S α`, then `λ⁻`-smallness of `S α` to find `J α`, then (M2) again to split off `T (α+1)`;
`min I'` is always adjoined to `I α` to ensure that the partitions exhaust `κ`.  (M1)
translates the internal decompositions into the required isomorphisms. -/
theorem exists_braided_of_iso (C : ModuleClass R κ) [C.IsSummandClosed] (hκ : ℵ₀ ≤ κ)
    (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ κ)
    (S : Set C.carrier)
    (hsmall : ∀ a ∈ S, IsLambdaSmall R lam (C.rep a))
    (hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S)
    (hSsummand : letI := C.instKMonoid hκ; ∀ a ∈ S, ∀ b : C.carrier,
      (∃ c, b + c = a) → b ∈ S)
    (x y : Idx κ → S)
    (e : (⨁ i, C.rep (x i : C.carrier)) ≃ₗ[R] ⨁ j, C.rep (y j : C.carrier)) :
    letI := C.instKMonoid hκ
    letI := hSsub.lmonoid hlam
    IsBraided lam x y := by
  letI := C.instKMonoid hκ
  letI := hSsub.lmonoid hlam
  -- package the data as a `DoubleDecomp`: `M = ⨁ᵢ A i` carries the two decompositions
  -- `id` and `e`; then run the transfinite construction.
  exact DoubleDecomp.isBraided
    { hκ := hκ, hlam := hlam, hlk := hlk, S := S, hsmall := hsmall, hSsub := hSsub
      hSsummand := hSsummand
      a₁ := fun i => (x i : C.carrier), a₂ := fun j => (y j : C.carrier)
      ha₁ := fun i => (x i).2, ha₂ := fun j => (y j).2
      D₁ := ⟨LinearEquiv.refl R _⟩, D₂ := ⟨e⟩ } x y (fun _ => rfl) (fun _ => rfl)

/-- **Theorem 4.3** (module-theoretic core), in the language of Section 3.  The hypothesis
`Σᵢ [A i] = Σⱼ [B j]` in `V^κ(C)` is the same thing as an isomorphism
`⨁ᵢ A i ≅ ⨁ⱼ B j` (`ModuleClass.iso_of_dsum_eq`), so this is `exists_braided_of_iso`. -/
theorem theorem_4_3_core (C : ModuleClass R κ) [C.IsSummandClosed] (hκ : ℵ₀ ≤ κ)
    (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ κ)
    (S : Set C.carrier)
    -- `S` consists of `λ⁻`-small modules …
    (hsmall : ∀ a ∈ S, IsLambdaSmall R lam (C.rep a))
    -- … and is closed under `0`, direct sums of size `< λ`, and direct summands:
    (hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S)
    (hSsummand : letI := C.instKMonoid hκ; ∀ a ∈ S, ∀ b : C.carrier,
      (∃ c, b + c = a) → b ∈ S)
    (x y : Idx κ → S) :
    letI := C.instKMonoid hκ
    letI := hSsub.lmonoid hlam
    (ksum (κ := κ) fun i => (x i : C.carrier)) = (ksum (κ := κ) fun i => (y i : C.carrier)) →
      IsBraided lam x y := by
  letI := C.instKMonoid hκ
  letI := hSsub.lmonoid hlam
  intro hsum
  -- the hypothesis says exactly that the two direct sums are isomorphic
  have hdsum : C.dsum (fun i => (x i : C.carrier)) = C.dsum (fun i => (y i : C.carrier)) := by
    rw [← C.instKMonoid_ksum hκ, ← C.instKMonoid_ksum hκ]
    exact hsum
  exact exists_braided_of_iso C hκ lam hlam hlk S hsmall hSsub hSsummand x y
    (C.iso_of_dsum_eq _ _ hdsum).some

/-- **Theorem 4.3**, in the language of Section 3: the `κ`-submonoid of `V^κ(C)` generated by
`V^{λ⁻}(Cλ⁻)` is `λ⁻`-braided over `V^{λ⁻}(Cλ⁻)`. -/
theorem theorem_4_3 (C : ModuleClass R κ) [C.IsSummandClosed] (hκ : ℵ₀ ≤ κ)
    (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) (S : Set C.carrier)
    (hsmall : ∀ a ∈ S, IsLambdaSmall R lam (C.rep a))
    (hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S)
    (hSsummand : letI := C.instKMonoid hκ; ∀ a ∈ S, ∀ b : C.carrier, (∃ c, b + c = a) → b ∈ S) :
    letI := C.instKMonoid hκ
    letI := hSsub.lmonoid hlam
    letI := (KMonoid.isKSubmonoid_kclosure κ S).kmonoid
    IsBraidedOver lam κ S (kclosure κ S) hlk
      (fun a => ⟨(a : C.carrier), subset_kclosure a.2⟩) := by
  letI := C.instKMonoid hκ
  letI := hSsub.lmonoid hlam
  letI hKsub : IsKSubmonoid κ (kclosure κ S) := KMonoid.isKSubmonoid_kclosure κ S
  letI := hKsub.kmonoid
  have h0S : (0 : C.carrier) ∈ S := hSsub.zero_mem
  refine ⟨⟨rfl, ?_⟩, ?_, ?_, ?_⟩
  · -- the inclusion is a `λ⁻`-homomorphism: both sides are the ambient `κ`-sum
    intro ι h z
    apply Subtype.ext
    rw [hSsub.coe_lsumOf hlam h z, hKsub.coe_sumOf (h.le.trans hlk)]
    rfl
  · -- injectivity
    intro a b hab
    have hab' := congrArg (fun t : ↥(kclosure κ S) => (t : C.carrier)) hab
    exact Subtype.ext hab'
  · -- `⟨S⟩_κ` is generated by `S`
    intro q
    obtain ⟨x, hxS, hx⟩ := (KMonoid.mem_kclosure_iff h0S (q : C.carrier)).mp q.2
    refine ⟨fun i => ⟨x i, hxS i⟩, Subtype.ext ?_⟩
    rw [hKsub.coe_ksum]
    exact hx
  · -- families with equal sums are braided: this is the module-theoretic core
    intro a b hab
    refine theorem_4_3_core C hκ lam hlam hlk S hsmall hSsub hSsummand a b ?_
    have hcoe := congrArg (fun t : kclosure κ S => (t : C.carrier)) hab
    rwa [hKsub.coe_ksum, hKsub.coe_ksum] at hcoe

/-- **Corollary 4.4(2)** / the "in particular" of Theorem 4.3: if every module in `C` is a
direct sum of modules in `Cλ⁻`, then all of `V^κ(C)` is `λ⁻`-braided over
`V^{λ⁻}(Cλ⁻)`, hence is its universal `κ`-extension. -/
theorem corollary_4_4 (C : ModuleClass R κ) [C.IsSummandClosed] (hκ : ℵ₀ ≤ κ)
    (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) (S : Set C.carrier)
    (hsmall : ∀ a ∈ S, IsLambdaSmall R lam (C.rep a))
    (hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S)
    (hSsummand : letI := C.instKMonoid hκ; ∀ a ∈ S, ∀ b : C.carrier, (∃ c, b + c = a) → b ∈ S)
    (hgen : letI := C.instKMonoid hκ; KGenerates κ S) :
    letI := C.instKMonoid hκ
    letI := hSsub.lmonoid hlam
    IsBraidedOver lam κ S C.carrier hlk (fun a => (a : C.carrier)) ∧
      IsUniversalKExtension lam κ S C.carrier hlk (fun a => (a : C.carrier)) := by
  letI := C.instKMonoid hκ
  letI := hSsub.lmonoid hlam
  have h0S : (0 : C.carrier) ∈ S := hSsub.zero_mem
  have hbr : IsBraidedOver lam κ S C.carrier hlk (fun a => (a : C.carrier)) := by
    refine ⟨⟨rfl, ?_⟩, fun a b hab => Subtype.ext hab, ?_, ?_⟩
    · -- the inclusion is a `λ⁻`-homomorphism
      intro ι h z
      exact hSsub.coe_lsumOf hlam h z
    · -- `V^κ(C)` is generated by `S`
      intro h
      have hmem : h ∈ kclosure κ S := by rw [hgen]; trivial
      obtain ⟨x, hxS, hx⟩ := (KMonoid.mem_kclosure_iff h0S h).mp hmem
      exact ⟨fun i => ⟨x i, hxS i⟩, hx⟩
    · -- families with equal sums are braided
      intro a b hab
      exact theorem_4_3_core C hκ lam hlam hlk S hsmall hSsub hSsummand a b hab
  exact ⟨hbr, hbr.isUniversalKExtension hlk⟩

/-! ## The `λ⁻`-small part of a class of modules -/

section SmallPart

variable {κ : Cardinal.{u}} (C : ModuleClass R κ)

theorem ModuleClass.mem_lambdaSmallPart {a : C.carrier} {lam : Cardinal.{u}}
    (h : IsLambdaSmall R lam (C.rep a)) : a ∈ C.lambdaSmallPart lam := h

theorem ModuleClass.isLambdaSmall_of_mem {a : C.carrier} {lam : Cardinal.{u}}
    (h : a ∈ C.lambdaSmallPart lam) : IsLambdaSmall R lam (C.rep a) := h

theorem ModuleClass.lambdaSmallPart_isLSubset (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) :
    letI := C.instKMonoid hκ
    IsLSubset lam hlk (C.lambdaSmallPart lam) := by
  letI := C.instKMonoid hκ
  constructor
  · -- the zero module is `λ⁻`-small
    haveI := C.subsingleton_rep_of_eq_zero (C.instKMonoid_zero hκ)
    intro ι N iAG iMod f
    exact isLambdaSmall_of_subsingleton (R := R) hlam.pos (C.rep 0) N iAG iMod f
  · -- a direct sum of `< λ` many `λ⁻`-small modules is `λ⁻`-small
    intro ι h x hx
    have hsmall : IsLambdaSmall R lam (⨁ i, C.rep (x i)) :=
      isLambdaSmall_dsum hlam h (fun i => C.rep (x i)) fun i => C.isLambdaSmall_of_mem (hx i)
    intro ι₂ N iAG iMod f
    exact IsLambdaSmall.of_equiv hsmall
      (C.rep_sumOf hκ (h.le.trans hlk) x).some.symm N iAG iMod f

theorem ModuleClass.lambdaSmallPart_summand (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u}) :
    letI := C.instKMonoid hκ
    ∀ a ∈ C.lambdaSmallPart lam, ∀ b : C.carrier, (∃ c, b + c = a) →
      b ∈ C.lambdaSmallPart lam := by
  letI := C.instKMonoid hκ
  intro a ha b ⟨c, hc⟩
  have hprod : IsLambdaSmall R lam (C.rep b × C.rep c) :=
    IsLambdaSmall.of_equiv (C.isLambdaSmall_of_mem ha)
      ((C.iso_of_eq hc).some.symm.trans (C.rep_add hκ b c).some)
  intro ι N iAG iMod f
  exact hprod.of_prod_left N iAG iMod f

theorem ModuleClass.lambdaSmallPart_small (lam : Cardinal.{u}) :
    ∀ a ∈ C.lambdaSmallPart lam, IsLambdaSmall R lam (C.rep a) := by
  intro a ha ι N iAG iMod f
  exact ha N iAG iMod f

theorem ModuleClass.lambdaSmallPart_mono {lam lam' : Cardinal.{u}} (h : lam ≤ lam') :
    C.lambdaSmallPart lam ⊆ C.lambdaSmallPart lam' := by
  intro a ha ι N iAG iMod f
  exact IsLambdaSmall.mono h (C.isLambdaSmall_of_mem ha) N iAG iMod f

end SmallPart

section Gen

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

theorem KMonoid.KGenerates.mono {S S' : Set H} (h : S ⊆ S') (hgen : KGenerates κ S) :
    KGenerates κ S' :=
  Set.eq_univ_of_univ_subset (hgen ▸ KMonoid.kclosure_mono h)

end Gen

/-- **Kaplansky's Theorem** [Kaplansky58] in its classical form, which we take as an axiom:
every projective module is a direct sum of countably generated projective modules. -/
axiom kaplansky_classical {R : Type u} [Ring R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Projective R P] :
    ∃ (ι : Type u) (Q : ι → Type u) (_ : ∀ i, AddCommGroup (Q i)) (_ : ∀ i, Module R (Q i)),
      (∀ i, Module.Projective R (Q i)) ∧
        (∀ i, ∃ s : Set (Q i), #s ≤ ℵ₀ ∧ Submodule.span R s = ⊤) ∧
          Nonempty (P ≃ₗ[R] ⨁ i, Q i)


/-! ## Projective modules: Corollaries 4.5–4.7 -/

section Projective

variable (R) (κ : Cardinal.{u})

/-! ### `V^κ(R)` as the direct summands of the free module `R^{(κ)}` -/

/-- The free module `R^{(κ)}`. -/
abbrev freeMod : Type u := ⨁ _ : Idx κ, R

/-- The `k`-th standard generator of `R^{(κ)}`. -/
noncomputable def freeGen (k : Idx κ) : freeMod R κ := lof R (Idx κ) (fun _ => R) k 1

theorem freeMod_span : Submodule.span R (Set.range (freeGen R κ)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← DirectSum.sum_support_of x]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : (of (fun _ : Idx κ => R) k) (x k) = (x k) • freeGen R κ k := by
    rw [← lof_eq_of R, freeGen, ← LinearMap.map_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  rw [hk]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The direct summands of `R^{(κ)}`; these are exactly the projective modules generated by at
most `κ` elements. -/
def Summand : Type u := {P : Submodule R (freeMod R κ) // ∃ Q, IsCompl P Q}

/-- Two summands are identified when they are isomorphic. -/
instance summandSetoid : Setoid (Summand R κ) where
  r P P' := Nonempty (↥P.1 ≃ₗ[R] ↥P'.1)
  iseqv := ⟨fun _ => ⟨LinearEquiv.refl R _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩

/-- A chosen complement of a summand. -/
noncomputable def Summand.compl (P : Summand R κ) : Submodule R (freeMod R κ) := P.2.choose

theorem Summand.isCompl (P : Summand R κ) : IsCompl P.1 (Summand.compl R κ P) := P.2.choose_spec

/-- `κ` copies of `R^{(κ)}` form `R^{(κ)}`. -/
noncomputable def freeSelfIso (hκ : ℵ₀ ≤ κ) :
    (⨁ _ : Idx κ, freeMod R κ) ≃ₗ[R] freeMod R κ :=
  (DirectSum.sigmaLcurryEquiv (R := R) (ι := Idx κ) (α := fun _ => Idx κ)
      (δ := fun _ _ => R)).symm.trans
    (DirectSum.lequivCongrLeft R
      ((Equiv.sigmaEquivProd (Idx κ) (Idx κ)).trans (pairEquiv hκ)))

/-- The direct sum of a `κ`-indexed family of summands of `R^{(κ)}`, again as a summand. -/
noncomputable def projDsum (hκ : ℵ₀ ≤ κ) (f : Idx κ → Quotient (summandSetoid R κ)) :
    Summand R κ :=
  ⟨Submodule.map (freeSelfIso R κ hκ).toLinearMap
      (dsSub R (fun _ : Idx κ => freeMod R κ) fun i => (f i).out.1),
    ⟨Submodule.map (freeSelfIso R κ hκ).toLinearMap
        (dsSub R (fun _ : Idx κ => freeMod R κ) fun i => Summand.compl R κ (f i).out),
      isCompl_map_equiv _ (dsSub_isCompl R _ fun i => Summand.isCompl R κ (f i).out)⟩⟩

/-- **Definition 2.4(2)**: `V^κ(R)`, the class of projective right `R`-modules generated by at
most `κ` elements, presented as the direct summands of `R^{(κ)}` up to isomorphism. -/
noncomputable def projClass (hκ : ℵ₀ ≤ κ) : ModuleClass R κ where
  carrier := Quotient (summandSetoid R κ)
  rep := fun a => ↥(a.out.1)
  addCommGroup := fun _ => inferInstance
  module := fun _ => inferInstance
  eq_of_iso := fun {a b} e => by
    rw [← Quotient.out_eq a, ← Quotient.out_eq b]
    exact Quotient.sound ⟨e⟩
  zero := ⟦⟨⊥, ⟨⊤, isCompl_bot_top⟩⟩⟧
  subsingleton_rep_zero := by
    haveI : Subsingleton ↥(⊥ : Submodule R (freeMod R κ)) := inferInstance
    exact Equiv.subsingleton
      (Quotient.mk_out (s := summandSetoid R κ) ⟨⊥, ⟨⊤, isCompl_bot_top⟩⟩).some.toEquiv
  dsum := fun f => ⟦projDsum R κ hκ f⟧
  dsum_iso := fun f => by
    have e1 : ↥(((⟦projDsum R κ hκ f⟧ : Quotient (summandSetoid R κ)).out).1) ≃ₗ[R]
        ↥((projDsum R κ hκ f).1) :=
      (Quotient.mk_out (s := summandSetoid R κ) (projDsum R κ hκ f)).some
    have e2 : ↥(dsSub R (fun _ : Idx κ => freeMod R κ) fun i => (f i).out.1) ≃ₗ[R]
        ↥((projDsum R κ hκ f).1) :=
      (freeSelfIso R κ hκ).submoduleMap
        (dsSub R (fun _ : Idx κ => freeMod R κ) fun i => (f i).out.1)
    exact ⟨e1.trans (e2.symm.trans
      (dsSubIso R (fun _ : Idx κ => freeMod R κ) fun i => (f i).out.1))⟩

/-- A direct summand of a summand of `R^{(κ)}` is again a summand of `R^{(κ)}`. -/
theorem exists_class_of_summand_projClass (a : Quotient (summandSetoid R κ))
    (N K : Submodule R ↥(a.out.1)) (hNK : IsCompl N K) :
    ∃ b : Quotient (summandSetoid R κ), Nonempty (↥(b.out.1) ≃ₗ[R] ↥N) := by
  obtain ⟨Qa, hQa⟩ := a.out.2
  have hNle : Submodule.map a.out.1.subtype N ≤ a.out.1 := Submodule.map_subtype_le _ N
  have hKle : Submodule.map a.out.1.subtype K ≤ a.out.1 := Submodule.map_subtype_le _ K
  have hsup : Submodule.map a.out.1.subtype N ⊔ Submodule.map a.out.1.subtype K
      = a.out.1 := by
    rw [← Submodule.map_sup, hNK.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
  have hdisj : Disjoint (Submodule.map a.out.1.subtype N)
      (Submodule.map a.out.1.subtype K ⊔ Qa) := by
    rw [Submodule.disjoint_def]
    intro x hxN hx
    obtain ⟨k, hk, q, hq, hkq⟩ := Submodule.mem_sup.mp hx
    have hqP : q ∈ a.out.1 := by
      have hxP : x ∈ a.out.1 := hNle hxN
      have : q = x - k := by rw [← hkq]; abel
      rw [this]
      exact Submodule.sub_mem _ hxP (hKle hk)
    have hq0 : q = 0 := Submodule.disjoint_def.mp hQa.disjoint q hqP hq
    have hxk : x = k := by rw [← hkq, hq0, add_zero]
    -- now `x` lies in both images, so it comes from `N ⊓ K = ⊥`
    obtain ⟨n, hn, hnx⟩ := hxN
    obtain ⟨k', hk', hk'x⟩ := (hxk ▸ hk : x ∈ Submodule.map a.out.1.subtype K)
    have hnk : n = k' := Subtype.ext (by rw [show (n : freeMod R κ) = x from hnx,
      show (k' : freeMod R κ) = x from hk'x])
    have : n ∈ N ⊓ K := ⟨hn, hnk ▸ hk'⟩
    rw [hNK.inf_eq_bot] at this
    rw [← hnx, (Submodule.mem_bot R).mp this]
    rfl
  have hcompl : IsCompl (Submodule.map a.out.1.subtype N)
      (Submodule.map a.out.1.subtype K ⊔ Qa) := by
    refine ⟨hdisj, ?_⟩
    rw [codisjoint_iff, ← sup_assoc, hsup, ← codisjoint_iff]
    exact hQa.codisjoint
  refine ⟨⟦⟨Submodule.map a.out.1.subtype N, ⟨_, hcompl⟩⟩⟧, ?_⟩
  have e1 : ↥(((⟦(⟨Submodule.map a.out.1.subtype N, ⟨_, hcompl⟩⟩ : Summand R κ)⟧ :
        Quotient (summandSetoid R κ)).out).1) ≃ₗ[R] ↥(Submodule.map a.out.1.subtype N) :=
    (Quotient.mk_out (s := summandSetoid R κ)
      ⟨Submodule.map a.out.1.subtype N, ⟨_, hcompl⟩⟩).some
  have e2 : ↥N ≃ₗ[R] ↥(Submodule.map a.out.1.subtype N) :=
    Submodule.equivMapOfInjective a.out.1.subtype a.out.1.injective_subtype N
  exact ⟨e1.trans e2.symm⟩

/-- **`V^κ(R)` is closed under direct summands.**  This is the property §4 needs and the class
of free modules of §2.3 lacks. -/
instance instIsSummandClosed (hκ : ℵ₀ ≤ κ) : (projClass R κ hκ).IsSummandClosed where
  exists_of_isCompl := exists_class_of_summand_projClass R κ

/-- A projective module generated by at most `κ` elements is a direct summand of `R^{(κ)}`. -/
theorem exists_summand_of_projective (Q : Type u) [AddCommGroup Q] [Module R Q]
    [Module.Projective R Q] (s : Set Q) (hs : #s ≤ κ) (hspan : Submodule.span R s = ⊤) :
    ∃ P : Summand R κ, Nonempty (↥P.1 ≃ₗ[R] Q) := by
  -- a surjection `R^{(κ)} → Q`
  set g : Idx κ → Q := Function.extend (emb hs)
    (fun x : s => (x : Q)) (0 : Idx κ → Q) with hgdef
  have hgs : ∀ x : s, g (emb hs x) = (x : Q) :=
    fun x => (emb hs).injective.extend_apply _ _ x
  set π : freeMod R κ →ₗ[R] Q :=
    DirectSum.toModule R (Idx κ) Q (fun k => LinearMap.toSpanSingleton R Q (g k)) with hπdef
  have hπgen : ∀ k, π (freeGen R κ k) = g k := by
    intro k
    show π (lof R (Idx κ) (fun _ => R) k 1) = g k
    rw [hπdef, DirectSum.toModule_lof (M := fun _ : Idx κ => R) R k (1 : R)]
    show (1 : R) • g k = g k
    rw [one_smul]
  have hπsurj : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    intro x hx
    exact ⟨freeGen R κ (emb hs ⟨x, hx⟩), by
      rw [hπgen, hgs ⟨x, hx⟩]⟩
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπsurj
  have hσπ : ∀ q, π (σ q) = q := fun q => LinearMap.congr_fun hσ q
  have hσinj : Function.Injective σ := by
    intro q q' h
    rw [← hσπ q, ← hσπ q', h]
  refine ⟨⟨LinearMap.range σ, ⟨LinearMap.ker π, ?_⟩⟩,
    ⟨(LinearEquiv.ofInjective σ hσinj).symm⟩⟩
  constructor
  · rw [Submodule.disjoint_def]
    rintro x ⟨q, rfl⟩ hker
    have : q = 0 := by rw [← hσπ q]; exact hker
    rw [this, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.mpr ⟨σ (π x), ⟨π x, rfl⟩, x - σ (π x), ?_, by abel⟩
    show π (x - σ (π x)) = 0
    rw [map_sub, hσπ, sub_self]

/-- Direct summands of `R^{(κ)}` are projective. -/
theorem summand_projective (P : Summand R κ) : Module.Projective R ↥P.1 :=
  Module.Projective.of_split (R := R) (M := freeMod R κ) P.1.subtype
    (Submodule.projectionOnto P.1 (Summand.compl R κ P) (Summand.isCompl R κ P))
    (Submodule.projectionOnto_comp_subtype _)

/-- A summand of `R^{(κ)}` is generated by at most `κ` elements, so if it is written as a
direct sum then at most `κ` of the summands are non-trivial. -/
theorem exists_small_support (hκ : ℵ₀ ≤ κ) (P : Summand R κ) {ι : Type u} (Q : ι → Type u)
    [∀ i, AddCommGroup (Q i)] [∀ i, Module R (Q i)] (e : ↥P.1 ≃ₗ[R] ⨁ i, Q i) :
    ∃ T : Set ι, #T ≤ κ ∧ ∀ i ∉ T, Subsingleton (Q i) := by
  set σ : freeMod R κ →ₗ[R] ⨁ i, Q i :=
    (e : ↥P.1 →ₗ[R] ⨁ i, Q i).comp
      (Submodule.projectionOnto P.1 (Summand.compl R κ P) (Summand.isCompl R κ P)) with hσdef
  have hsurj : Function.Surjective σ :=
    e.surjective.comp (Submodule.projectionOnto_surjective _)
  refine ⟨⋃ k, {i | (σ (freeGen R κ k)) i ≠ 0}, ?_, ?_⟩
  · have hfin : ∀ k, #({i | (σ (freeGen R κ k)) i ≠ 0} : Set ι) ≤ ℵ₀ := by
      intro k
      refine le_of_lt ?_
      rw [Cardinal.lt_aleph0_iff_set_finite]
      refine Set.Finite.subset (σ (freeGen R κ k)).support.finite_toSet fun i hi => ?_
      exact Finset.mem_coe.mpr (DFinsupp.mem_support_iff.mpr hi)
    calc #(⋃ k, {i | (σ (freeGen R κ k)) i ≠ 0} : Set ι)
        ≤ #(Idx κ) * ⨆ k, #({i | (σ (freeGen R κ k)) i ≠ 0} : Set ι) := Cardinal.mk_iUnion_le _
      _ ≤ κ * ℵ₀ := mul_le_mul' (le_of_eq (mk_Idx κ)) (ciSup_le' hfin)
      _ ≤ κ * κ := mul_le_mul' le_rfl hκ
      _ = κ := Cardinal.mul_eq_self hκ
  · -- everything in the direct sum is supported in the union
    intro i hi
    have htop : (⊤ : Submodule R (⨁ i, Q i)) ≤ dsPart R Q (⋃ k, {i | (σ (freeGen R κ k)) i ≠ 0}) := by
      rw [← LinearMap.range_eq_top.mpr hsurj, LinearMap.range_eq_map, ← freeMod_span R κ,
        Submodule.map_span, Submodule.span_le]
      rintro y ⟨x, ⟨k, rfl⟩, rfl⟩ i' hi'
      by_contra hne
      exact hi' (Set.mem_iUnion.mpr ⟨k, hne⟩)
    have hz : ∀ q : Q i, q = 0 := by
      intro q
      have hmem := htop (Submodule.mem_top (x := lof R ι Q i q))
      have := hmem i hi
      rwa [lof_eq_of R, DirectSum.of_eq_same] at this
    exact ⟨fun q q' => by rw [hz q, hz q']⟩


/-! ### Kaplansky's theorem and Corollary 4.5 -/

/-- If every projective module is a direct sum of projective modules generated by fewer than
`λ` elements, then `V^κ(R)` is generated as a `κ`-monoid by its `λ⁻`-small part. -/
theorem kGenerates_of_decomposition (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u}) (hlam : lam.IsRegular)
    (hdec : ∀ (P : Type u) (_ : AddCommGroup P) (_ : Module R P), Module.Projective R P →
      ∃ (ι : Type u) (Q : ι → Type u) (_ : ∀ i, AddCommGroup (Q i)) (_ : ∀ i, Module R (Q i)),
        (∀ i, Module.Projective R (Q i)) ∧
          (∀ i, ∃ s : Set (Q i), #s < lam ∧ #s ≤ κ ∧ Submodule.span R s = ⊤) ∧
            Nonempty (P ≃ₗ[R] ⨁ i, Q i)) :
    letI := (projClass R κ hκ).instKMonoid hκ
    KGenerates κ ((projClass R κ hκ).lambdaSmallPart lam) := by
  letI := (projClass R κ hκ).instKMonoid hκ
  apply Set.eq_univ_of_forall
  intro a
  -- Kaplansky's theorem applied to the projective module `rep a`
  haveI : Module.Projective R ((projClass R κ hκ).rep a) := summand_projective R κ a.out
  obtain ⟨ι, Q, iAG, iMod, hproj, hgen, ⟨e⟩⟩ :=
    hdec ((projClass R κ hκ).rep a) inferInstance inferInstance inferInstance
  -- at most `κ` of the summands are non-trivial
  obtain ⟨T, hT, hTsub⟩ := exists_small_support R κ hκ a.out Q e
  -- each non-trivial summand is a summand of `R^{(κ)}`
  have hQi : ∀ i : T, ∃ P : Summand R κ, Nonempty (↥P.1 ≃ₗ[R] Q i.1) := by
    intro i
    obtain ⟨s, _, hsκ, hsp⟩ := hgen i.1
    haveI := hproj i.1
    exact exists_summand_of_projective R κ (Q i.1) s hsκ hsp
  choose Pfam hPfam using hQi
  -- the corresponding family of classes, padded by zeros
  set c : T → (projClass R κ hκ).carrier := fun i => ⟦Pfam i⟧ with hcdef
  set b : Idx κ → (projClass R κ hκ).carrier :=
    Function.extend (emb hT) c (0 : Idx κ → (projClass R κ hκ).carrier) with hbdef
  have hbc : ∀ i : T, b (emb hT i) = c i :=
    fun i => (emb hT).injective.extend_apply c (0 : Idx κ → (projClass R κ hκ).carrier) i
  have hb0 : ∀ k, k ∉ Set.range (emb hT) → b k = 0 := fun k hk =>
    Function.extend_apply' c (0 : Idx κ → (projClass R κ hκ).carrier) k
      fun ⟨i, hi⟩ => hk ⟨i, hi⟩
  have hrepc : ∀ i : T, Nonempty ((projClass R κ hκ).rep (c i) ≃ₗ[R] Q i.1) := by
    intro i
    exact ⟨(Quotient.mk_out (s := summandSetoid R κ) (Pfam i)).some.trans (hPfam i).some⟩
  have hbsub : ∀ k, k ∉ Set.range (emb hT) →
      Subsingleton ((projClass R κ hκ).rep (b k)) := by
    intro k hk
    refine (projClass R κ hκ).subsingleton_rep_of_eq_zero ?_
    rw [hb0 k hk]
    exact (projClass R κ hκ).instKMonoid_zero hκ
  -- the two decompositions of `rep a` agree, so `a` is the `κ`-sum of the family
  have hdsum : (projClass R κ hκ).dsum b = a := by
    have e1 : (projClass R κ hκ).rep ((projClass R κ hκ).dsum b) ≃ₗ[R]
        ⨁ k, (projClass R κ hκ).rep (b k) := ((projClass R κ hκ).dsum_iso b).some
    have e2 : (⨁ k, (projClass R κ hκ).rep (b k)) ≃ₗ[R]
        ⨁ i : T, (projClass R κ hκ).rep (b (emb hT i)) :=
      ((projClass R κ hκ).restrict_iso b (emb hT) hbsub).some
    have e3 : (⨁ i : T, (projClass R κ hκ).rep (b (emb hT i))) ≃ₗ[R] ⨁ i : T, Q i.1 :=
      DirectSum.congrLinearEquiv fun i : T =>
        ((projClass R κ hκ).iso_of_eq (hbc i)).some.trans (hrepc i).some
    have e4 : (⨁ i : T, Q i.1) ≃ₗ[R] ⨁ i : ι, Q i := (dsum_restrict_iso R Q T hTsub).some.symm
    exact (projClass R κ hκ).eq_of_iso (e1.trans (e2.trans (e3.trans (e4.trans e.symm))))
  have hmemS : ∀ k, b k ∈ (projClass R κ hκ).lambdaSmallPart lam := by
    intro k
    by_cases hk : k ∈ Set.range (emb hT)
    · obtain ⟨i, rfl⟩ := hk
      obtain ⟨s, hs, _, hsp⟩ := hgen i.1
      have hsmall : IsLambdaSmall R lam (Q i.1) :=
        isLambdaSmall_of_span R hlam (Q i.1) s hs hsp
      have hfinal : IsLambdaSmall R lam ((projClass R κ hκ).rep (b (emb hT i))) := by
        rw [hbc i]
        exact IsLambdaSmall.of_equiv hsmall (hrepc i).some.symm
      exact hfinal
    · haveI := hbsub k hk
      exact isLambdaSmall_of_subsingleton hlam.pos ((projClass R κ hκ).rep (b k))
  have hksum : a = ksum (κ := κ) b := by
    rw [(projClass R κ hκ).instKMonoid_ksum hκ b, hdsum]
  rw [hksum]
  exact (KMonoid.isKSubmonoid_kclosure κ _).ksum_mem b fun k => subset_kclosure (hmemS k)

/-- **Kaplansky's Theorem**, `κ`-monoid form: `V^κ(R)` is generated as a `κ`-monoid by the
classes of countably generated projective modules.  Countably generated modules are
`ℵ₁⁻`-small by Example 4.2(2) (note that `ℵ₀⁻`-small would mean finitely generated). -/
theorem kaplansky (hκ : ℵ₀ ≤ κ) :
    letI := (projClass R κ hκ).instKMonoid hκ
    KGenerates κ ((projClass R κ hκ).lambdaSmallPart ℵ₁) := by
  refine kGenerates_of_decomposition R κ hκ ℵ₁ Cardinal.isRegular_aleph_one ?_
  intro P _ _ hP
  obtain ⟨ι, Q, iAG, iMod, hproj, hgen, he⟩ := kaplansky_classical (R := R) P
  refine ⟨ι, Q, iAG, iMod, hproj, fun i => ?_, he⟩
  obtain ⟨s, hs, hsp⟩ := hgen i
  exact ⟨s, lt_of_le_of_lt hs Cardinal.aleph0_lt_aleph_one, hs.trans hκ, hsp⟩


/-- **Corollary 4.5(1)(2)**: for every regular `λ` with `ℵ₁ ≤ λ ≤ κ` the `κ`-monoid `V^κ(R)`
is `λ⁻`-braided over, and hence is the universal `κ`-extension of, the `λ⁻`-monoid
`V^{λ⁻}(R)` of `λ⁻`-small projective modules.  For `λ = ℵ₁` this is `V^{ℵ₀}(R)`, the countably
generated projective modules: `V^{ℵ₀}(R)` determines `V^κ(R)`. -/
theorem corollary_4_5 (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u}) (hlam : lam.IsRegular)
    (h₁ : ℵ₁ ≤ lam) (hlk : lam ≤ κ) :
    letI := (projClass R κ hκ).instKMonoid hκ
    letI := IsLSubset.lmonoid hlam ((projClass R κ hκ).lambdaSmallPart_isLSubset hκ lam hlam hlk)
    IsBraidedOver lam κ ((projClass R κ hκ).lambdaSmallPart lam)
        (projClass R κ hκ).carrier hlk (fun a => (a : (projClass R κ hκ).carrier)) ∧
      IsUniversalKExtension lam κ ((projClass R κ hκ).lambdaSmallPart lam)
        (projClass R κ hκ).carrier hlk (fun a => (a : (projClass R κ hκ).carrier)) := by
  letI := (projClass R κ hκ).instKMonoid hκ
  exact corollary_4_4 (projClass R κ hκ) hκ lam hlam hlk _
    ((projClass R κ hκ).lambdaSmallPart_small lam)
    ((projClass R κ hκ).lambdaSmallPart_isLSubset hκ lam hlam hlk)
    ((projClass R κ hκ).lambdaSmallPart_summand hκ lam)
    (KMonoid.KGenerates.mono ((projClass R κ hκ).lambdaSmallPart_mono h₁) (kaplansky R κ hκ))

/-- **Corollary 4.5(3)**: if every projective `R`-module is a direct sum of finitely generated
modules, then `V^κ(R)` is the universal `κ`-extension of the monoid `V(R)` of finitely
generated projective modules (an `ℵ₀⁻`-monoid is an ordinary commutative monoid). -/
theorem corollary_4_5_three (hκ : ℵ₀ ≤ κ)
    (hfg : ∀ (P : Type u) (_ : AddCommGroup P) (_ : Module R P), Module.Projective R P →
      ∃ (ι : Type u) (Q : ι → Type u) (_ : ∀ i, AddCommGroup (Q i)) (_ : ∀ i, Module R (Q i)),
        (∀ i, Module.Projective R (Q i)) ∧ (∀ i, Module.Finite R (Q i)) ∧
          Nonempty (P ≃ₗ[R] ⨁ i, Q i)) :
    letI := (projClass R κ hκ).instKMonoid hκ
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
      ((projClass R κ hκ).lambdaSmallPart_isLSubset hκ ℵ₀ Cardinal.isRegular_aleph0 hκ)
    IsBraidedOver ℵ₀ κ ((projClass R κ hκ).lambdaSmallPart ℵ₀)
        (projClass R κ hκ).carrier hκ (fun a => (a : (projClass R κ hκ).carrier)) ∧
      IsUniversalKExtension ℵ₀ κ ((projClass R κ hκ).lambdaSmallPart ℵ₀)
        (projClass R κ hκ).carrier hκ (fun a => (a : (projClass R κ hκ).carrier)) := by
  refine corollary_4_4 (projClass R κ hκ) hκ ℵ₀ Cardinal.isRegular_aleph0 hκ _
    ((projClass R κ hκ).lambdaSmallPart_small ℵ₀)
    ((projClass R κ hκ).lambdaSmallPart_isLSubset hκ ℵ₀ Cardinal.isRegular_aleph0 hκ)
    ((projClass R κ hκ).lambdaSmallPart_summand hκ ℵ₀) ?_
  refine kGenerates_of_decomposition R κ hκ ℵ₀ Cardinal.isRegular_aleph0 ?_
  intro P _ _ hP
  obtain ⟨ι, Q, iAG, iMod, hproj, hfin, he⟩ := hfg P inferInstance inferInstance hP
  refine ⟨ι, Q, iAG, iMod, hproj, fun i => ?_, he⟩
  obtain ⟨s, hs⟩ := (hfin i).fg_top
  have hlt : #(↑s : Set (Q i)) < ℵ₀ := by
    rw [Cardinal.lt_aleph0_iff_set_finite]
    exact s.finite_toSet
  exact ⟨↑s, hlt, hlt.le.trans hκ, hs⟩


/-- **Corollary 4.6**: classes of rings over which the hypothesis of Corollary 4.5(3) holds
(weakly semihereditary, one-sided semihereditary, exchange, semiperfect, weakly noetherian
commutative, Bézout with Krull dimension).  These are quoted results from the literature and
are not formalised here. -/
theorem corollary_4_6 : True := trivial

/-- **Corollary 4.7(1)**: for a `κ`-monoid `H` the following are equivalent: (a) `H` is
braided over `add x` for some `x ∈ H`; (b) for every field `k` there is a hereditary
`k`-algebra `R` with `V^κ(R) ≅ H`; (c) there is a right hereditary ring `R` with
`V^κ(R) ≅ H`.  The implication (a) ⇒ (b) rests on the Bergman–Dicks realisation theorem,
which is not formalised here. -/
theorem corollary_4_7 : True := trivial

end Projective

end KappaMonoid
