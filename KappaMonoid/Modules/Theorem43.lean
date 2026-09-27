/-
**Theorem 4.3**: if every module of `C` is a direct sum of `λ⁻`-small ones, then `V^κ(C)` is
`λ⁻`-braided over `V^{λ⁻}(C_{λ⁻})`.  The transfinite recursion of the paper's proof, and
**Corollary 4.4**.
-/
import KappaMonoid.Modules.Class

universe u v w t

open Cardinal Function Set DirectSum
open scoped Classical

namespace KappaMonoid

open KMonoid LMonoid

variable (R : Type u) [Ring R]


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
  let := C.instKMonoid hκ
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
  let := C.instKMonoid hκ
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
  let := C.instKMonoid hκ
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
  let := C.instKMonoid hκ
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

/-- There are at least `κ` positions `Idx κ × ℕ`. -/
theorem le_mk_Idx_prod_nat : κ ≤ #(Idx κ × ℕ) :=
  (mk_Idx κ).symm.le.trans (Cardinal.mk_le_of_injective (f := fun i : Idx κ => (i, 0))
    fun _ _ h => (Prod.ext_iff.mp h).1)

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
  hlk : lam ≤ Order.succ κ
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
  let := C.instKMonoid B.hκ
  have h := B.hSsub.zero_mem
  rwa [C.instKMonoid_zero B.hκ] at h

theorem isRep_zero : IsRep C C.zero (⊥ : Submodule R M) :=
  haveI := C.subsingleton_rep_zero
  ⟨LinearEquiv.ofSubsingleton (R := R) (C.rep C.zero) ↥(⊥ : Submodule R M)⟩

theorem empty_small (hlam : lam.IsRegular) : #(∅ : Set (Idx κ)) < lam := by
  have h0 : #(∅ : Set (Idx κ)) = 0 := Cardinal.mk_eq_zero _
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
    sumOf (κ := κ) (le_of_lt_of_le_succ B.hlk st.Ismall) (fun i : st.Iset => B.a₁ i.1) = vc + st.uc
  hJ : letI := C.instKMonoid B.hκ
    sumOf (κ := κ) (le_of_lt_of_le_succ B.hlk st.Jsmall) (fun j : st.Jset => B.a₂ j.1) = st.tc + st.uc

/-! From here on the class must be closed under direct summands: the recursion splits off
complements at every step.  See `ModuleClass.IsSummandClosed`. -/

variable [C.IsSummandClosed]

/-- **Half a step of Theorem 4.3.**  Let `E` be one of the two decompositions, `U` the indices of
`E` used so far, and `X` a module with class `x ∈ S` such that `X ⊕ E_U = Q` for a direct summand
`Q` of `M`.  Then a set `I` of `< λ` fresh indices, containing a prescribed small set `I₀` of fresh
indices, has `X ≤ E_{U ∪ I}`; the complement `Y = Qᶜ ⊓ E_{U ∪ I}` of `Q` in `E_{U ∪ I}` has a class
`y ∈ S`; and `x + y = Σ_{i ∈ I} a i`.

This is the paper's "there exists `I_α ⊆ I'` with `|I_α| < λ` such that `T_α ⊕ ⨁_{μ<α} ⨁_{I_μ} A_i
⊆ ⨁_{μ≤α} ⨁_{I_μ} A_i` … so we can choose `S_α`", with `E` the first decomposition and `Q` a partial
sum of the second; with the roles exchanged it is the step producing `J_α` and `T_{α+1}`.

Paper proof: `X` is `λ⁻`-small, so it lies in a sub-sum over `< λ` fresh indices
(`exists_small_cover`).  `Q` is a direct summand of `M` contained in `E_{U ∪ I}`, so it is one of
`E_{U ∪ I}` (M2).  Both `X ⊕ Y` and `E_I` are complements of `E_U` in `E_{U ∪ I}`, so they are
isomorphic (M1); hence `Y` is a summand of a module in the class, with `x + y = Σ_{i ∈ I} a i`,
and `y ∈ S` because `S` is closed under summands. -/
theorem exists_halfStep {a : Idx κ → C.carrier} (ha : ∀ i, a i ∈ B.S) (E : Decomp C M a)
    (U I₀ : Set (Idx κ)) (hI₀ : I₀ ⊆ Uᶜ) (hI₀small : #I₀ < lam)
    {Q Qc X : Submodule R M} (hQ : IsCompl Q Qc) {x : C.carrier} (hxS : x ∈ B.S)
    (hx : IsRep C x X) (hdisj : Disjoint X (E.P U)) (heq : X ⊔ E.P U = Q) :
    letI := C.instKMonoid B.hκ
    ∃ (I : Set (Idx κ)) (hI : #I < lam) (y : C.carrier),
      I₀ ⊆ I ∧ I ⊆ Uᶜ ∧ X ≤ E.P (U ∪ I) ∧ y ∈ B.S ∧ IsRep C y (Qc ⊓ E.P (U ∪ I)) ∧
      Disjoint Q (Qc ⊓ E.P (U ∪ I)) ∧ Q ⊔ (Qc ⊓ E.P (U ∪ I)) = E.P (U ∪ I) ∧
      x + y = sumOf (κ := κ) (le_of_lt_of_le_succ B.hlk hI) fun i : I => a i.1 := by
  let := C.instKMonoid B.hκ
  -- `X` is `λ⁻`-small, so it lies in a sub-sum over `< λ` fresh indices; add `I₀`
  obtain ⟨t, ht, htU, hXt⟩ :=
    E.exists_small_cover (IsLambdaSmall.of_equiv (B.hsmall x hxS) hx.some) U
  have hI : #(t ∪ I₀ : Set (Idx κ)) < lam := (Cardinal.mk_union_le _ _).trans_lt
    (Cardinal.add_lt_of_lt B.hlam.aleph0_le ht hI₀small)
  have hIU : t ∪ I₀ ⊆ Uᶜ := Set.union_subset (fun i hi hU => Set.disjoint_left.mp htU hi hU) hI₀
  have hXle : X ≤ E.P (U ∪ (t ∪ I₀)) :=
    hXt.trans (E.P_mono (Set.union_subset_union_right _ Set.subset_union_left))
  -- (M2): `Q` is a summand of `M` inside `E_{U ∪ I}`, so it has the complement `Y` there
  have hQle : Q ≤ E.P (U ∪ (t ∪ I₀)) := heq ▸ sup_le hXle (E.P_mono Set.subset_union_left)
  obtain ⟨hdQY, hsQY⟩ := relCompl_of_isCompl hQ hQle
  -- (M1): `X ⊕ Y` and `E_I` are both complements of `E_U` in `E_{U ∪ I}`
  have hXY : Disjoint X (Qc ⊓ E.P (U ∪ (t ∪ I₀))) := hdQY.mono_left (heq ▸ le_sup_left)
  have hU_XY : Disjoint (E.P U) (X ⊔ (Qc ⊓ E.P (U ∪ (t ∪ I₀)))) :=
    hdisj.symm.disjoint_sup_right_of_disjoint_sup_left (by rw [sup_comm, heq]; exact hdQY)
  have hsU_XY : E.P U ⊔ (X ⊔ (Qc ⊓ E.P (U ∪ (t ∪ I₀)))) = E.P (U ∪ (t ∪ I₀)) := by
    rw [← sup_assoc, sup_comm (E.P U) X, heq, hsQY]
  obtain ⟨e⟩ := iso_of_relCompl hU_XY hsU_XY
    (E.P_disjoint (Set.disjoint_left.mpr fun i hi hi' => hIU hi' hi)) (E.P_union _ _).symm
  -- so `Y` is represented by a class `y` with `x + y = Σ_{i ∈ I} a i`, and `y ∈ S`
  have hA : Nonempty (C.rep (sumOf (κ := κ) (le_of_lt_of_le_succ B.hlk hI)
      fun i : (t ∪ I₀ : Set (Idx κ)) => a i.1) ≃ₗ[R] ↥(X ⊔ (Qc ⊓ E.P (U ∪ (t ∪ I₀))))) :=
    ⟨(E.P_class B.hκ _ _).some.trans e.symm⟩
  obtain ⟨y, hy⟩ := C.exists_class_of_relCompl _ hXY.symm (sup_comm _ _) hA.some
  have hsum := C.add_eq_of_relCompl B.hκ hXY rfl hx hy hA
  have hyS : y ∈ B.S := B.hSsummand _ (B.hSsub.sumOf_mem hI _ fun i => ha i.1) y
    ⟨x, by rw [add_comm]; exact hsum⟩
  exact ⟨t ∪ I₀, hI, y, Set.subset_union_right, hIU, hXle, hyS, hy, hdQY, hsQY, hsum⟩

/-- **The recursion step of Theorem 4.3.**  Given that `Told ⊕ ⨁_{i ∈ Uidx} A i` is the
internal sum `⨁_{j ∈ Jidx} B j`, we find fresh blocks `I_α`, `J_α` of size `< λ` and modules
`S_α`, `T_{α+1}` continuing the two decompositions: two half steps (`exists_halfStep`), one in
each decomposition.  `I_α` contains the least unused index of the first decomposition, if there
is one, which makes the blocks exhaust `Idx κ`; when there is none, `Told = 0` and the step is
empty. -/
theorem exists_step (Uidx Jidx : Set (Idx κ)) (Told : Submodule R M) (vc : C.carrier)
    (hvcS : vc ∈ B.S) (hvrep : IsRep C vc Told)
    (hdisj : Disjoint Told (B.D₁.P Uidx))
    (heq : Told ⊔ B.D₁.P Uidx = B.D₂.P Jidx) :
    ∃ st : B.Step, B.StepProps Uidx Jidx Told vc st := by
  let := C.instKMonoid B.hκ
  -- the least unused index of the first decomposition, if any
  let I₀ : Set (Idx κ) := Set.range fun h : (Uidxᶜ).Nonempty => wfMin Uidxᶜ h
  have hI₀ : I₀ ⊆ Uidxᶜ := Set.range_subset_iff.mpr fun h => wfMin_mem _ h
  have hI₀small : #I₀ < lam := (Set.finite_range _).lt_aleph0.trans_le B.hlam.aleph0_le
  -- absorb `T_α` into the first decomposition, splitting off `S_α`
  obtain ⟨I, hI, uc, hI₀I, hIU, hTold, hucS, hucrep, hd₁, hs₁, hIsum⟩ :=
    B.exists_halfStep B.ha₁ B.D₁ Uidx I₀ hI₀ hI₀small (B.D₂.P_isCompl Jidx) hvcS hvrep hdisj heq
  -- absorb `S_α` into the second decomposition, splitting off `T_{α+1}`
  obtain ⟨J, hJ, tc, -, hJU, -, htcS, htcrep, hd₂, hs₂, hJsum⟩ :=
    B.exists_halfStep B.ha₂ B.D₂ Jidx ∅ (Set.empty_subset _) (empty_small B.hlam)
      (B.D₁.P_isCompl (Uidx ∪ I)) hucS hucrep hd₁.symm (by rw [sup_comm]; exact hs₁)
  exact ⟨{ Iset := I, Jset := J, Ssub := _, Tsub := _, uc := uc, tc := tc, Ismall := hI
           Jsmall := hJ, ucS := hucS, tcS := htcS, urep := hucrep, trep := htcrep },
    { Isub := hIU
      Jsub := hJU
      minMem := fun h => hI₀I ⟨h, rfl⟩
      ToldLe := hTold
      Tdisj := hd₂.symm
      Teq := by rw [sup_comm]; exact hs₂
      hI := hIsum.symm
      hJ := (add_comm tc uc).trans hJsum |>.symm }⟩

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
  usedBefore (fun ν => (F ν).Iset) μ

open IsBraided in
/-- The indices of the second decomposition used strictly before `μ`. -/
def JidxOf (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : Set (Idx κ) :=
  usedBefore (fun ν => (F ν).Jset) μ

/-- The paper's `T_μ`: the module carried over from the preceding stage; `0` at limits. -/
def TmOf (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : Submodule R M :=
  if μ.2 = 0 then ⊥ else (F (μ.1, μ.2 - 1)).Tsub

/-- The class of `T_μ`. -/
def vcOf (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : C.carrier :=
  if μ.2 = 0 then C.zero else (F (μ.1, μ.2 - 1)).tc

omit [C.IsSummandClosed] in
theorem vcOf_mem (F : Idx κ × ℕ → B.Step) (μ : Idx κ × ℕ) : B.vcOf F μ ∈ B.S := by
  unfold vcOf
  by_cases h : μ.2 = 0
  · rw [if_pos h]; exact B.zero_mem_S
  · rw [if_neg h]; exact (F (μ.1, μ.2 - 1)).tcS

omit [C.IsSummandClosed] in
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
  have hU : B.UidxOf F μ = B.UidxOf G μ := usedBefore_congr fun ν hν => by rw [h ν hν]
  have hJ : B.JidxOf F μ = B.JidxOf G μ := usedBefore_congr fun ν hν => by rw [h ν hν]
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
    i ∈ B.Uidx μ ↔ ∃ ν, kOrd (Idx κ) ν μ ∧ i ∈ (B.fam ν).Iset := mem_usedBefore

open IsBraided in
theorem mem_Jidx {μ : Idx κ × ℕ} {j : Idx κ} :
    j ∈ B.Jidx μ ↔ ∃ ν, kOrd (Idx κ) ν μ ∧ j ∈ (B.fam ν).Jset := mem_usedBefore

open IsBraided in
theorem Uidx_bsucc (μ : Idx κ × ℕ) : B.Uidx (bsucc μ) = B.Uidx μ ∪ (B.fam μ).Iset :=
  usedBefore_bsucc _ μ

open IsBraided in
theorem Jidx_bsucc (μ : Idx κ × ℕ) : B.Jidx (bsucc μ) = B.Jidx μ ∪ (B.fam μ).Jset :=
  usedBefore_bsucc _ μ

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
theorem Uidx_mono {ρ μ : Idx κ × ℕ} (h : kOrd (Idx κ) ρ μ) : B.Uidx ρ ⊆ B.Uidx μ :=
  usedBefore_mono h

open IsBraided in
theorem Jidx_mono {ρ μ : Idx κ × ℕ} (h : kOrd (Idx κ) ρ μ) : B.Jidx ρ ⊆ B.Jidx μ :=
  usedBefore_mono h

/-! ### The invariant -/

open IsBraided in
/-- At a limit position the blocks used so far are the union of those used before any earlier
position. -/
theorem Uidx_limit_eq {μ : Idx κ × ℕ} (h : μ.2 = 0) :
    B.Uidx μ = ⋃ ρ : {ρ : Idx κ × ℕ // kOrd (Idx κ) ρ μ}, B.Uidx ρ.1 :=
  usedBefore_limit _ h

open IsBraided in
theorem Jidx_limit_eq {μ : Idx κ × ℕ} (h : μ.2 = 0) :
    B.Jidx μ = ⋃ ρ : {ρ : Idx κ × ℕ // kOrd (Idx κ) ρ μ}, B.Jidx ρ.1 :=
  usedBefore_limit _ h

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
        · refine le_trans ?_ (le_iSup
            (fun j : {ρ : Idx κ × ℕ // kOrd (Idx κ) ρ μ} => B.D₁.P (B.Uidx j.1))
            (⟨bsucc ρ.1, kOrd_bsucc_of_limit hμ ρ.2⟩ : {ρ : Idx κ × ℕ // kOrd (Idx κ) ρ μ}))
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
    (B.fam ν).Iset ⊆ B.Uidx μ := subset_usedBefore (A := fun ν => (B.fam ν).Iset) h

open IsBraided in
theorem Jset_subset_Jidx {ν μ : Idx κ × ℕ} (h : kOrd (Idx κ) ν μ) :
    (B.fam ν).Jset ⊆ B.Jidx μ := subset_usedBefore (A := fun ν => (B.fam ν).Jset) h

open IsBraided in
theorem Iset_disjoint {μ ρ : Idx κ × ℕ} (h : μ ≠ ρ) :
    Disjoint (B.fam μ).Iset (B.fam ρ).Iset :=
  pairwise_disjoint_of_disjoint_usedBefore
    (fun ν => Set.subset_compl_iff_disjoint_right.mp (B.spec ν).Isub) h

open IsBraided in
theorem Jset_disjoint {μ ρ : Idx κ × ℕ} (h : μ ≠ ρ) :
    Disjoint (B.fam μ).Jset (B.fam ρ).Jset :=
  pairwise_disjoint_of_disjoint_usedBefore
    (fun ν => Set.subset_compl_iff_disjoint_right.mp (B.spec ν).Jsub) h

open IsBraided in
theorem Uidx_subset_iUnion (μ : Idx κ × ℕ) : B.Uidx μ ⊆ ⋃ ν, (B.fam ν).Iset :=
  usedBefore_subset_iUnion _ μ

open IsBraided in
theorem Uidx_iUnion : (⋃ μ, B.Uidx μ) = ⋃ ν, (B.fam ν).Iset := iUnion_usedBefore _

open IsBraided in
theorem Jidx_iUnion : (⋃ μ, B.Jidx μ) = ⋃ ν, (B.fam ν).Jset := iUnion_usedBefore _

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
  exact absurd ((le_mk_Idx_prod_nat.trans h1).trans_lt (mk_Iic_Idx_lt B.hκ i₀)) (lt_irrefl κ)

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
  let := C.instKMonoid B.hκ
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
  have hcard : #(↥(Wᶜ)) ≤ #(Idx κ × ℕ) :=
    ((Cardinal.mk_set_le _).trans_eq (mk_Idx κ)).trans le_mk_Idx_prod_nat
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
  let := C.instKMonoid B.hκ
  let := B.hSsub.lmonoid B.hlam
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
            I_small := fun p => ⟨(B.fam p).Ismall⟩
            J_small := fun p => ⟨hJsmall p⟩
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
    show sumOf (κ := κ) (le_of_lt_of_le_succ B.hlk (B.fam p).Jsmall)
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
    (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ)
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
  let := C.instKMonoid hκ
  let := hSsub.lmonoid hlam
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
    (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ)
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
  let := C.instKMonoid hκ
  let := hSsub.lmonoid hlam
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
    (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ) (S : Set C.carrier)
    (hsmall : ∀ a ∈ S, IsLambdaSmall R lam (C.rep a))
    (hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S)
    (hSsummand : letI := C.instKMonoid hκ; ∀ a ∈ S, ∀ b : C.carrier, (∃ c, b + c = a) → b ∈ S) :
    letI := C.instKMonoid hκ
    letI := hSsub.lmonoid hlam
    letI := (KMonoid.isKSubmonoid_kclosure κ S).kmonoid
    IsBraidedOver lam κ S (kclosure κ S) hlk
      (fun a => ⟨(a : C.carrier), subset_kclosure a.2⟩) := by
  let := C.instKMonoid hκ
  let := hSsub.lmonoid hlam
  let hKsub : IsKSubmonoid κ (kclosure κ S) := KMonoid.isKSubmonoid_kclosure κ S
  let := hKsub.kmonoid
  have h0S : (0 : C.carrier) ∈ S := hSsub.zero_mem
  refine ⟨⟨rfl, ?_⟩, ?_, ?_, ?_⟩
  · -- the inclusion is a `λ⁻`-homomorphism: both sides are the ambient `κ`-sum
    intro ι h z
    apply Subtype.ext
    rw [hSsub.coe_lsumOf hlam h z, hKsub.coe_sumOf (le_of_lt_of_le_succ hlk h)]
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

/-- The "in particular" of **Theorem 4.3**, for an arbitrary `λ⁻`-closed, summand-closed subset
`S` of `V^κ(C)`: if every module in `C` is a direct sum of modules in `Cλ⁻`, then all of `V^κ(C)`
is `λ⁻`-braided over `V^{λ⁻}(Cλ⁻)`, hence is its universal `κ`-extension.  Corollary 4.4(1) and
(2) are the case of the modules generated by fewer than `λ` elements. -/
theorem corollary_4_4 (C : ModuleClass R κ) [C.IsSummandClosed] (hκ : ℵ₀ ≤ κ)
    (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ) (S : Set C.carrier)
    (hsmall : ∀ a ∈ S, IsLambdaSmall R lam (C.rep a))
    (hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S)
    (hSsummand : letI := C.instKMonoid hκ; ∀ a ∈ S, ∀ b : C.carrier, (∃ c, b + c = a) → b ∈ S)
    (hgen : letI := C.instKMonoid hκ; KGenerates κ S) :
    letI := C.instKMonoid hκ
    letI := hSsub.lmonoid hlam
    IsBraidedOver lam κ S C.carrier hlk (fun a => (a : C.carrier)) ∧
      IsUniversalKExtension.{u, u, u, t} lam κ S C.carrier hlk (fun a => (a : C.carrier)) := by
  let := C.instKMonoid hκ
  let := hSsub.lmonoid hlam
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

end KappaMonoid
