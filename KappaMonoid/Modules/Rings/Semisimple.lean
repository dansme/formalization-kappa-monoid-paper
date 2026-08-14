/-
Proposition 2.17 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*:

semisimple rings realise exactly the finitely generated free `κ`-monoids `F_κ^n`.

Every module over a semisimple ring is a direct sum of simple modules
(`IsSemisimpleModule.exists_linearEquiv_dfinsupp`, from Mathlib), and the multiplicity of each
isomorphism class of simple modules is uniquely determined (axiom A3).  So a module is described
by its multiplicity function, and `V^κ(R)` is the `κ`-monoid of such functions with values
`≤ κ`, which is `F_κ^n` when there are `n` classes.
-/
import KappaMonoid.Modules
import KappaMonoid.Core.Cardinal
import KappaMonoid.Axioms.Modules

universe u

open Cardinal Function Set DirectSum

namespace KappaMonoid

/-! ## A complete irredundant list of the simple modules

The paper's "`n` isomorphism classes of simple modules" is taken as data: a family `S : Fin n →
Type u` of pairwise non-isomorphic simple modules such that every simple module is isomorphic to
one of them. -/

/-- A complete irredundant list of the simple `R`-modules. -/
structure SimpleList (R : Type u) [Ring R] (n : ℕ) where
  /-- The chosen representatives. -/
  S : Fin n → Type u
  [addCommGroup : ∀ i, AddCommGroup (S i)]
  [module : ∀ i, Module R (S i)]
  /-- Each representative is simple. -/
  simple : ∀ i, IsSimpleModule R (S i)
  /-- The representatives are pairwise non-isomorphic. -/
  distinct : ∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j
  /-- Every simple module is one of them. -/
  complete : ∀ (T : Type u) [AddCommGroup T] [Module R T], IsSimpleModule R T →
    ∃ i, Nonempty (T ≃ₗ[R] S i)

attribute [instance] SimpleList.addCommGroup SimpleList.module

namespace SimpleList

variable {R : Type u} [Ring R] {n : ℕ} (L : SimpleList R n)

/-- The index of the isomorphism class of a simple module. -/
noncomputable def classOf {T : Type u} [AddCommGroup T] [Module R T] (h : IsSimpleModule R T) :
    Fin n := (L.complete T h).choose

theorem classOf_spec {T : Type u} [AddCommGroup T] [Module R T] (h : IsSimpleModule R T) :
    Nonempty (T ≃ₗ[R] L.S (L.classOf h)) := (L.complete T h).choose_spec

/-- The class of a simple module is determined by its isomorphism type. -/
theorem classOf_eq_of_equiv {T T' : Type u} [AddCommGroup T] [Module R T] [AddCommGroup T']
    [Module R T'] (h : IsSimpleModule R T) (h' : IsSimpleModule R T')
    (e : T ≃ₗ[R] T') : L.classOf h = L.classOf h' :=
  L.distinct _ _ ⟨((L.classOf_spec h).some.symm.trans e).trans (L.classOf_spec h').some⟩

/-- The class of `S i` is `i`. -/
@[simp] theorem classOf_S (i : Fin n) : L.classOf (L.simple i) = i :=
  L.distinct _ _ ⟨(L.classOf_spec (L.simple i)).some.symm⟩

end SimpleList

/-! ## Multiplicities

For a family of simple modules, the multiplicity of the class `i` is the number of members of
the family lying in that class. -/

section Mult

variable {R : Type u} [Ring R] {n : ℕ} (L : SimpleList R n)

/-- The multiplicity of the class `i` in a family of simple modules. -/
noncomputable def multOf {J : Type u} (A : J → Type u) [∀ j, AddCommGroup (A j)]
    [∀ j, Module R (A j)] (i : Fin n) : Cardinal.{u} :=
  #{j : J // Nonempty (A j ≃ₗ[R] L.S i)}

/-- **Axiom A3, in the form used here**: isomorphic direct sums of simple modules have the same
multiplicities. -/
theorem multOf_eq {J J' : Type u} {A : J → Type u} {B : J' → Type u}
    [∀ j, AddCommGroup (A j)] [∀ j, Module R (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)]
    (hA : ∀ j, IsSimpleModule R (A j)) (hB : ∀ j, IsSimpleModule R (B j))
    (e : (⨁ j, A j) ≃ₗ[R] (⨁ j, B j)) (i : Fin n) :
    multOf L A i = multOf L B i :=
  mk_multiplicity_eq hA hB e (L.S i)

end Mult

/-! ## The multiplicity function of a semisimple module

Mathlib decomposes every semisimple module into simple submodules; a choice of such a
decomposition gives a multiplicity function, and axiom A3 makes it independent of the choice —
indeed an isomorphism invariant. -/

section Decomp

variable (R : Type u) [Ring R] (M : Type u) [AddCommGroup M] [Module R M]
  [IsSemisimpleModule R M]

/-- A chosen decomposition of a semisimple module into simple submodules. -/
noncomputable def decompSet : Set (Submodule R M) :=
  (IsSemisimpleModule.exists_linearEquiv_dfinsupp R M).choose

/-- `M` is the direct sum of its chosen decomposition. -/
noncomputable def decompEquiv : M ≃ₗ[R] (⨁ m : decompSet R M, (m : Submodule R M)) :=
  (IsSemisimpleModule.exists_linearEquiv_dfinsupp R M).choose_spec.choose

theorem decomp_simple (m : decompSet R M) : IsSimpleModule R (m : Submodule R M) :=
  (IsSemisimpleModule.exists_linearEquiv_dfinsupp R M).choose_spec.choose_spec.2 m

variable {R M}

/-- **The multiplicity function of a semisimple module**: how many copies of `S i` occur in it. -/
noncomputable def mult {n : ℕ} (L : SimpleList R n) (i : Fin n) : Cardinal.{u} :=
  multOf L (fun m : decompSet R M => (m : Submodule R M)) i

variable {M' : Type u} [AddCommGroup M'] [Module R M'] [IsSemisimpleModule R M']

/-- **Multiplicities are isomorphism invariants**, by axiom A3. -/
theorem mult_congr {n : ℕ} (L : SimpleList R n) (e : M ≃ₗ[R] M') (i : Fin n) :
    mult (M := M) L i = mult (M := M') L i :=
  multOf_eq L (decomp_simple R M) (decomp_simple R M')
    (((decompEquiv R M).symm.trans e).trans (decompEquiv R M')) i

/-- The multiplicity of `S i` in `S j` is `1` if `i = j` and `0` otherwise: a simple module is
its own decomposition. -/
theorem mult_of_simple {n : ℕ} (L : SimpleList R n) (hM : IsSimpleModule R M) (i : Fin n) :
    mult (M := M) L i = if L.classOf hM = i then 1 else 0 := by
  classical
  -- `M` decomposes as the one-element family `M` itself
  have hone : Nonempty ((⨁ _ : PUnit.{u + 1}, M) ≃ₗ[R] (⨁ m : decompSet R M,
      (m : Submodule R M))) := by
    refine ⟨((directSumEquivOfSubsingleton R (fun _ : PUnit.{u + 1} => M) PUnit.unit
      fun i hi => absurd (Subsingleton.elim i _) hi).trans (decompEquiv R M))⟩
  have hmul := multOf_eq L (fun _ : PUnit.{u + 1} => hM) (decomp_simple R M) hone.some i
  rw [mult, ← hmul, multOf]
  by_cases hc : L.classOf hM = i
  · have hP : Nonempty (M ≃ₗ[R] L.S i) := hc ▸ L.classOf_spec hM
    rw [if_pos hc]
    haveI : Unique {j : PUnit.{u + 1} // Nonempty (M ≃ₗ[R] L.S i)} :=
      ⟨⟨⟨PUnit.unit, hP⟩⟩, fun a => Subtype.ext (Subsingleton.elim _ _)⟩
    exact Cardinal.mk_eq_one _
  · rw [if_neg hc]
    haveI : IsEmpty {j : PUnit.{u + 1} // Nonempty (M ≃ₗ[R] L.S i)} :=
      ⟨fun a => hc (L.distinct _ _ ⟨(L.classOf_spec hM).some.symm.trans a.2.some⟩)⟩
    exact Cardinal.mk_eq_zero _

end Decomp

/-! ## Additivity

Over a semisimple *ring* every module is semisimple, so the chosen decompositions of a family
concatenate to a decomposition of its direct sum, and multiplicities add. -/

section Additive

variable {R : Type u} [Ring R] [IsSemisimpleRing R] {n : ℕ} (L : SimpleList R n)

/-- A subtype of a sigma type is the sigma of the subtypes. -/
theorem multOf_sigma {J : Type u} {D : J → Type u} (A : (Σ j, D j) → Type u)
    [∀ p, AddCommGroup (A p)] [∀ p, Module R (A p)] (i : Fin n) :
    multOf L A i = Cardinal.sum fun j => multOf L (fun d : D j => A ⟨j, d⟩) i := by
  simp only [multOf]
  rw [← Cardinal.mk_sigma]
  exact Cardinal.mk_congr
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }

/-- **Multiplicities are additive over direct sums.** -/
theorem mult_dsum {J : Type u} (A : J → Type u) [∀ j, AddCommGroup (A j)] [∀ j, Module R (A j)]
    (i : Fin n) :
    mult (M := ⨁ j, A j) L i = Cardinal.sum fun j => mult (M := A j) L i := by
  classical
  -- the decompositions of the summands concatenate to one of the direct sum
  have e : (⨁ p : (Σ j, decompSet R (A j)), ((p.2 : Submodule R (A p.1)) : Type u))
      ≃ₗ[R] (⨁ m : decompSet R (⨁ j, A j), ((m : Submodule R (⨁ j, A j)) : Type u)) :=
    ((DirectSum.sigmaLcurryEquiv (R := R) (ι := J) (α := fun j => decompSet R (A j))
        (δ := fun j m => ((m : Submodule R (A j)) : Type u))).trans
      (DirectSum.congrLinearEquiv fun j => (decompEquiv R (A j)).symm)).trans
      (decompEquiv R (⨁ j, A j))
  have hA3 := multOf_eq L (fun p : (Σ j, decompSet R (A j)) => decomp_simple R (A p.1) p.2)
    (decomp_simple R (⨁ j, A j)) e i
  rw [mult, ← hA3, multOf_sigma]
  rfl

/-- Splitting a family of simple modules by isomorphism class. -/
noncomputable def classEquiv {J : Type u} (A : J → Type u) [∀ j, AddCommGroup (A j)]
    [∀ j, Module R (A j)] (hA : ∀ j, IsSimpleModule R (A j)) :
    J ≃ Σ i : Fin n, {j : J // Nonempty (A j ≃ₗ[R] L.S i)} where
  toFun j := ⟨L.classOf (hA j), ⟨j, L.classOf_spec (hA j)⟩⟩
  invFun p := p.2.1
  left_inv j := rfl
  right_inv := by
    rintro ⟨i, ⟨j, hj⟩⟩
    have : L.classOf (hA j) = i := L.distinct _ _ ⟨(L.classOf_spec (hA j)).some.symm.trans hj.some⟩
    subst this
    rfl

/-- The normal form of a direct sum of simple modules: group the summands by class, and replace
each by the chosen representative of its class. -/
noncomputable def normalForm {K : Type u} (C : K → Type u) [∀ k, AddCommGroup (C k)]
    [∀ k, Module R (C k)] (hC : ∀ k, IsSimpleModule R (C k)) :
    (⨁ k, C k) ≃ₗ[R] ⨁ i : Fin n, ⨁ _ : {k : K // Nonempty (C k ≃ₗ[R] L.S i)}, L.S i := by
  classical
  exact ((DirectSum.lequivCongrLeft R (classEquiv L C hC)).trans
    (DirectSum.sigmaLcurryEquiv (R := R) (ι := Fin n)
      (α := fun i => {k : K // Nonempty (C k ≃ₗ[R] L.S i)}) (δ := fun i f => C f.1))).trans
    (DirectSum.congrLinearEquiv fun i => DirectSum.congrLinearEquiv fun f => f.2.some)

/-- **Multiplicities determine the module**: two direct sums of simple modules with the same
multiplicities are isomorphic.  Both are brought to the same normal form. -/
noncomputable def equivOfMultOf_eq {J J' : Type u} {A : J → Type u} {B : J' → Type u}
    [∀ j, AddCommGroup (A j)] [∀ j, Module R (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)]
    (hA : ∀ j, IsSimpleModule R (A j)) (hB : ∀ j, IsSimpleModule R (B j))
    (h : ∀ i, multOf L A i = multOf L B i) : (⨁ j, A j) ≃ₗ[R] (⨁ j, B j) := by
  classical
  have hfib : ∀ i : Fin n, Nonempty ({j : J // Nonempty (A j ≃ₗ[R] L.S i)}
      ≃ {j : J' // Nonempty (B j ≃ₗ[R] L.S i)}) := fun i => Cardinal.eq.mp (h i)
  exact (normalForm L A hA).trans
    ((DirectSum.congrLinearEquiv fun i =>
      DirectSum.lequivCongrLeft R (hfib i).some).trans (normalForm L B hB).symm)

end Additive


/-! ## The multiplicity map on `V^κ(R)`

For a summand of `R^{(κ)}` the multiplicities are bounded by `κ`, so they define a map into
`F_κ^n`.  Injectivity is `equivOfMultOf_eq`, and the homomorphism property is `mult_dsum`.
-/

section MultMap

variable {R : Type u} [Ring R] [IsSemisimpleRing R] {κ : Cardinal.{u}} {n : ℕ}
  (L : SimpleList R n)

/-- A simple module is not a subsingleton. -/
theorem not_subsingleton_of_simple {M : Type u} [AddCommGroup M] [Module R M]
    (h : IsSimpleModule R M) : ¬ Subsingleton M := by
  haveI := h
  haveI := IsSimpleModule.nontrivial (R := R) (M := M)
  exact not_subsingleton M

/-- A module isomorphic to a summand of `R^{(κ)}` decomposes into at most `κ` simple modules.
Stated for a plain type `N` rather than for `↥P.1`, so that the module structures on the pieces
of the decomposition are the canonical ones. -/
theorem mk_decompSet_le_of_equiv (hκ : ℵ₀ ≤ κ) (P : Summand R κ) (N : Type u) [AddCommGroup N]
    [Module R N] (e : ↥P.1 ≃ₗ[R] N) : #(decompSet R N) ≤ κ := by
  obtain ⟨T, hT, hsub⟩ := exists_small_support R κ hκ P
    (fun m : decompSet R N => ((m : Submodule R N) : Type u)) (e.trans (decompEquiv R N))
  have huniv : T = Set.univ :=
    Set.eq_univ_of_forall fun m => by
      by_contra hm
      exact not_subsingleton_of_simple (decomp_simple R N m) (hsub m hm)
  rw [huniv, Cardinal.mk_univ] at hT
  exact hT

/-- Every summand of `R^{(κ)}` decomposes into at most `κ` simple modules. -/
theorem mk_decompSet_le (hκ : ℵ₀ ≤ κ) (P : Summand R κ) : #(decompSet R ↥P.1) ≤ κ :=
  mk_decompSet_le_of_equiv hκ P ↥P.1 (LinearEquiv.refl R _)

/-- Multiplicities of a summand of `R^{(κ)}` are at most `κ`. -/
theorem mult_le (hκ : ℵ₀ ≤ κ) (P : Summand R κ) (i : Fin n) :
    mult (M := ↥P.1) L i ≤ κ :=
  le_trans (Cardinal.mk_subtype_le _) (mk_decompSet_le hκ P)

/-- **The multiplicity map** `V^κ(R) → F_κ^n`. -/
noncomputable def multMap (hκ : ℵ₀ ≤ κ) (a : (projClass R κ hκ).carrier) : Fin n → Fcard κ :=
  fun i => Fcard.mk (mult (M := (projClass R κ hκ).rep a) L i) (mult_le L hκ a.out i)

@[simp] theorem val_multMap (hκ : ℵ₀ ≤ κ) (a : (projClass R κ hκ).carrier) (i : Fin n) :
    ((multMap L hκ a i : Fcard κ) : Cardinal.{u})
      = mult (M := (projClass R κ hκ).rep a) L i := rfl

/-- A subsingleton module has no simple summands, so all its multiplicities vanish. -/
theorem mult_of_subsingleton {M : Type u} [AddCommGroup M] [Module R M] [Subsingleton M]
    (i : Fin n) : mult (M := M) L i = 0 := by
  haveI : IsEmpty (decompSet R M) :=
    ⟨fun m => not_subsingleton_of_simple (decomp_simple R M m)
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩⟩
  haveI : IsEmpty {m : decompSet R M // Nonempty (((m : Submodule R M) : Type u) ≃ₗ[R] L.S i)} :=
    ⟨fun p => IsEmpty.false p.1⟩
  exact Cardinal.mk_eq_zero _

/-- **The multiplicity map is a `κ`-homomorphism.** -/
theorem isKHom_multMap (hκ : ℵ₀ ≤ κ) :
    letI := (projClass R κ hκ).instKMonoid hκ
    letI := Fcard.instKMonoid hκ
    letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ
    KMonoid.IsKHom κ (multMap L hκ) := by
  letI := (projClass R κ hκ).instKMonoid hκ
  letI := Fcard.instKMonoid hκ
  letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ
  constructor
  · -- the zero class has a subsingleton representative
    funext i
    apply Subtype.ext
    haveI := (projClass R κ hκ).subsingleton_rep_zero
    rw [val_multMap]
    exact (mult_of_subsingleton L i).trans (Fcard.instKMonoid_zero hκ).symm
  · intro x
    funext i
    apply Subtype.ext
    have hiso := (projClass R κ hκ).rep_sumOf hκ (le_of_eq (mk_Idx κ)) x
    rw [val_multMap, KMonoid.sumOf_Idx (κ := κ)] at *
    rw [mult_congr L hiso.some i, mult_dsum L (fun j => (projClass R κ hκ).rep (x j)) i]
    rfl

/-- **The multiplicity map is injective**: multiplicities determine the module. -/
theorem multMap_injective (hκ : ℵ₀ ≤ κ) : Function.Injective (multMap L hκ) := by
  intro a b h
  refine (projClass R κ hκ).eq_of_iso ?_
  have hmult : ∀ i, mult (M := (projClass R κ hκ).rep a) L i
      = mult (M := (projClass R κ hκ).rep b) L i := by
    intro i
    have := congrArg (fun g : Fin n → Fcard κ => ((g i : Fcard κ) : Cardinal.{u})) h
    rwa [val_multMap, val_multMap] at this
  exact ((decompEquiv R ((projClass R κ hκ).rep a)).trans
    (equivOfMultOf_eq L (decomp_simple R ((projClass R κ hκ).rep a))
      (decomp_simple R ((projClass R κ hκ).rep b)) hmult)).trans
    (decompEquiv R ((projClass R κ hκ).rep b)).symm

/-! ### Surjectivity

A prescribed multiplicity function `f` is realised by `⨁_{p : Σ i, Idx (f i)} S p.1`: it is
projective because each simple module over a semisimple ring is an ideal, hence a direct summand
of `R`; it is generated by `Σ f i ≤ κ` elements because each simple module is cyclic; so it is
isomorphic to a summand of `R^{(κ)}`, and its multiplicities are `f` by axiom A3. -/

/-- A direct summand of a projective module is projective. -/
theorem projective_of_isCompl {M : Type u} [AddCommGroup M] [Module R M] [Module.Projective R M]
    {N K : Submodule R M} (h : IsCompl N K) : Module.Projective R ↥N :=
  Module.Projective.of_split (R := R) (M := M) N.subtype
    (Submodule.projectionOnto N K h) (Submodule.projectionOnto_comp_subtype h)

/-- Over a semisimple ring every simple module is projective: it is isomorphic to an ideal, and
every ideal is a direct summand of `R`. -/
theorem projective_simple (i : Fin n) : Module.Projective R (L.S i) := by
  haveI := L.simple i
  obtain ⟨I, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule (R := R) (M := L.S i)
  obtain ⟨K, hK⟩ := exists_isCompl I
  haveI : Module.Projective R ↥I := projective_of_isCompl hK
  exact Module.Projective.of_equiv e.symm

/-- A simple module is generated by any nonzero element. -/
theorem exists_generator_of_simple {M : Type u} [AddCommGroup M] [Module R M]
    (h : IsSimpleModule R M) : ∃ x : M, Submodule.span R {x} = ⊤ := by
  haveI := h
  haveI := IsSimpleModule.nontrivial (R := R) (M := M)
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  refine ⟨x, ?_⟩
  rcases h.eq_bot_or_eq_top (Submodule.span R {x}) with hb | ht
  · exact absurd (Submodule.span_eq_bot.mp hb x (Set.mem_singleton x)) hx
  · exact ht

/-- A direct sum of cyclic modules is generated by the chosen generators. -/
theorem span_range_gen {K : Type u} [DecidableEq K] (N : K → Type u) [∀ k, AddCommGroup (N k)]
    [∀ k, Module R (N k)] (g : ∀ k, N k) (hg : ∀ k, Submodule.span R {g k} = ⊤) :
    Submodule.span R (Set.range fun k => (lof R K N k (g k) : ⨁ k, N k)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  rw [← DirectSum.sum_support_of x]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp ((hg k).symm ▸ Submodule.mem_top : x k ∈ _)
  have hk : (of (fun k : K => N k) k) (x k) = r • (lof R K N k (g k)) := by
    rw [← lof_eq_of R, ← LinearMap.map_smul, hr]
  rw [hk]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- **The multiplicity map is surjective.** -/
theorem multMap_surjective (hκ : ℵ₀ ≤ κ) : Function.Surjective (multMap L hκ) := by
  intro f
  -- the module with the prescribed multiplicities
  set K : Type u := Σ j : Fin n, Idx ((f j : Fcard κ) : Cardinal.{u}) with hK
  letI : DecidableEq K := Classical.decEq K
  set N : K → Type u := fun p => L.S p.1 with hN
  haveI : ∀ p, Module.Projective R (N p) := fun p => projective_simple L p.1
  -- it has at most `κ` generators
  have hmkK : #K ≤ κ := by
    rw [hK, Cardinal.mk_sigma]
    refine le_trans (Cardinal.sum_le_sum _ (fun _ => κ) fun j =>
      le_of_le_of_eq (le_of_eq (mk_Idx _)) rfl |>.trans (Fcard.le _)) ?_
    rw [Cardinal.sum_const (Fin n) κ, Cardinal.mk_fintype, Fintype.card_fin]
    simp only [Cardinal.lift_natCast, Cardinal.lift_id, Cardinal.lift_id',
      Cardinal.lift_uzero]
    exact le_trans (mul_le_mul' (le_trans (le_of_lt Cardinal.natCast_lt_aleph0) hκ) le_rfl)
      (le_of_eq (Cardinal.mul_eq_self hκ))
  choose g hg using fun p : K => exists_generator_of_simple (L.simple p.1)
  set gens : Set (⨁ k, N k) := Set.range fun k => (lof R K N k (g k) : ⨁ k, N k) with hgensdef
  have hspan : Submodule.span R gens = ⊤ := by
    rw [hgensdef]; exact span_range_gen (R := R) N g hg
  have hcard : #gens ≤ κ := le_trans Cardinal.mk_range_le hmkK
  obtain ⟨P, ⟨e⟩⟩ := exists_summand_of_projective R κ (⨁ k, N k) gens hcard hspan
  set a : (projClass R κ hκ).carrier := Quotient.mk (summandSetoid R κ) P with hadef
  refine ⟨a, ?_⟩
  funext i
  refine Subtype.ext ?_
  show mult (M := (projClass R κ hκ).rep a) L i = ((f i : Fcard κ) : Cardinal.{u})
  -- the representative of the class of `P` is `⨁ N`
  have erep : (projClass R κ hκ).rep a ≃ₗ[R] ⨁ k, N k :=
    (Quotient.mk_out (s := summandSetoid R κ) P).some.trans e
  rw [mult_congr L erep i]
  -- axiom A3 compares the chosen decomposition with the given one
  have hA3 := multOf_eq L (decomp_simple R (⨁ k, N k)) (fun p => L.simple p.1)
    (decompEquiv R (⨁ k, N k)).symm i
  rw [mult, hA3, multOf]
  -- the members of the family in class `i` are exactly those indexed over `Idx (f i)`
  have hequiv : {p : K // Nonempty (N p ≃ₗ[R] L.S i)}
      ≃ Idx ((f i : Fcard κ) : Cardinal.{u}) :=
    (Equiv.subtypeEquivRight fun p =>
      ⟨fun h => L.distinct _ _ h, fun h => ⟨h ▸ LinearEquiv.refl R _⟩⟩).trans
      { toFun := fun p => p.2 ▸ p.1.2
        invFun := fun x => ⟨⟨i, x⟩, rfl⟩
        left_inv := by rintro ⟨⟨j, x⟩, rfl⟩; rfl
        right_inv := fun x => rfl }
  rw [Cardinal.mk_congr hequiv, mk_Idx]

/-! ## Proposition 2.17(1) -/

/-- **Proposition 2.17(1)**: if `R` is a semisimple ring with `n` isomorphism classes of simple
modules, then `V^κ(R) ≅ F_κ^n`.

The isomorphism is the multiplicity map.  It is a homomorphism because multiplicities are
additive, injective because they determine the module, and surjective because every multiplicity
function is realised by a direct sum of simples, which is a summand of `R^{(κ)}`. -/
theorem prop_2_17_one (hκ : ℵ₀ ≤ κ) :
    letI := (projClass R κ hκ).instKMonoid hκ
    letI := Fcard.instKMonoid hκ
    letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ
    KMonoid.IsKHom κ (multMap L hκ) ∧ Function.Bijective (multMap L hκ) :=
  ⟨isKHom_multMap L hκ, multMap_injective L hκ, multMap_surjective L hκ⟩

end MultMap


/-! ## Proposition 2.17(2): semisimple rings with a prescribed number of simple classes

For a field `K`, the ring `Fin n → K` is semisimple and its simple modules are exactly the `n`
coordinates: `K` with `(Fin n → K)` acting through the `i`-th projection. -/

section Exists

variable (K : Type u) [Field K] (n : ℕ)

/-- The `i`-th coordinate of `Fin n → K`.  This is a copy of `K` for each `i`, kept as a separate
type so that the `n` different module structures do not collide in instance resolution. -/
def Coord (i : Fin n) : Type u := K

instance (i : Fin n) : Field (Coord K n i) := inferInstanceAs (Field K)

/-- `Fin n → K` acts on the `i`-th coordinate through the `i`-th projection. -/
noncomputable instance (i : Fin n) : Module (Fin n → K) (Coord K n i) :=
  (Pi.evalRingHom (fun _ : Fin n => K) i).toModule

/-- `Coord K n i` is a copy of `K`; `toK` is the identification. -/
def Coord.toK {i : Fin n} (x : Coord K n i) : K := x

/-- The identification the other way. -/
def Coord.ofK {i : Fin n} (x : K) : Coord K n i := x

theorem Coord.ext {i : Fin n} {a b : Coord K n i} (h : Coord.toK K n a = Coord.toK K n b) :
    a = b := h

@[simp] theorem Coord.toK_smul (i : Fin n) (r : Fin n → K) (x : Coord K n i) :
    Coord.toK K n (r • x) = r i * Coord.toK K n x := rfl

@[simp] theorem Coord.toK_one (i : Fin n) : Coord.toK K n (1 : Coord K n i) = 1 := rfl

@[simp] theorem Coord.toK_zero (i : Fin n) : Coord.toK K n (0 : Coord K n i) = 0 := rfl

/-- A simple quotient of a direct sum of simple modules is one of the summands. -/
theorem exists_equiv_of_surjective_dsum {R : Type u} [Ring R] {ι : Type*} (A : ι → Type u)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] (hA : ∀ i, IsSimpleModule R (A i))
    {M : Type u} [AddCommGroup M] [Module R M] (hM : IsSimpleModule R M)
    (φ : (⨁ i, A i) →ₗ[R] M) (hφ : Function.Surjective φ) :
    ∃ i, Nonempty (A i ≃ₗ[R] M) := by
  classical
  have hne : ∃ i, φ.comp (lof R ι A i) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    haveI := hM
    obtain ⟨x, y, hxy⟩ := (IsSimpleModule.nontrivial (R := R) (M := M)).exists_pair_ne
    obtain ⟨z, rfl⟩ := hφ x
    obtain ⟨w, rfl⟩ := hφ y
    refine hxy ?_
    have hzero : ∀ v : ⨁ i, A i, φ v = 0 := by
      intro v
      rw [← DirectSum.sum_support_of v, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← lof_eq_of R]
      exact congrArg (fun ψ : A k →ₗ[R] M => ψ (v k)) (hcon k)
    rw [hzero z, hzero w]
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, ⟨?_⟩⟩
  haveI := hA i
  haveI := hM
  set ψ := φ.comp (lof R ι A i) with hψ
  have hker : LinearMap.ker ψ = ⊥ := by
    rcases (hA i).eq_bot_or_eq_top (LinearMap.ker ψ) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hi
  have hran : LinearMap.range ψ = ⊤ := by
    rcases hM.eq_bot_or_eq_top (LinearMap.range ψ) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hi
    · exact h
  exact LinearEquiv.ofBijective ψ ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hran⟩

/-- Each coordinate is a simple module: an `R`-submodule of `K` is closed under multiplication by
every element of `K`, because the projection is surjective. -/
instance isSimpleModule_coord (i : Fin n) : IsSimpleModule (Fin n → K) (Coord K n i) := by
  haveI : IsSimpleOrder (Submodule (Fin n → K) (Coord K n i)) :=
    { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩
      eq_bot_or_eq_top := fun N => by
        by_cases h : ∀ x ∈ N, x = 0
        · exact Or.inl (Submodule.eq_bot_iff N |>.mpr h)
        · rw [not_forall] at h
          obtain ⟨x, hx⟩ := h
          rw [Classical.not_imp] at hx
          obtain ⟨hxN, hx0⟩ := hx
          refine Or.inr (le_antisymm le_top fun y _ => ?_)
          have hx0' : Coord.toK K n x ≠ 0 := fun hc => hx0 (Coord.ext K n (by simpa using hc))
          have hmem := N.smul_mem
            (fun _ : Fin n => Coord.toK K n y * (Coord.toK K n x)⁻¹) hxN
          rwa [show ((fun _ : Fin n => Coord.toK K n y * (Coord.toK K n x)⁻¹) • x
              : Coord K n i) = y from Coord.ext K n (by
            rw [Coord.toK_smul]
            field_simp)] at hmem }
  exact ⟨⟩

/-- Distinct coordinates are non-isomorphic: `Pi.single i 1` acts as the identity on the `i`-th
coordinate and as zero on the others. -/
theorem coord_distinct (i j : Fin n) (h : Nonempty (Coord K n i ≃ₗ[Fin n → K] Coord K n j)) :
    i = j := by
  by_contra hij
  obtain ⟨e⟩ := h
  have hsmul := e.map_smul (Pi.single i (1 : K)) (1 : Coord K n i)
  have hL : (Pi.single i (1 : K) : Fin n → K) • (1 : Coord K n i) = (1 : Coord K n i) :=
    Coord.ext K n (by rw [Coord.toK_smul, Coord.toK_one, Pi.single_eq_same, one_mul])
  have hR : (Pi.single i (1 : K) : Fin n → K) • e 1 = 0 :=
    Coord.ext K n (by
      rw [Coord.toK_smul, Coord.toK_zero, Pi.single_eq_of_ne (Ne.symm hij), zero_mul])
  rw [hL, hR] at hsmul
  exact one_ne_zero (α := Coord K n i) (e.injective (by rw [hsmul, map_zero]))

/-- `Fin n → K` is the direct sum of its coordinates, as a module over itself. -/
noncomputable def piEquivDsum : (Fin n → K) ≃ₗ[Fin n → K] ⨁ i : Fin n, Coord K n i :=
  LinearEquiv.symm ((DirectSum.linearEquivFunOnFintype (Fin n → K) (Fin n)
      (fun i => Coord K n i)).trans
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })

/-- Every simple `Fin n → K`-module is one of the coordinates: it is a cyclic quotient of the
ring, which is the direct sum of the coordinates. -/
theorem coord_complete (T : Type u) [AddCommGroup T] [Module (Fin n → K) T]
    (hT : IsSimpleModule (Fin n → K) T) : ∃ i, Nonempty (T ≃ₗ[Fin n → K] Coord K n i) := by
  haveI := hT
  obtain ⟨t, ht⟩ := exists_generator_of_simple (R := Fin n → K) hT
  set ψ : (Fin n → K) →ₗ[Fin n → K] T :=
    { toFun := fun r => r • t
      map_add' := fun _ _ => add_smul _ _ _
      map_smul' := fun _ _ => mul_smul _ _ _ } with hψ
  have hsurj : Function.Surjective ψ := fun y => by
    obtain ⟨r, hr⟩ :=
      Submodule.mem_span_singleton.mp (ht ▸ Submodule.mem_top : y ∈ Submodule.span _ {t})
    exact ⟨r, hr⟩
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_of_surjective_dsum (R := Fin n → K) (fun i => Coord K n i)
    (fun i => isSimpleModule_coord K n i) hT (ψ.comp (piEquivDsum K n).symm.toLinearMap)
    (fun y => by
      obtain ⟨r, hr⟩ := hsurj y
      exact ⟨piEquivDsum K n r, by simpa using hr⟩)
  exact ⟨i, ⟨e.symm⟩⟩

/-- **Proposition 2.17(2)**: for every `n` there is a semisimple ring with exactly `n` isomorphism
classes of simple modules, namely `Fin n → K` for any field `K`. -/
noncomputable def simpleListPi : SimpleList (Fin n → K) n where
  S := fun i => Coord K n i
  simple := fun i => isSimpleModule_coord K n i
  distinct := fun i j h => coord_distinct K n i j h
  complete := fun T _ _ hT => coord_complete K n T hT

end Exists

end KappaMonoid
