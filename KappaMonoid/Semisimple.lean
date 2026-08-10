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
import KappaMonoid.Examples
import KappaMonoid.Axioms

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

end MultMap

end KappaMonoid
