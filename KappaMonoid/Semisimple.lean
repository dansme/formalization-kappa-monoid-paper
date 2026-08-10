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

end KappaMonoid
