/-
**Uniqueness of the multiplicities of simple modules**, infinite multiplicities included.

If `⨁ i, A i ≅ ⨁ j, B j` with all `A i` and `B j` simple, then for every module `S` the number of
`i` with `A i ≅ S` equals the number of `j` with `B j ≅ S`.  Jordan–Hölder gives the finite case;
this is the cardinal form, and it was assumed as axiom A3 of this development until proved here.

The argument is the classical one.  Fix a simple `S` and let `D = End_R(S)`, a division ring by
Schur.  Applying `Hom_R(S, -)`:

* `Hom_R(S, ⨁ i, A i) ≅ ⨁ i, Hom_R(S, A i)`, because `S` is cyclic — this is
  `ForMathlib/HomDirectSum.lean`, and it is the part Mathlib does not have;
* `Hom_R(S, A i)` is `D` when `A i ≅ S` and `0` otherwise, again by Schur;
* so the rank of `Hom_R(S, ⨁ A)` counts exactly the `i` with `A i ≅ S`, and rank over a division
  ring is well defined.

The isomorphism `⨁ A ≅ ⨁ B` carries `Hom_R(S, ⨁ A)` to `Hom_R(S, ⨁ B)` by postcomposition, so the
two counts agree.

`Module.End R S` acts on `S →ₗ[R] M` by *pre*composition, which is a right action; the module
structure is therefore over `(Module.End R S)ᵐᵒᵖ`, which is a division ring just the same.
-/
import KappaMonoid.ForMathlib.HomDirectSum
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Field.Opposite
import Mathlib.LinearAlgebra.Basis.VectorSpace

universe u

open Cardinal DirectSum

namespace SimpleMultiplicity

variable {R : Type u} [Ring R] {S : Type u} [AddCommGroup S] [Module R S]

/-- Precomposition makes `S →ₗ[R] M` a module over `(Module.End R S)ᵐᵒᵖ`.  It is a right action of
`Module.End R S`, hence a left action of its opposite. -/
instance homPrecomp (M : Type u) [AddCommGroup M] [Module R M] :
    Module (Module.End R S)ᵐᵒᵖ (S →ₗ[R] M) where
  smul d f := f.comp d.unop
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  add_smul d₁ d₂ f := by ext x; exact f.map_add _ _
  zero_smul f := by ext x; exact f.map_zero

theorem smul_def {M : Type u} [AddCommGroup M] [Module R M] (d : (Module.End R S)ᵐᵒᵖ)
    (f : S →ₗ[R] M) : d • f = f.comp d.unop := rfl

/-- `Module.End.instDivisionRing` (Schur) is stated with a `DecidableEq` hypothesis, so supplying
one classically is what puts the division-ring structure — and with it the rank theory — in
scope. -/
noncomputable instance decidableEqEnd : DecidableEq (Module.End R S) := Classical.decEq _

/-! ## The two Schur computations -/

/-- If `A` is simple and not isomorphic to the simple module `S`, there are no homomorphisms
`S → A`. -/
theorem subsingleton_hom_of_not_iso [IsSimpleModule R S] {A : Type u} [AddCommGroup A] [Module R A]
    [IsSimpleModule R A] (h : ¬ Nonempty (A ≃ₗ[R] S)) : Subsingleton (S →ₗ[R] A) := by
  refine ⟨fun f g => ?_⟩
  suffices hz : ∀ f : S →ₗ[R] A, f = 0 by rw [hz f, hz g]
  intro f
  by_contra hf
  exact h ⟨(LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)).symm⟩

/-- Postcomposition with an isomorphism `A ≅ A'` is `(Module.End R S)ᵐᵒᵖ`-linear. -/
noncomputable def homCongr {A A' : Type u} [AddCommGroup A] [Module R A] [AddCommGroup A']
    [Module R A'] (e : A ≃ₗ[R] A') : (S →ₗ[R] A) ≃ₗ[(Module.End R S)ᵐᵒᵖ] (S →ₗ[R] A') where
  toFun f := (e : A →ₗ[R] A').comp f
  invFun f := (e.symm : A' →ₗ[R] A).comp f
  left_inv f := by ext x; exact e.symm_apply_apply _
  right_inv f := by ext x; exact e.apply_symm_apply _
  map_add' f g := by ext x; exact e.map_add _ _
  map_smul' d f := rfl

/-- `End_R(S)` is free of rank one over its own opposite: the action is right multiplication. -/
noncomputable def endEquivOp [IsSimpleModule R S] :
    (S →ₗ[R] S) ≃ₗ[(Module.End R S)ᵐᵒᵖ] (Module.End R S)ᵐᵒᵖ where
  toFun f := MulOpposite.op f
  invFun d := d.unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-! ## The rank of `Hom_R(S, ⨁ A i)` counts the copies of `S` -/

variable {ι : Type u} {A : ι → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]

/-- The `(Module.End R S)ᵐᵒᵖ`-linear form of `homDirectSumAddEquiv`: the additive equivalence of
`ForMathlib/HomDirectSum.lean` commutes with precomposition. -/
noncomputable def homDirectSumEquiv [IsSimpleModule R S] [DecidableEq ι] {s : S}
    (hs : Submodule.span R {s} = ⊤) :
    (S →ₗ[R] ⨁ i, A i) ≃ₗ[(Module.End R S)ᵐᵒᵖ] (⨁ i, (S →ₗ[R] A i)) :=
  { homDirectSumAddEquiv hs with
    map_smul' := fun d f => by
      ext i x
      exact congrArg (fun (h : S →ₗ[R] A i) => h x) (homDirectSumAddEquiv_precomp hs f d.unop i) }

/-- A summand isomorphic to `S` contributes one dimension. -/
theorem rank_hom_eq_one [IsSimpleModule R S] {A : Type u} [AddCommGroup A] [Module R A]
    (e : A ≃ₗ[R] S) : Module.rank (Module.End R S)ᵐᵒᵖ (S →ₗ[R] A) = 1 := by
  rw [(homCongr e).rank_eq, endEquivOp.rank_eq]
  exact Module.rank_self _

/-- A summand not isomorphic to `S` contributes none. -/
theorem rank_hom_eq_zero [IsSimpleModule R S] {A : Type u} [AddCommGroup A] [Module R A]
    [IsSimpleModule R A] (h : ¬ Nonempty (A ≃ₗ[R] S)) :
    Module.rank (Module.End R S)ᵐᵒᵖ (S →ₗ[R] A) = 0 := by
  haveI := subsingleton_hom_of_not_iso (S := S) (A := A) h
  exact rank_subsingleton' _ _

/-- **The multiplicity of `S`, read off the rank.** -/
theorem rank_hom_directSum [IsSimpleModule R S] (hA : ∀ i, IsSimpleModule R (A i)) {s : S}
    (hs : Submodule.span R {s} = ⊤) :
    Module.rank (Module.End R S)ᵐᵒᵖ (S →ₗ[R] ⨁ i, A i) = #{i // Nonempty (A i ≃ₗ[R] S)} := by
  have hcomp : ∀ i, Module.rank (Module.End R S)ᵐᵒᵖ (S →ₗ[R] A i)
      = #(ULift.{u} (PLift (Nonempty (A i ≃ₗ[R] S)))) := by
    intro i
    haveI := hA i
    by_cases h : Nonempty (A i ≃ₗ[R] S)
    · haveI : Inhabited (ULift.{u} (PLift (Nonempty (A i ≃ₗ[R] S)))) := ⟨ULift.up (PLift.up h)⟩
      haveI : Unique (ULift.{u} (PLift (Nonempty (A i ≃ₗ[R] S)))) := Unique.mk' _
      rw [Cardinal.mk_eq_one]
      exact rank_hom_eq_one h.some
    · haveI : IsEmpty (ULift.{u} (PLift (Nonempty (A i ≃ₗ[R] S)))) := ⟨fun x => h x.down.down⟩
      rw [Cardinal.mk_eq_zero]
      exact rank_hom_eq_zero h
  classical
  haveI : ∀ i, Module.Free (Module.End R S)ᵐᵒᵖ (S →ₗ[R] A i) := fun i => inferInstance
  rw [(homDirectSumEquiv hs).rank_eq, rank_directSum]
  simp_rw [hcomp]
  rw [← Cardinal.mk_sigma]
  exact Cardinal.mk_congr (Equiv.sigmaULiftPLiftEquivSubtype _)

/-! ## A3 -/

/-- **Uniqueness of the multiplicities of simple modules**, infinite multiplicities included.

This was axiom A3 of this development. -/
theorem mk_multiplicity_eq {J : Type u} {B : J → Type u} [∀ j, AddCommGroup (B j)]
    [∀ j, Module R (B j)] (hA : ∀ i, IsSimpleModule R (A i)) (hB : ∀ j, IsSimpleModule R (B j))
    (e : (⨁ i, A i) ≃ₗ[R] (⨁ j, B j)) (S : Type u) [AddCommGroup S] [Module R S] :
    #{i // Nonempty (A i ≃ₗ[R] S)} = #{j // Nonempty (B j ≃ₗ[R] S)} := by
  classical
  by_cases hS : IsSimpleModule R S
  · -- a simple module is cyclic: any nonzero element generates
    haveI := hS
    haveI := IsSimpleModule.nontrivial R S
    obtain ⟨s, hs0⟩ := exists_ne (0 : S)
    have hs : Submodule.span R {s} = ⊤ :=
      (eq_bot_or_eq_top _).resolve_left fun h => hs0 <| by
        simpa using (Submodule.eq_bot_iff _).mp h s (Submodule.mem_span_singleton_self s)
    rw [← rank_hom_directSum hA hs, ← rank_hom_directSum hB hs]
    exact (LinearEquiv.rank_eq (homCongr e))
  · -- otherwise nothing is isomorphic to `S`, and both counts are zero
    have hempty : ∀ {K : Type u} {C : K → Type u} [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)],
        (∀ k, IsSimpleModule R (C k)) → IsEmpty {k // Nonempty (C k ≃ₗ[R] S)} := by
      intro K C _ _ hC
      exact ⟨fun k => hS (by haveI := hC k.1; exact IsSimpleModule.congr k.2.some.symm)⟩
    haveI := hempty hA
    haveI := hempty hB
    simp

end SimpleMultiplicity
