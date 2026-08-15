/-
**Homomorphisms out of a cyclic module commute with direct sums.**

`Hom_R(S, ⨁ i, A i) ≅ ⨁ i, Hom_R(S, A i)` when `S` is cyclic.  Mathlib has the easy direction —
Hom *out of* a direct sum is a product — but not this one, which needs the source to be small:
a map out of `S = R ∙ s` is pinned by the image of `s`, and that image has finite support.

The intended use is uniqueness of the multiplicities of simple modules: a simple module is
cyclic, `Hom_R(S, A)` is the endomorphism division ring when `A ≅ S` and zero otherwise (Schur), so
the left side becomes a free module whose rank is the multiplicity of `S`.

Both sides carry the action of `Module.End R S` by *pre*composition, which is a right action, hence
a `(Module.End R S)ᵐᵒᵖ`-module structure; the equivalence below is stated additively and
`map_precomp` records that it commutes with that action, which is what makes it an isomorphism of
`(Module.End R S)ᵐᵒᵖ`-modules where one is needed.
-/
import Mathlib.Algebra.DirectSum.Module

universe u

open DirectSum

open scoped Classical

variable {R : Type u} [Ring R] {S : Type u} [AddCommGroup S] [Module R S]
  {ι : Type u} [DecidableEq ι] {A : ι → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]

/-- The `i`-th components of a homomorphism, packaged with the support of the image of `s`.
For cyclic `S` with generator `s` this really is the family of components — `componentsOf_apply`. -/
noncomputable def componentsOf (s : S) (f : S →ₗ[R] ⨁ i, A i) : ⨁ i, (S →ₗ[R] A i) :=
  DFinsupp.mk (f s).support fun i => (component R ι A (i : ι)).comp f

section Cyclic

variable {s : S} (hs : Submodule.span R {s} = ⊤)

include hs

omit [DecidableEq ι] in
/-- A homomorphism out of a cyclic module vanishes in the `i`-th component as soon as it does so
on the generator. -/
theorem component_comp_eq_zero (f : S →ₗ[R] ⨁ i, A i) {i : ι}
    (hi : (f s) i = 0) : (component R ι A i).comp f = 0 := by
  ext x
  obtain ⟨r, rfl⟩ :=
    Submodule.mem_span_singleton.mp (hs ▸ Submodule.mem_top : x ∈ Submodule.span R {s})
  show (f (r • s)) i = 0
  rw [map_smul]
  show r • ((f s) i) = 0
  rw [hi, smul_zero]

@[simp] theorem componentsOf_apply (f : S →ₗ[R] ⨁ i, A i) (i : ι) :
    componentsOf s f i = (component R ι A i).comp f := by
  show (DFinsupp.mk (β := fun i => S →ₗ[R] A i) (f s).support
    fun j => (component R ι A (j : ι)).comp f) i = _
  rw [DFinsupp.mk_apply]
  split_ifs with h
  · rfl
  · exact (component_comp_eq_zero hs f (DFinsupp.notMem_support_iff.mp h)).symm

end Cyclic

/-- Assemble a finitely supported family of homomorphisms into one homomorphism into the direct
sum. -/
noncomputable def ofComponents (g : ⨁ i, (S →ₗ[R] A i)) : S →ₗ[R] ⨁ i, A i where
  toFun x := DFinsupp.sum g fun i gi => lof R ι A i (gi x)
  map_add' x y := by
    simp only [map_add]
    rw [← DFinsupp.sum_add]
  map_smul' r x := by
    simp only [map_smul, RingHom.id_apply]
    rw [DFinsupp.sum, DFinsupp.sum, Finset.smul_sum]

@[simp] theorem ofComponents_apply (g : ⨁ i, (S →ₗ[R] A i)) (x : S) (i : ι) :
    (ofComponents g x) i = g i x := by
  show (DFinsupp.sum g fun j gj => lof R ι A j (gj x)) i = g i x
  rw [DFinsupp.sum, DFinsupp.finsetSum_apply]
  by_cases hi : i ∈ g.support
  · rw [Finset.sum_eq_single i]
    · rw [lof_eq_of, of_eq_same]
    · intro j _ hj
      rw [lof_eq_of, of_eq_of_ne _ _ _ (Ne.symm hj)]
    · exact fun h => absurd hi h
  · have hzero : ∀ j ∈ g.support, (lof R ι A j (g j x)) i = 0 := by
      intro j hj
      have hne : i ≠ j := fun h => hi (h ▸ hj)
      rw [lof_eq_of, of_eq_of_ne _ _ _ hne]
    rw [Finset.sum_eq_zero hzero]
    have hg : g i = 0 := DFinsupp.notMem_support_iff.mp hi
    rw [hg]
    simp

/-- **Hom out of a cyclic module commutes with direct sums.** -/
noncomputable def homDirectSumAddEquiv {s : S} (hs : Submodule.span R {s} = ⊤) :
    (S →ₗ[R] ⨁ i, A i) ≃+ (⨁ i, (S →ₗ[R] A i)) where
  toFun := componentsOf s
  invFun := ofComponents
  left_inv f := by
    ext x i
    rw [ofComponents_apply, componentsOf_apply hs]
    rfl
  right_inv g := by
    ext i x
    rw [componentsOf_apply hs]
    exact ofComponents_apply g x i
  map_add' f g := by
    ext i x
    simp [componentsOf_apply hs]

/-- The equivalence commutes with precomposition, so it is an isomorphism of modules over
`(Module.End R S)ᵐᵒᵖ` wherever one is needed. -/
theorem homDirectSumAddEquiv_precomp {s : S} (hs : Submodule.span R {s} = ⊤)
    (f : S →ₗ[R] ⨁ i, A i) (d : Module.End R S) (i : ι) :
    homDirectSumAddEquiv hs (f.comp d) i = ((homDirectSumAddEquiv hs f) i).comp d := by
  ext x
  simp [homDirectSumAddEquiv, componentsOf_apply hs]
