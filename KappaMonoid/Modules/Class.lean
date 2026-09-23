/-
**Definition 2.4**: `ModuleClass R κ` — a class of modules closed under `κ`-indexed direct sums,
given by its isomorphism classes — and the `κ`-monoid `V^κ(C)` it carries.
-/
import KappaMonoid.Modules.DirectSum

universe u v w

open Cardinal Function Set DirectSum
open scoped Classical

namespace KappaMonoid

open KMonoid LMonoid

variable (R : Type u) [Ring R]


/-! ## Classes of modules and `V^κ(C)` -/

/-- A class of `R`-modules, closed under `κ`-indexed direct sums and isomorphisms, and whose
isomorphism classes form the set `carrier` (Definition 2.4).  Closure under direct summands is not
part of the structure; it is the separate class `IsSummandClosed`. -/
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

/-- The subclass of `λ⁻`-small members of `C` (Definition 4.1).  Theorem 4.3 is stated for a
subclass of these; `lambdaGenPart` is the `Cλ⁻` of Corollaries 4.4 and 4.5. -/
def lambdaSmallPart (lam : Cardinal.{u}) : Set C.carrier :=
  {a | IsLambdaSmall R lam (C.rep a)}

/-- `Cλ⁻`: the subclass of members of `C` generated by strictly fewer than `λ` elements.  This is
the subclass Corollaries 4.4 and 4.5 are stated for; Example 4.2(3) is
`lambdaGenPart_subset_lambdaSmallPart`, `lambdaGenPart_isLSubset` and `lambdaGenPart_summand`. -/
def lambdaGenPart (lam : Cardinal.{u}) : Set C.carrier :=
  {a | IsLambdaGenerated R lam (C.rep a)}

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

end KappaMonoid
