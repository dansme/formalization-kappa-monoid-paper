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
  /-- `κ` is infinite, the paper's standing assumption.  Carrying it here makes `V^κ(C)` a
  `κ`-monoid by instance (`ModuleClass.instKMonoid`), with no hypothesis to thread. -/
  aleph0_le : ℵ₀ ≤ κ
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
noncomputable def bareKMonoid : @BareKMonoid κ C.carrier ⟨C.zero⟩ := by
  classical
  have hκ := C.aleph0_le
  letI : Zero C.carrier := ⟨C.zero⟩
  refine
    { aleph0_le := hκ
      i₀ := (nonempty_Idx hκ).some
      ksum := C.dsum
      ksum_single := ?_
      ksum_sigma := ?_ }
  · -- (A1): all but one summand is the zero module
    intro x hx
    generalize (nonempty_Idx hκ).some = i₀ at hx ⊢
    refine C.eq_of_iso ?_
    have hsub : ∀ i, i ≠ i₀ → Subsingleton (C.rep (x i)) := fun i hi => by
      rw [hx i hi]; exact C.subsingleton_rep_zero
    exact (C.dsum_iso x).some.trans (directSumEquivOfSubsingleton R (fun i => C.rep (x i)) i₀ hsub)
  · -- (A2): `V(Σᵢ Σⱼ xᵢⱼ) ≅ ⨁ᵢ V(Σⱼ xᵢⱼ) ≅ ⨁ᵢ ⨁ⱼ V(xᵢⱼ) ≅ ⨁_{(i,j)} V(xᵢⱼ) ≅ ⨁ₖ … ≅ V(Σₖ …)`
    intro x π
    refine C.eq_of_iso ?_
    exact (C.dsum_iso _).some
      ≪≫ₗ DirectSum.congrLinearEquiv (fun i => (C.dsum_iso (x i)).some)
      ≪≫ₗ (DirectSum.sigmaLcurryEquiv (R := R) (δ := fun i j => C.rep (x i j))).symm
      ≪≫ₗ DirectSum.lequivCongrLeft R ((Equiv.sigmaEquivProd (Idx κ) (Idx κ)).trans π)
      ≪≫ₗ (C.dsum_iso _).some.symm

/-- `V^κ(C)` is a `κ`-monoid (Examples 2.3(4)); by Lemma 2.5 (`KMonoid.ofBare`) the additive
structure is determined by the direct sum. -/
noncomputable instance instKMonoid : KMonoid κ C.carrier :=
  @KMonoid.ofBare κ C.carrier ⟨C.zero⟩ C.bareKMonoid

/-- The `κ`-sum on `V^κ(C)` is the direct sum. -/
theorem instKMonoid_ksum (x : Idx κ → C.carrier) : ksum (κ := κ) x = C.dsum x :=
  @KMonoid.ofBare_ksum κ C.carrier ⟨C.zero⟩ C.bareKMonoid x

/-- The zero of `V^κ(C)` is the class of the zero module. -/
theorem instKMonoid_zero : (0 : C.carrier) = C.zero := rfl

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

/-- **Theorem 4.3**'s `C_{λ⁻}`: a subclass of `λ⁻`-small members of `C` closed under
isomorphisms (it is a set of classes), under direct sums of fewer than `λ` modules, and under
direct summands.  Its set of classes is `V^{λ⁻}(C_{λ⁻})`, a `λ⁻`-monoid when `λ` is regular
(`SmallSubclass.instLMonoid`).  `lambdaGenSubclass` is the `Cλ⁻` of Corollary 4.4. -/
structure SmallSubclass (lam : Cardinal.{u}) (hlk : lam ≤ Order.succ κ) where
  /-- The classes of the members of the subclass. -/
  carrier : Set C.carrier
  /-- Every member is `λ⁻`-small. -/
  isLambdaSmall : ∀ a ∈ carrier, IsLambdaSmall R lam (C.rep a)
  /-- Closure under `0` and direct sums of fewer than `λ` modules. -/
  isLSubset : IsLSubset lam hlk carrier
  /-- Closure under direct summands. -/
  summand_mem : ∀ {a b : C.carrier}, a + b ∈ carrier → a ∈ carrier

namespace SmallSubclass

variable {C} {lam : Cardinal.{u}} {hlk : lam ≤ Order.succ κ}

instance : SetLike (C.SmallSubclass lam hlk) C.carrier where
  coe := carrier
  coe_injective S T h := by cases S; cases T; congr

@[simp] theorem mem_carrier {S : C.SmallSubclass lam hlk} {a : C.carrier} :
    a ∈ S.carrier ↔ a ∈ S := Iff.rfl

theorem zero_mem (S : C.SmallSubclass lam hlk) : (0 : C.carrier) ∈ S := S.isLSubset.zero_mem

/-- `V^{λ⁻}(C_{λ⁻})` is a `λ⁻`-monoid, its sums computed in `V^κ(C)`. -/
noncomputable instance instLMonoid [hlam : Fact lam.IsRegular] (S : C.SmallSubclass lam hlk) :
    LMonoid lam S :=
  S.isLSubset.lmonoid hlam.out

/-- Sums in `V^{λ⁻}(C_{λ⁻})` are the ambient `κ`-sums. -/
theorem coe_lsumOf [Fact lam.IsRegular] (S : C.SmallSubclass lam hlk) {ι : Type u}
    (hι : #ι < lam) (z : ι → S) :
    ((LMonoid.lsumOf (lam := lam) hι z : S) : C.carrier)
      = LMonoid.lsumOf (lam := Order.succ κ) (hι.trans_le hlk) fun i => (z i : C.carrier) :=
  rfl

end SmallSubclass

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
