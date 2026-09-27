/-
`CardLT ι λ`: the standing assumption `#ι < λ` as a type class, and small sets.

The paper sums over index sets of cardinality `< λ` without mentioning the bound: `Σ_{i ∈ I} x_i`
presupposes `|I| < λ`.  Here that presupposition is an instance `[CardLT ι λ]`, found by instance
search from the rules below (finite types, products, sums, sigma types, subsets, unions, images),
the way Mathlib finds `[Fintype ι]` for `∑ i : ι, f i`.

A `SmallSet λ ι` is a subset of `ι` of cardinality `< λ` (as `Finset` is to finiteness); its
coercion to a type carries the instance, so a sum over a piece of a partition by small sets needs
no bound.  The product, sum and sigma rules need `λ` regular, as the instance `[Fact λ.IsRegular]`.
-/
import KappaMonoid.Core.Index

universe u

open Cardinal

namespace KappaMonoid

/-- `ι` has fewer than `lam` elements. -/
class CardLT (ι : Type u) (lam : Cardinal.{u}) : Prop where
  lt : #ι < lam

namespace CardLT

variable {lam : Cardinal.{u}}

instance (priority := low) of_finite [hlam : Fact lam.IsRegular] (ι : Type u) [Finite ι] :
    CardLT ι lam :=
  ⟨mk_lt_of_finite hlam.out ι⟩

instance prod [hlam : Fact lam.IsRegular] (α β : Type u) [hα : CardLT α lam] [hβ : CardLT β lam] :
    CardLT (α × β) lam :=
  ⟨mk_prod_lt hlam.out hα.lt hβ.lt⟩

instance sum [hlam : Fact lam.IsRegular] (α β : Type u) [hα : CardLT α lam] [hβ : CardLT β lam] :
    CardLT (α ⊕ β) lam :=
  ⟨mk_sum_lt hlam.out hα.lt hβ.lt⟩

instance sigma [hlam : Fact lam.IsRegular] {ι : Type u} (ρ : ι → Type u) [hι : CardLT ι lam]
    [hρ : ∀ i, CardLT (ρ i) lam] : CardLT ((i : ι) × ρ i) lam :=
  ⟨mk_sigma_lt hlam.out hι.lt fun i => (hρ i).lt⟩

/-- A subtype of a small type is small. -/
instance subtype {ι : Type u} [h : CardLT ι lam] (p : ι → Prop) : CardLT {i // p i} lam :=
  ⟨(mk_subtype_le p).trans_lt h.lt⟩

instance union [hlam : Fact lam.IsRegular] {ι : Type u} (S T : Set ι) [hS : CardLT S lam]
    [hT : CardLT T lam] : CardLT ↥(S ∪ T) lam :=
  ⟨mk_union_lt hlam.out hS.lt hT.lt⟩

instance image {ι κ : Type u} (f : ι → κ) (S : Set ι) [hS : CardLT S lam] :
    CardLT ↥(f '' S) lam :=
  ⟨mk_image_le.trans_lt hS.lt⟩

/-- Moving along an equivalence of index types. -/
theorem of_equiv {ι ι' : Type u} (e : ι ≃ ι') [h : CardLT ι' lam] : CardLT ι lam :=
  ⟨(mk_congr e).trans_lt h.lt⟩

end CardLT

/-- A subset of `ι` of cardinality `< lam`: the pieces of an indexed partition in Definition 3.1. -/
def SmallSet (lam : Cardinal.{u}) (ι : Type u) : Type u := {S : Set ι // #S < lam}

namespace SmallSet

variable {lam : Cardinal.{u}} {ι : Type u}

instance : CoeOut (SmallSet lam ι) (Set ι) := ⟨Subtype.val⟩

/-- A small set as an index type, directly (not through `Set ι`: a double coercion `↥↑S` would
defeat instance search). -/
instance : CoeSort (SmallSet lam ι) (Type u) := ⟨fun S => ↥S.1⟩

instance (S : SmallSet lam ι) : CardLT S lam := ⟨S.2⟩

theorem small (S : SmallSet lam ι) : #(S : Set ι) < lam := S.2

@[ext] theorem ext {S T : SmallSet lam ι} (h : (S : Set ι) = T) : S = T := Subtype.ext h

/-- A set that is small, as a small set. -/
def of (S : Set ι) [h : CardLT S lam] : SmallSet lam ι := ⟨S, h.lt⟩

@[simp] theorem coe_of (S : Set ι) [CardLT S lam] : ((of (lam := lam) S : SmallSet lam ι) : Set ι) = S :=
  rfl

end SmallSet

end KappaMonoid
