/-
Part 3 — Section 3.1: universal `κ`-extensions.

Contents:
* `KMonoid.extend_lhom` — Proposition 3.9;
* `IsUniversalKExtension` — Definition 3.10;
* `universalExtension` — the construction `Ĥ = X^κ / (λ⁻-braiding)` of Theorem 3.11;
* `theorem_3_11` — Theorem 3.11, **with the hypothesis `IsConical X` added**;
* `isConical_of_isUniversalKExtension` — the reason that hypothesis is needed.

The missing hypothesis
----------------------
Theorem 3.11(1) as printed asserts, for an arbitrary `λ⁻`-monoid `H`, the existence of a
`κ`-monoid `Ĥ ⊇ H` which is a `λ⁻`-overmonoid of `H`.  This cannot hold in general: by
Lemma 2.8(1) every `κ`-monoid is reduced, and a `λ⁻`-submonoid of a reduced monoid is
reduced.  For `λ = ℵ₀` a `λ⁻`-monoid is just a commutative monoid, so e.g. `H = ℤ` admits
no such `Ĥ`.  (For `λ > ℵ₀` the analogue of Lemma 2.8 makes reducedness automatic, so the
gap only concerns `λ = ℵ₀`; the paper's Example 2.3(1) already notes that reducedness is
needed there.)

Adding `IsConical H` repairs the statement, and it is exactly the right hypothesis: it is
also *necessary* (`isConical_of_isUniversalKExtension`), and it is what makes the canonical
map `H → Ĥ` injective — see `injective_of_isConical`.
-/
import KappaMonoid.Braiding

universe u v w

open Cardinal Function Set

namespace NS

open KMonoid LMonoid

/-! ## Proposition 3.9 -/

variable {lam κ : Cardinal.{u}}

/-- Proposition 3.9: if the `κ`-monoid `H` is `λ⁻`-braided over `X`, then every
`λ⁻`-homomorphism from `X` to a `κ`-monoid `K` extends uniquely to a `κ`-homomorphism on
`H`.

Paper proof: uniqueness is clear since `X` generates `H`.  For existence, well-definedness
of `φ̄ (Σᵢ xᵢ) := Σᵢ φ (xᵢ)` follows by telescoping along a braiding of two representations
`Σᵢ xᵢ = Σⱼ yⱼ`. -/
theorem extend_lhom {X : Type v} {H : Type w} [LMonoid lam X] [KMonoid κ H]
    (hlk : lam ≤ κ) (f : X → H) (hbr : IsBraidedOver lam κ X H hlk f)
    {K : Type w} [KMonoid κ K] (φ : X → K) (hφ : IsLHom hlk φ) :
    ∃! ψ : H → K, IsKHom κ ψ ∧ ∀ x, ψ (f x) = φ x := by
  sorry

/-! ## Definition 3.10 -/

/-- Definition 3.10: `Ĥ` (with structure map `f`) is a *universal `κ`-extension* of the
`λ⁻`-monoid `X`. -/
structure IsUniversalKExtension (lam κ : Cardinal.{u}) (X : Type v) (Hh : Type w)
    [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ κ) (f : X → Hh) : Prop where
  isLHom : IsLHom hlk f
  universal : ∀ (K : Type w) [KMonoid κ K] (φ : X → K), IsLHom hlk φ →
    ∃! ψ : Hh → K, IsKHom κ ψ ∧ ∀ x, ψ (f x) = φ x

/-- A universal `κ`-extension is unique up to a unique isomorphism, as for any object
defined by a universal property. -/
theorem isUniversalKExtension_unique {X : Type v} {H₁ H₂ : Type w}
    [LMonoid lam X] [KMonoid κ H₁] [KMonoid κ H₂] (hlk : lam ≤ κ)
    {f₁ : X → H₁} {f₂ : X → H₂}
    (h₁ : IsUniversalKExtension lam κ X H₁ hlk f₁)
    (h₂ : IsUniversalKExtension lam κ X H₂ hlk f₂) :
    ∃! e : H₁ → H₂, IsKHom κ e ∧ (∀ x, e (f₁ x) = f₂ x) ∧ Function.Bijective e := by
  sorry

/-- Being `λ⁻`-braided over `X` implies being the universal `κ`-extension of `X`
(the second half of Theorem 3.11(2)); it is immediate from Proposition 3.9. -/
theorem IsBraidedOver.isUniversalKExtension {X : Type v} {H : Type w}
    [LMonoid lam X] [KMonoid κ H] (hlk : lam ≤ κ) {f : X → H}
    (hbr : IsBraidedOver lam κ X H hlk f) :
    IsUniversalKExtension lam κ X H hlk f :=
  { isLHom := hbr.isLHom
    universal := fun K _ φ hφ => extend_lhom hlk f hbr φ hφ }

/-! ## The construction `Ĥ = X^κ / (λ⁻-braiding)` -/

section Construction

variable (lam κ) (X : Type u) [LMonoid lam X]

/-- The underlying type of the universal `κ`-extension: `κ`-indexed families over `X`
modulo `λ⁻`-braiding (Theorem 3.11(1)). -/
def UnivExt : Type u := Quotient (braidingSetoid lam κ X)

namespace UnivExt

variable {lam κ X}

/-- The class of a family. -/
def mk (x : Idx κ → X) : UnivExt lam κ X := Quotient.mk _ x

theorem mk_eq_mk {x y : Idx κ → X} : mk (lam := lam) x = mk y ↔ IsBraided lam x y :=
  Quotient.eq (r := braidingSetoid lam κ X)

/-- Concatenation of a `κ`-indexed family of `κ`-indexed families, using a fixed bijection
`Idx κ × Idx κ ≃ Idx κ`.  This is the operation on `Ĥ`; it is well defined because braidings
can be concatenated (and independent of the bijection by Lemma 3.6(1)). -/
noncomputable def concat (hκ : ℵ₀ ≤ κ) (F : Idx κ → Idx κ → X) : Idx κ → X :=
  fun k => F ((pairEquiv hκ).symm k).1 ((pairEquiv hκ).symm k).2

/-- The `κ`-monoid structure on `Ĥ` (Theorem 3.11(1)). -/
noncomputable def instKMonoid (hlam : lam.IsRegular) (hlk : lam ≤ κ) :
    KMonoid κ (UnivExt lam κ X) := by
  sorry

/-- The canonical `λ⁻`-homomorphism `X → Ĥ`, sending `x` to the class of the family
concentrated at one index. -/
noncomputable def of (i₀ : Idx κ) (x : X) : UnivExt lam κ X :=
  mk (fun i => if i = i₀ then x else 0)

end UnivExt

end Construction

/-! ## Theorem 3.11 -/

/-- **Injectivity of the canonical map**, and the reason reducedness is the right
hypothesis: over a reduced `λ⁻`-monoid `X`, two families concentrated at a single index are
`λ⁻`-braided only if they have the same entry.

Paper-style proof: in a braiding of `(x,0,0,…)` and `(y,0,0,…)`, reducedness forces
`u μ = v μ = 0` for all but at most one index, and the remaining equations give `x = y`. -/
theorem UnivExt.of_injective (hlam : lam.IsRegular) (hlk : lam ≤ κ) {X : Type u}
    [LMonoid lam X] (hred : IsConical X) (i₀ : Idx κ) :
    Function.Injective (UnivExt.of (lam := lam) (κ := κ) (X := X) i₀) := by
  sorry

/-- **Theorem 3.11** (with the hypothesis `IsConical X` added, cf. the module docstring).

Let `λ ≤ κ` with `λ` regular and let `X` be a *reduced* `λ⁻`-monoid.  Then there is a
`κ`-monoid `Ĥ` containing `X` as a `λ⁻`-submonoid such that

1. `Ĥ` is `λ⁻`-braided over `X`, and
2. `Ĥ` is the universal `κ`-extension of `X`. -/
theorem theorem_3_11 (hlam : lam.IsRegular) (hlk : lam ≤ κ) (X : Type u) [LMonoid lam X]
    (hred : IsConical X) :
    ∃ (Hh : Type u) (_ : KMonoid κ Hh) (f : X → Hh),
      Function.Injective f ∧
      IsBraidedOver lam κ X Hh hlk f ∧
      IsUniversalKExtension lam κ X Hh hlk f := by
  sorry

/-- Conversely, a `λ⁻`-monoid admitting a universal `κ`-extension into which it embeds must
be reduced; so the hypothesis added in `theorem_3_11` cannot be dropped. -/
theorem isConical_of_isUniversalKExtension {X : Type v} {Hh : Type w}
    [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ κ) {f : X → Hh}
    (hf : Function.Injective f) (hhom : IsLHom hlk f) : IsConical X := by
  refine LMonoid.isConical_of_injective (lam := lam) (κ := κ) f hf hhom.1 ?_
  intro a b
  -- `f` is additive because `+` is a `λ⁻`-sum over a two-element index type.
  sorry

/-- A concrete counterexample to Theorem 3.11 as printed: `ℤ` is an `ℵ₀⁻`-monoid (i.e. a
commutative monoid) that is not reduced, hence embeds into no `κ`-monoid. -/
example (hlam : (ℵ₀ : Cardinal.{u}).IsRegular) (hlk : (ℵ₀ : Cardinal.{u}) ≤ κ)
    {Hh : Type w} [KMonoid κ Hh] [LMonoid ℵ₀ (ULift.{u} ℤ)]
    (f : ULift.{u} ℤ → Hh) (hf : Function.Injective f) (hhom : IsLHom hlk f) : False := by
  have h := isConical_of_isUniversalKExtension (lam := ℵ₀) hlk hf hhom
  have := h ⟨1⟩ ⟨-1⟩ (by sorry)
  sorry

end NS
