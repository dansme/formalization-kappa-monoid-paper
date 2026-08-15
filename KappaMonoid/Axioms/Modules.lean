/-
**A5**, the Bergman-Dicks realisation theorem, and **A7**, Albrecht's theorem on projectives over
a hereditary ring.  A7 was a field of `BergmanDicksData` until it was given its own name: it is
about hereditary rings in general, and separating it lets the provenance audit say which of the
two a result actually uses.

Two of the axioms that used to live here have since been proved, in files that depend on nothing
in this development: A3 — uniqueness of the multiplicities of simple modules — in
`ForMathlib/SimpleMultiplicity.lean`, and A6 — Kaplansky's theorem — in `ForMathlib/Kaplansky.lean`.
-/
import Mathlib

universe u

open Cardinal DirectSum

namespace KappaMonoid


/-! ## A5: the Bergman–Dicks realisation theorem -/

/-- A hereditary `k`-algebra realising a given reduced commutative monoid `M` as its monoid of
finitely generated projective modules.

`P a` is the module realising `a ∈ M`; the four conditions `iso_zero`, `iso_add`, `inj` and
`surj` say exactly that `a ↦ [P a]` is a monoid isomorphism `M ≅ V(R)`, and `iso_unit` says that
it carries the given order-unit `u` to the class of `R` itself. -/
structure BergmanDicksData (k : Type u) [Field k] (M : Type u) [AddCommMonoid M] (u : M) where
  /-- The realising algebra. -/
  R : Type u
  [ring : Ring R]
  [algebra : Algebra k R]
  /-- `R` is hereditary: every left ideal is projective. -/
  hereditary : ∀ I : Ideal R, Module.Projective R I
  /-- The finitely generated projective module realising `a ∈ M`. -/
  P : M → Type u
  [addCommGroup : ∀ a, AddCommGroup (P a)]
  [module : ∀ a, Module R (P a)]
  proj : ∀ a, Module.Projective R (P a)
  fin : ∀ a, Module.Finite R (P a)
  /-- `P 0 = 0`. -/
  iso_zero : Subsingleton (P 0)
  /-- `P (a + b) ≅ P a ⊕ P b`. -/
  iso_add : ∀ a b, Nonempty (P (a + b) ≃ₗ[R] P a × P b)
  /-- `a ↦ [P a]` is injective. -/
  inj : ∀ a b, Nonempty (P a ≃ₗ[R] P b) → a = b
  /-- `a ↦ [P a]` is onto the finitely generated projectives. -/
  surj : ∀ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q), Module.Projective R Q →
    Module.Finite R Q → ∃ a, Nonempty (Q ≃ₗ[R] P a)
  /-- The order-unit is the class of the ring itself: `[R] = u`.  Bergman's construction gives
  this, and it is what makes the *free* modules over `R` visible in `M`: `R^k` realises `k • u`. -/
  iso_unit : Nonempty (P u ≃ₗ[R] R)

attribute [instance] BergmanDicksData.ring BergmanDicksData.algebra
  BergmanDicksData.addCommGroup BergmanDicksData.module

/-- **Assumed** (Bergman 1974; Bergman–Dicks 1978).  For every field `k`, every reduced
commutative monoid with an order-unit is `V(R)` for a hereditary `k`-algebra `R`.

*Reduced* is the paper's term for conical: `a + b = 0` forces `a = 0`.  An *order-unit* is a `u`
such that every element divides some multiple of `u`.

Provenance, field by field.  **Bergman, *Coproducts and some universal ring constructions*, Trans.
AMS 200 (1974), Theorem 6.2**: for a field `k` and a *finitely generated* abelian semigroup `A`
(his "semigroup" means monoid) with distinguished `I ≠ 0` satisfying (i) `x + y = 0 ⇒ x = y = 0`
and (ii) `∀ x, ∃ y, n ≥ 0, x + y = nI`, there is a right and left hereditary `k`-algebra `R` with
`S_⊕(P-Mod R) ≅ A` *as semigroups with distinguished element* `I` — and Theorem 6.1 fixes that
distinguished element to be `[R]`, the class of the free module of rank 1.  So (i) is `_hred`,
(ii) is `_hunit`, the isomorphism is `iso_zero`/`iso_add`/`inj`/`surj`, and "with distinguished
element" is `iso_unit`.  **Bergman–Dicks, *Universal derivations and universal ring constructions*,
Pacific J. Math. 79 (1978), Theorem 3.4** and the paragraph after it remove the finite-generation
hypothesis — "one may drop the words *finitely generated* from Theorem 6.2" — via direct limits,
which is what licenses an arbitrary `M` here.

Two differences from the sources, both checked:

* The papers are about **right** modules (Bergman §2), this statement about left ones, and
  `Ideal R` is `Submodule R R`, so `hereditary` is *left* hereditary.  Theorem 6.2 gives both
  sides, and `V` transfers by the duality Bergman records in §3: `* = Hom(_, R)` is a contravariant
  equivalence between the finitely generated projective right and left modules, additive and
  carrying `R` to `R`, hence a monoid isomorphism `V_right(R) ≅ V_left(R)` fixing the class of `R`.
* Theorem 6.2 assumes `I ≠ 0`; there is no `u ≠ 0` here.  That is safe rather than an oversight:
  with `_hred` and `_hunit`, `u = 0` forces `M` to be trivial (`y + z = n • 0 = 0` gives `y = 0`),
  and the zero ring realises the trivial monoid — every ideal projective, `V(0)` trivial,
  `[0] = 0`.  Nothing here claims `Nontrivial R`, which is what keeps the degenerate case honest;
  a `Nontrivial R` field together with a monoid only the zero ring can realise is exactly how the
  earlier statement of Leavitt's theorem became false.

The proof is a construction by universal localisation and is far out of reach here; Mathlib has
neither hereditary rings nor universal localisation.  The statement used to bundle Albrecht's
theorem as a `sumOfFG` field, since Corollary 4.7(1) uses the two together; that is now A7
below, which is where it belongs — it is a statement about hereditary rings in general, not
about the one this axiom produces. -/
axiom bergmanDicksData (k : Type u) [Field k] (M : Type u) [AddCommMonoid M] (u : M)
    (_hred : ∀ a b : M, a + b = 0 → a = 0)
    (_hunit : ∀ y : M, ∃ (z : M) (n : ℕ), y + z = n • u) :
    BergmanDicksData.{u} k M u

/-! ## A7: projective modules over a hereditary ring -/

/-- **Assumed** (Albrecht 1961; Bergman 1972).  Over a hereditary ring every projective module is
a direct sum of finitely generated projective modules.

Albrecht proves it for semihereditary rings, which is more than is needed here.  Mathlib has
neither hereditary rings nor this decomposition, and the argument — a transfinite filtration of a
free module compatible with the projective summand, as for Kaplansky's theorem — is not monoid
theory, so it is assumed rather than proved.

This is exactly the content of Corollary 4.6 in the hereditary case, which is why the shape below
matches `EveryProjectiveIsSumOfFG` and the hypothesis of `corollary_4_5_three` verbatim: applied
to a hereditary ring it plugs straight into both.  It was a field of `BergmanDicksData` until it
was moved here; carrying it separately is what lets a result say which of the two quoted theorems
it actually uses. -/
axiom albrecht_classical {R : Type u} [Ring R]
    (_hered : ∀ I : Ideal R, Module.Projective R I) :
    ∀ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q), Module.Projective R Q →
      ∃ (ι : Type u) (S : ι → Type u) (_ : ∀ i, AddCommGroup (S i)) (_ : ∀ i, Module R (S i)),
        (∀ i, Module.Projective R (S i)) ∧ (∀ i, Module.Finite R (S i)) ∧
          Nonempty (Q ≃ₗ[R] ⨁ i, S i)

end KappaMonoid
