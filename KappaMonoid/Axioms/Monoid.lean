/-
**A2** Leavitt's realisation of the cyclic monoids `C_{m,n}`.  It is monoid-theoretic; it mentions
no module beyond the free ones.

**A4**, the classification of cyclic monoids, lived here until it was proved:
`ForMathlib/CyclicMonoid.lean`, which is also where `CyclicRel` now lives.
-/
import Mathlib
import KappaMonoid.ForMathlib.CyclicMonoid

universe u

open Cardinal DirectSum

namespace KappaMonoid


/-! ## A2: Leavitt's realisation theorem -/

/-- A ring realising the cyclic monoid `C_{m,n}` as its monoid of finitely generated free
modules: `R^k ≅ R^l` exactly when `k ∼_{m,n} l`. -/
structure LeavittData (m n : ℕ) where
  /-- The realising ring. -/
  R : Type u
  [ring : Ring R]
  [nontrivial : Nontrivial R]
  /-- Isomorphism of finitely generated free modules is exactly `∼_{m,n}`. -/
  iso_iff : ∀ k l : ℕ,
    Nonempty ((⨁ _ : Fin k, R) ≃ₗ[R] (⨁ _ : Fin l, R)) ↔ CyclicRel m n k l

attribute [instance] LeavittData.ring LeavittData.nontrivial

/-- **Assumed** (Leavitt, 1962).  Every cyclic monoid `C_{m,n}` with `n ≥ 1` is the monoid of
finitely generated free modules over some ring.

The remaining cyclic monoid, `ℕ₀` itself, needs no axiom: every ring with invariant basis
number realises it. -/
axiom leavittData (m n : ℕ) (_hn : 1 ≤ n) : LeavittData.{u} m n

end KappaMonoid
