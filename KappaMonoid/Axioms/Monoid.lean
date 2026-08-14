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

/-- **Assumed** (Leavitt, 1962).  Every cyclic monoid `C_{m,n}` with `m ≥ 1` and `n ≥ 1` is the
monoid of finitely generated free modules over some ring.

The remaining cyclic monoid, `ℕ₀` itself, needs no axiom: every ring with invariant basis
number realises it.

**`m ≥ 1` is not a convenience, it is necessary**, and the axiom is *false* without it: `C_{0,n}`
identifies `0` with `n`, so a realising ring would have `R^0 ≅ R^n` with `n ≥ 1`, forcing `R = 0`
and contradicting `Nontrivial R`.  A false axiom proves everything, and this one did: at `m = 0`,
`(leavittData 0 1 _).iso_iff 0 1` gives `0 ≅ R` over a nontrivial ring.  Leavitt's theorem is
stated for `m ≥ 1`; the loose form "every cyclic monoid is realised", which the paper quotes and an
earlier version of this file transcribed, is wrong for `C_{0,n}` with `n ≥ 2` — such a monoid is a
group, and `V(𝓕)` of a ring is conical.  Proposition 2.16 never needs it: a faithful order-unit
satisfies no relation `n u = 0` (`KMonoid.nsmul_ne_zero_of_faithful`), so the `m` it produces is
at least `1`. -/
axiom leavittData (m n : ℕ) (_hm : 1 ≤ m) (_hn : 1 ≤ n) : LeavittData.{u} m n

end KappaMonoid
