/-
**A2** Leavitt's realisation of the cyclic monoids `C_{m,n}`.  It is monoid-theoretic; it mentions
no module beyond the free ones.

Only the hard half of A2 is assumed: `ForMathlib/ModuleType.lean` proves that `R^m ≅ R^{m+n}`
forces every isomorphism `∼_{m,n}` demands, so what is left to assume is the absence of any
others.

**A4**, the classification of cyclic monoids, lived here until it was proved:
`ForMathlib/CyclicMonoid.lean`, which is also where `CyclicRel` now lives.
-/
import Mathlib
import KappaMonoid.ForMathlib.CyclicMonoid
import KappaMonoid.ForMathlib.ModuleType

universe u

open Cardinal DirectSum

namespace KappaMonoid


/-! ## A2: Leavitt's realisation theorem -/

/-- A ring realising the cyclic monoid `C_{m,n}` as its monoid of finitely generated free
modules: `R^k ≅ R^l` exactly when `k ∼_{m,n} l`.

Only *half* of that is assumed.  The isomorphisms `∼_{m,n}` demands all follow from the single
relation `R^m ≅ R^{m+n}` — that is `ForMathlib/ModuleType.lean`, and it is elementary.  What is
assumed is `iso_imp`: that a ring exists with those isomorphisms and **no others**.  That is the
whole content of Leavitt's theorem, and `iso_iff` below recovers the two-way form. -/
structure LeavittData (m n : ℕ) where
  /-- The realising ring. -/
  R : Type u
  [ring : Ring R]
  [nontrivial : Nontrivial R]
  /-- The defining relation `R^m ≅ R^{m+n}`. -/
  iso : Nonempty ((⨁ _ : Fin m, R) ≃ₗ[R] (⨁ _ : Fin (m + n), R))
  /-- No other isomorphisms: `R^k ≅ R^l` forces `k ∼_{m,n} l`. -/
  iso_imp : ∀ k l : ℕ, Nonempty ((⨁ _ : Fin k, R) ≃ₗ[R] (⨁ _ : Fin l, R)) → CyclicRel m n k l

attribute [instance] LeavittData.ring LeavittData.nontrivial

/-- Isomorphism of finitely generated free modules over the realising ring is exactly `∼_{m,n}`.
The `←` direction is proved, not assumed. -/
theorem LeavittData.iso_iff {m n : ℕ} (d : LeavittData.{u} m n) (k l : ℕ) :
    Nonempty ((⨁ _ : Fin k, d.R) ≃ₗ[d.R] (⨁ _ : Fin l, d.R)) ↔ CyclicRel m n k l :=
  ⟨d.iso_imp k l, ModuleType.nonempty_directSum_of_cyclicRel d.iso⟩

/-- **Assumed** (Leavitt, 1962).  Every cyclic monoid `C_{m,n}` with `m ≥ 1` and `n ≥ 1` is the
monoid of finitely generated free modules over some ring.

The remaining cyclic monoid, `ℕ₀` itself, needs no axiom: every ring with invariant basis
number realises it.

**`m ≥ 1` is not a convenience, it is necessary**, and the axiom is *false* without it: `C_{0,n}`
identifies `0` with `n`, so a realising ring would have `R^0 ≅ R^n` with `n ≥ 1`, forcing `R = 0`
and contradicting `Nontrivial R`.  A false axiom proves everything, and this one did: at `m = 0`
its `iso_iff` gave `0 ≅ R` over a nontrivial ring.  Leavitt's theorem is stated for `m ≥ 1`;
the loose form "every cyclic monoid is realised", which the paper quotes and an
earlier version of this file transcribed, is wrong for `C_{0,n}` with `n ≥ 2` — such a monoid is a
group, and `V(𝓕)` of a ring is conical.  Proposition 2.16 never needs it: a faithful order-unit
satisfies no relation `n u = 0` (`KMonoid.nsmul_ne_zero_of_faithful`), so the `m` it produces is
at least `1`. -/
axiom leavittData (m n : ℕ) (_hm : 1 ≤ m) (_hn : 1 ≤ n) : LeavittData.{u} m n

end KappaMonoid
