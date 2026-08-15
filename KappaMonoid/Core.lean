/-
A Lean 4 / Mathlib formalisation of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

The core: infinite summation, `κ`-monoids and `λ⁻`-monoids.  This file is the entry point of
the layer — import it to get all of `KappaMonoid/Core/`, which depends on no module theory and on
no assumed result.

Design notes (see also `README.md`):

* Index sets.  The paper indexes by the von Neumann cardinal `κ` itself.  We let the
  summation operation act on families indexed by an *arbitrary* type of the right size:
  `λ⁻`-monoids sum families indexed by any `ι` with `#ι < λ`.  Nothing has to be transported
  along a chosen bijection, and the reindexing law is an axiom rather than a theorem.

* One theory, not two.  A `κ`-monoid is exactly a `λ⁻`-monoid for `λ = κ⁺` (Remark 2.19;
  `#ι ≤ κ ↔ #ι < κ⁺`, and `κ⁺` is regular).  So `LMonoid` is developed once and `KMonoid`
  extends it; the `κ`-level names (`sumOf`, `ksum`, …) are a thin layer on top.

* Underlying additive monoid.  By Lemma 2.5 a `λ⁻`-monoid carries a canonical commutative
  monoid structure with `a + b = Σ²(a, b)`.  Following Mathlib's forgetful-inheritance
  convention, `LMonoid` *extends* `AddCommMonoid` and adds the compatibility axiom
  `add_eq_lsumOf`; this prevents a second, propositionally-equal `+` from appearing on types
  that already have one.  Nothing is lost: `SumData.toLMonoid` builds the additive structure
  from the summation alone (Lemma 2.5).

* (A1).  The paper states (A1) for the distinguished element `0 ∈ κ`.  Here it is the
  statement that a sum over a one-point index type is its unique entry, which needs no
  distinguished element and no `0`.
-/
import KappaMonoid.Core.Index
import KappaMonoid.Core.SumData
import KappaMonoid.Core.LMonoid
import KappaMonoid.Core.KMonoid
import KappaMonoid.Core.Subobject
import KappaMonoid.Core.Bare
import KappaMonoid.Core.LHom
