/-
Section 2.3 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*,

preparation for Proposition 2.16: the class of `R^{(s)}` in `V^κ(𝓕^κ)` depends only on `#s`,
and — for a nontrivial ring — determines `#s` when that is infinite.  The latter is invariance
of infinite rank (axiom A1) once more, and is what makes `[R]` a *faithful* order-unit.
-/
import KappaMonoid.FreeModules
import KappaMonoid.ProjOrderUnit

universe u

open Cardinal Function Set DirectSum
open scoped Classical

namespace KappaMonoid

namespace FreeMod

variable {R : Type u} [Ring R]

/-! ## The standard generators of a free module -/

/-- The standard generators span `R^{(ι)}`.  This is `freeMod_span` for an arbitrary index. -/
theorem span_range_lof (ι : Type u) :
    Submodule.span R (Set.range fun i : ι => (lof R ι (fun _ => R) i 1 : ⨁ _ : ι, R)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  rw [← DirectSum.sum_support_of x]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : (of (fun _ : ι => R) k) (x k) = (x k) • (lof R ι (fun _ => R) k 1) := by
    rw [← lof_eq_of R, ← LinearMap.map_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  rw [hk]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-! ## Invariance of infinite rank, for `R^{(ι)}` -/

/-- If `R^{(ι)} ≅ R^{(ι')}` and `ι` is infinite then `#ι ≤ #ι'`: the standard generators of
`R^{(ι')}` map onto a spanning set of `R^{(ι)}`, and axiom A1 bounds the rank by it. -/
theorem mk_le_of_equiv [Nontrivial R] {ι ι' : Type u} [Infinite ι]
    (e : (⨁ _ : ι, R) ≃ₗ[R] (⨁ _ : ι', R)) : #ι ≤ #ι' :=
  le_trans
    (Projective.mk_le_of_surjective R (e.symm : (⨁ _ : ι', R) →ₗ[R] (⨁ _ : ι, R))
      e.symm.surjective (span_range_lof ι'))
    Cardinal.mk_range_le

/-- Free modules of infinite rank determine their rank. -/
theorem mk_eq_of_equiv [Nontrivial R] {ι ι' : Type u} [Infinite ι]
    (e : (⨁ _ : ι, R) ≃ₗ[R] (⨁ _ : ι', R)) : #ι = #ι' := by
  have h1 : #ι ≤ #ι' := mk_le_of_equiv e
  haveI : Infinite ι' :=
    Cardinal.infinite_iff.mpr ((Cardinal.infinite_iff.mp ‹Infinite ι›).trans h1)
  exact le_antisymm h1 (mk_le_of_equiv e.symm)

/-! ## Classes of free modules and their ranks -/

variable {κ : Cardinal.{u}}

/-- The class of `R^{(s)}` depends only on `#s`. -/
theorem mk_eq_mk_of_mk_eq {s t : Set (Idx κ)} (h : #s = #t) : (mk s : Carrier R κ) = mk t :=
  mk_eq_mk.mpr ⟨DirectSum.lequivCongrLeft R (Cardinal.eq.mp h).some⟩

/-- Conversely, for a nontrivial ring an infinite rank is determined by the class. -/
theorem mk_eq_of_mk_eq_mk [Nontrivial R] {s t : Set (Idx κ)} (hs : ℵ₀ ≤ #s)
    (h : (mk s : Carrier R κ) = mk t) : #s = #t := by
  haveI : Infinite ↥s := Cardinal.infinite_iff.mpr hs
  exact mk_eq_of_equiv (mk_eq_mk.mp h).some

end FreeMod

end KappaMonoid
