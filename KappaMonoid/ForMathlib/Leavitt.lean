/-
**The Leavitt algebra of type `(m, N)`.**

The universal ring with `R^m ≅ R^N`: generators `x i j` (an `m × N` matrix `X`) and `y j i` (an
`N × m` matrix `Y`), relations `XY = I_m` and `YX = I_N`.  Over `ℤ`, not over a field — the
mod-`n` half of the module type is read off `R / [R,R]`, and over a `ℚ`-algebra that quotient is a
`ℚ`-vector space, where the torsion the argument needs cannot live.

This file is the presentation and the easy direction: `X` and `Y` are mutually inverse over the
quotient, so `R^m ≅ R^N`.  What the ring is *not* — no unwanted isomorphisms of free modules — needs
a normal form, and is elsewhere.
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import KappaMonoid.ForMathlib.FreeTrace

namespace Leavitt

/-- The generators of the Leavitt algebra: the entries of an `m × N` matrix `X` and of an
`N × m` matrix `Y`. -/
inductive Gen (m N : ℕ)
  | x : Fin m → Fin N → Gen m N
  | y : Fin N → Fin m → Gen m N
  deriving DecidableEq

/-- The free `ℤ`-algebra on the generators. -/
abbrev Free (m N : ℕ) : Type := FreeAlgebra ℤ (Gen m N)

/-- `X` as a matrix over the free algebra. -/
def freeX (m N : ℕ) : Matrix (Fin m) (Fin N) (Free m N) :=
  Matrix.of fun i j => FreeAlgebra.ι ℤ (Gen.x i j)

/-- `Y` as a matrix over the free algebra. -/
def freeY (m N : ℕ) : Matrix (Fin N) (Fin m) (Free m N) :=
  Matrix.of fun j i => FreeAlgebra.ι ℤ (Gen.y j i)

/-- The defining relations `XY = I_m` and `YX = I_N`, entry by entry. -/
inductive Rel (m N : ℕ) : Free m N → Free m N → Prop
  | xy (i i' : Fin m) : Rel m N ((freeX m N * freeY m N) i i') ((1 : Matrix _ _ _) i i')
  | yx (j j' : Fin N) : Rel m N ((freeY m N * freeX m N) j j') ((1 : Matrix _ _ _) j j')

/-- **The Leavitt algebra of type `(m, N)`**: the universal ring with `R^m ≅ R^N`. -/
abbrev Alg (m N : ℕ) : Type := RingQuot (Rel m N)

variable (m N : ℕ)

/-- The quotient map, as a `ℤ`-algebra homomorphism. -/
noncomputable def mk : Free m N →ₐ[ℤ] Alg m N := RingQuot.mkAlgHom ℤ (Rel m N)

/-- `X` over the Leavitt algebra. -/
noncomputable def X : Matrix (Fin m) (Fin N) (Alg m N) :=
  (freeX m N).map (mk m N)

/-- `Y` over the Leavitt algebra. -/
noncomputable def Y : Matrix (Fin N) (Fin m) (Alg m N) :=
  (freeY m N).map (mk m N)

theorem X_mul_Y : X m N * Y m N = 1 := by
  ext i i'
  have h : (X m N * Y m N) i i' = mk m N ((freeX m N * freeY m N) i i') := by
    simp [X, Y, Matrix.mul_apply, Matrix.map_apply, map_sum]
  have hrel : mk m N ((freeX m N * freeY m N) i i')
      = mk m N ((1 : Matrix (Fin m) (Fin m) (Free m N)) i i') :=
    RingQuot.mkAlgHom_rel ℤ (Rel.xy i i')
  rw [h, hrel]
  by_cases hii : i = i' <;> simp [Matrix.one_apply, hii]

theorem Y_mul_X : Y m N * X m N = 1 := by
  ext j j'
  have h : (Y m N * X m N) j j' = mk m N ((freeY m N * freeX m N) j j') := by
    simp [X, Y, Matrix.mul_apply, Matrix.map_apply, map_sum]
  have hrel : mk m N ((freeY m N * freeX m N) j j')
      = mk m N ((1 : Matrix (Fin N) (Fin N) (Free m N)) j j') :=
    RingQuot.mkAlgHom_rel ℤ (Rel.yx j j')
  rw [h, hrel]
  by_cases hjj : j = j' <;> simp [Matrix.one_apply, hjj]

/-- **`R^m ≅ R^N` over the Leavitt algebra.** -/
noncomputable def freeEquiv : (Fin m → Alg m N) ≃ₗ[Alg m N] (Fin N → Alg m N) :=
  FreeTrace.equivOfMatrices (X m N) (Y m N) (X_mul_Y m N) (Y_mul_X m N)

end Leavitt
