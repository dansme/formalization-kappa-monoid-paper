/-
**Lifting along square-zero extensions.**

For a surjective ring map `π : T → T'` whose kernel squares to zero, idempotent matrices and
isomorphisms between the images of idempotent matrices lift from `T'` to `T`.  These are the
two lifting properties that make the realising algebra quasi-free (`Bergman/MainRing.lean`).
-/
import Mathlib

universe u

namespace Bergman

open Matrix

variable {T T' : Type*} [Ring T] [Ring T'] (π : T →+* T')

/-- `π` is surjective with square-zero kernel. -/
structure SqZero : Prop where
  surj : Function.Surjective π
  sq : ∀ x y, π x = 0 → π y = 0 → x * y = 0

variable {π}

namespace SqZero

variable (hπ : SqZero π)
include hπ

theorem exists_lift {m n : Type*} (X' : Matrix m n T') : ∃ X : Matrix m n T, X.map π = X' :=
  ⟨fun a b => (hπ.surj (X' a b)).choose, by ext a b; exact (hπ.surj (X' a b)).choose_spec⟩

theorem mul_eq_zero {l m n : Type*} [Fintype m] {X : Matrix l m T} {Y : Matrix m n T}
    (hX : X.map π = 0) (hY : Y.map π = 0) : X * Y = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => hπ.sq _ _ ?_ ?_
  · exact congrFun (congrFun hX a) c
  · exact congrFun (congrFun hY c) b

end SqZero

/-- The idempotent correction: if `a * a = a + n` with `n` commuting with `a` and `n * n = 0`,
then `a + n - 2 a n` is idempotent. -/
theorem idem_correction {A : Type*} [Ring A] {a n : A} (h1 : a * a = a + n) (h2 : a * n = n * a)
    (h3 : n * n = 0) : (a + n - 2 * (a * n)) * (a + n - 2 * (a * n)) = a + n - 2 * (a * n) := by
  have h4 : a * n * n = 0 := by rw [mul_assoc, h3, mul_zero]
  have h5 : n * (a * n) = 0 := by rw [← mul_assoc, ← h2, h4]
  have h6 : a * n * a = a * n + 0 := by rw [mul_assoc, ← h2, ← mul_assoc, h1, add_mul, h3]
  have h7 : a * (a * n) = a * n := by rw [← mul_assoc, h1, add_mul, h3, add_zero]
  have h8 : a * n * (a * n) = 0 := by rw [← mul_assoc, h6, add_zero, h4]
  have h9 : n * a = a * n := h2.symm
  simp only [two_mul, mul_add, add_mul, mul_sub, sub_mul, h1, h3, h4, h5, h7, h8, h9,
    add_zero, sub_zero]
  simp only [h6, add_zero]
  abel

variable (hπ : SqZero π)
include hπ

/-- **Idempotent matrices lift** along square-zero extensions. -/
theorem SqZero.exists_idem_lift {n : Type*} [Fintype n] [DecidableEq n] {e' : Matrix n n T'}
    (he' : e' * e' = e') : ∃ e : Matrix n n T, e * e = e ∧ e.map π = e' := by
  obtain ⟨a, ha⟩ := hπ.exists_lift e'
  set nn := a * a - a with hnn
  have hn0 : nn.map π = 0 := by
    rw [hnn, Matrix.map_sub _ (map_sub π), Matrix.map_mul, ha, he', sub_self]
  refine ⟨a + nn - 2 * (a * nn), idem_correction (by rw [hnn]; abel) ?_ (hπ.mul_eq_zero hn0 hn0),
    ?_⟩
  · rw [hnn, mul_sub, sub_mul, mul_assoc]
  · rw [Matrix.map_sub _ (map_sub π), Matrix.map_add _ (map_add π), hn0, Matrix.map_mul,
      Matrix.map_mul, hn0, mul_zero, mul_zero, add_zero, sub_zero, ha]

/-- **Isomorphisms between images of idempotents lift** along square-zero extensions: if
`D`, `D'` are idempotent over `T` and `a`, `b` are mutually inverse maps between the images of
`π D`, `π D'`, then they lift to mutually inverse maps between the images of `D`, `D'`. -/
theorem SqZero.exists_iso_lift {m m' : Type*} [Fintype m] [Fintype m'] [DecidableEq m]
    [DecidableEq m'] {D : Matrix m m T} {D' : Matrix m' m' T} (hD : D * D = D)
    (hD' : D' * D' = D') {a : Matrix m m' T'} {b : Matrix m' m T'}
    (ha : D.map π * a * D'.map π = a) (hb : D'.map π * b * D.map π = b)
    (hab : a * b = D.map π) (hba : b * a = D'.map π) :
    ∃ (A : Matrix m m' T) (B : Matrix m' m T), D * A * D' = A ∧ D' * B * D = B ∧ A * B = D ∧
      B * A = D' ∧ A.map π = a ∧ B.map π = b := by
  obtain ⟨A0, hA0⟩ := hπ.exists_lift a
  obtain ⟨B0, hB0⟩ := hπ.exists_lift b
  set A := D * A0 * D' with hA
  set B1 := D' * B0 * D with hB1
  have hAπ : A.map π = a := by rw [hA, Matrix.map_mul, Matrix.map_mul, hA0, ha]
  have hB1π : B1.map π = b := by rw [hB1, Matrix.map_mul, Matrix.map_mul, hB0, hb]
  have hDA : D * A = A := by rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hD]
  have hAD : A * D' = A := by rw [hA, Matrix.mul_assoc, hD']
  have hD'B1 : D' * B1 = B1 := by rw [hB1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hD']
  have hB1D : B1 * D = B1 := by rw [hB1, Matrix.mul_assoc, hD]
  set nn := A * B1 - D with hnn
  clear_value nn
  have hn0 : nn.map π = 0 := by
    rw [hnn, Matrix.map_sub _ (map_sub π), Matrix.map_mul, hAπ, hB1π, hab, sub_self]
  have hDn : D * nn = nn := by rw [hnn, Matrix.mul_sub, ← Matrix.mul_assoc, hDA, hD]
  have hnD : nn * D = nn := by rw [hnn, Matrix.sub_mul, Matrix.mul_assoc, hB1D, hD]
  have hnn0 : nn * nn = 0 := hπ.mul_eq_zero hn0 hn0
  set B := B1 * (D - nn) with hB
  clear_value B
  have hAB : A * B = D := by
    have : A * B1 = D + nn := by rw [hnn]; abel
    rw [hB, ← Matrix.mul_assoc, this, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, hD, hDn, hnD, hnn0]; abel
  have hDA' : D * A * D' = A := by rw [hDA, hAD]
  have hBD : B * D = B := by rw [hB, Matrix.mul_assoc, Matrix.sub_mul, hD, hnD]
  have hD'B : D' * B = B := by rw [hB, ← Matrix.mul_assoc, hD'B1]
  have hBπ : B.map π = b := by
    have hbD : b * D.map π = b := by rw [← hb, Matrix.mul_assoc, ← Matrix.map_mul, hD]
    rw [hB, Matrix.map_mul, Matrix.map_sub _ (map_sub π), hn0, sub_zero, hB1π, hbD]
  -- `f = B * A` is an idempotent in the corner of `D'`, congruent to `D'`, hence equal to it
  set f := B * A with hf
  clear_value f
  have hff : f * f = f := by rw [hf, Matrix.mul_assoc, ← Matrix.mul_assoc A, hAB, ← Matrix.mul_assoc, hBD]
  have hD'f : D' * f = f := by rw [hf, ← Matrix.mul_assoc, hD'B]
  have hfD' : f * D' = f := by rw [hf, Matrix.mul_assoc, hAD]
  have hg0 : (D' - f).map π = 0 := by
    rw [Matrix.map_sub _ (map_sub π), hf, Matrix.map_mul, hBπ, hAπ, hba, sub_self]
  have hgg : (D' - f) * (D' - f) = D' - f := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, hD', hD'f, hfD', hff]; abel
  have hBA : B * A = D' := by
    have := hπ.mul_eq_zero hg0 hg0
    rw [hgg, sub_eq_zero] at this
    rw [← hf]; exact this.symm
  exact ⟨A, B, hDA', by rw [hD'B, hBD], hAB, hBA, hAπ, hBπ⟩

end Bergman
