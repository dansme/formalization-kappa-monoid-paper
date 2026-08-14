/-
**The elementary half of Leavitt's theorem.**

A ring with `R^m ≅ R^{m+n}` has `R^k ≅ R^l` for every pair `k ∼_{m,n} l`: add `R^j` to both sides
of the defining isomorphism to move it above `m`, and iterate to add `n` as often as wanted.  No
hypothesis on `R` is needed, and nothing here is deep.

What *is* deep, and stays assumed as axiom A2, is the converse: that a ring with those
isomorphisms and no others exists.  Splitting the two makes the boundary explicit — the axiom
assumes exactly the non-existence of unwanted isomorphisms, and the isomorphisms Leavitt's relation
demands are constructed rather than assumed.

Free modules are indexed here as `Fin k → R`; `LeavittData` uses `⨁ _ : Fin k, R`, and
`nonempty_directSum_of_cyclicRel` is the same statement transported along
`DirectSum.linearEquivFunOnFintype`.
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import KappaMonoid.ForMathlib.CyclicMonoid

universe u

open DirectSum

namespace ModuleType

variable {R : Type u} [Ring R]

/-- `R^(a+b) ≅ R^a ⊕ R^b`. -/
def freeSplit (R : Type u) [Ring R] (a b : ℕ) :
    (Fin (a + b) → R) ≃ₗ[R] (Fin a → R) × (Fin b → R) :=
  (LinearEquiv.funCongrLeft R R (finSumFinEquiv (m := a) (n := b))).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R)

/-- Equal ranks give isomorphic free modules. -/
theorem nonempty_of_eq {a b : ℕ} (h : a = b) : Nonempty ((Fin a → R) ≃ₗ[R] (Fin b → R)) :=
  h ▸ ⟨LinearEquiv.refl R _⟩

/-- A common free summand may be added to both sides. -/
theorem nonempty_add {a b : ℕ} (h : Nonempty ((Fin a → R) ≃ₗ[R] (Fin b → R))) (c : ℕ) :
    Nonempty ((Fin (a + c) → R) ≃ₗ[R] (Fin (b + c) → R)) := by
  obtain ⟨e⟩ := h
  exact ⟨(freeSplit R a c).trans
    ((e.prodCongr (LinearEquiv.refl R (Fin c → R))).trans (freeSplit R b c).symm)⟩

/-- Above `m`, any multiple of `n` may be added to the rank. -/
theorem nonempty_addMul {m n : ℕ} (h : Nonempty ((Fin m → R) ≃ₗ[R] (Fin (m + n) → R)))
    {a : ℕ} (ha : m ≤ a) (t : ℕ) : Nonempty ((Fin a → R) ≃ₗ[R] (Fin (a + n * t) → R)) := by
  induction t with
  | zero => exact nonempty_of_eq (by omega)
  | succ t ih =>
    obtain ⟨e1⟩ := ih
    obtain ⟨e2⟩ := nonempty_add h (a + n * t - m)
    obtain ⟨e3⟩ := nonempty_of_eq (R := R) (show a + n * t = m + (a + n * t - m) by omega)
    obtain ⟨e4⟩ := nonempty_of_eq (R := R)
      (show m + n + (a + n * t - m) = a + n * (t + 1) by rw [Nat.mul_succ]; omega)
    exact ⟨e1.trans (e3.trans (e2.trans e4))⟩

/-- **The isomorphisms `∼_{m,n}` demands are automatic** once `R^m ≅ R^{m+n}`. -/
theorem nonempty_of_cyclicRel {m n : ℕ} (h : Nonempty ((Fin m → R) ≃ₗ[R] (Fin (m + n) → R)))
    {k l : ℕ} (hkl : CyclicRel m n k l) : Nonempty ((Fin k → R) ≃ₗ[R] (Fin l → R)) := by
  have hle : ∀ a b : ℕ, m ≤ a → a ≤ b → n ∣ b - a → Nonempty ((Fin a → R) ≃ₗ[R] (Fin b → R)) := by
    rintro a b hma hab ⟨t, ht⟩
    obtain ⟨e⟩ := nonempty_addMul h hma t
    obtain ⟨e'⟩ := nonempty_of_eq (R := R) (show a + n * t = b by omega)
    exact ⟨e.trans e'⟩
  obtain rfl | ⟨hk, hl, hd⟩ := hkl
  · exact ⟨LinearEquiv.refl R _⟩
  · rcases le_total k l with hkl' | hkl'
    · exact hle k l hk hkl' ((natCast_dvd_sub_iff hkl').mp hd)
    · obtain ⟨e⟩ := hle l k hl hkl' ((natCast_dvd_sub_iff hkl').mp (natCast_dvd_sub_comm.mp hd))
      exact ⟨e.symm⟩

/-- The same statement for `⨁ _ : Fin k, R`, which is how `LeavittData` indexes free modules. -/
theorem nonempty_directSum_of_cyclicRel {m n : ℕ}
    (h : Nonempty ((⨁ _ : Fin m, R) ≃ₗ[R] (⨁ _ : Fin (m + n), R))) {k l : ℕ}
    (hkl : CyclicRel m n k l) : Nonempty ((⨁ _ : Fin k, R) ≃ₗ[R] (⨁ _ : Fin l, R)) := by
  have hfun : ∀ a : ℕ, (⨁ _ : Fin a, R) ≃ₗ[R] (Fin a → R) := fun a =>
    DirectSum.linearEquivFunOnFintype R (Fin a) fun _ => R
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := nonempty_of_cyclicRel
    ⟨((hfun m).symm.trans e).trans (hfun (m + n))⟩ hkl
  exact ⟨((hfun k).trans e').trans (hfun l).symm⟩

end ModuleType
