/-
**Bergman's coproduct theorem: the setting.**

Throughout `Bergman/Core/`:

* `k` is a field, `ι` a finite type, `R₀ = k^ι` with its orthogonal idempotents `ee i`;
* `R l` (`l : Λ`, finite) are `k`-algebras made into faithful `k^ι`-rings by `σ l`;
* `C` is their coproduct (`IsCoprod`).

Modules are *left* modules (Bergman works with right modules; everything is mirrored, so a
monomial `s t₁ ⋯ tₙ` of Bergman becomes `tₙ ⋯ t₁ s` here).  Bergman's index `μ ∈ Λ ∪ {0}` is
`μ : Option Λ`, with `Rμ none = k^ι`.

This file fixes the **letter bases**: for each `l, i, j` a `k`-basis of the Peirce component
`e_i (R l) e_j`, containing `e_i` when `i = j` (Bergman §9: bases `ⁱTₗʲ ∪ {e_i}`).
-/
import KappaMonoid.Bergman.IsCoprod

universe u

namespace Bergman.Core

open Module

variable {k : Type u} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]

/-- The idempotent `e_i ∈ k^ι`. -/
def ee (i : ι) : ι → k := Pi.single i 1

theorem ee_mul_ee (i j : ι) : (ee i : ι → k) * ee j = if i = j then ee i else 0 := by
  ext x; by_cases h : i = j <;> by_cases hx : x = i <;> simp_all [ee, Pi.single_apply]

theorem sum_ee : ∑ i : ι, (ee i : ι → k) = 1 := by
  ext x; simp [ee, Pi.single_apply]

/-! ## The family indexed by `Option Λ` -/

variable (k ι R) in
/-- `R_μ`: `k^ι` for `μ = none` (Bergman's `R₀`), `R l` for `μ = some l`. -/
def Rμ : Option Λ → Type u
  | none => ι → k
  | some l => R l

instance Rμ.instRing : ∀ μ : Option Λ, Ring (Rμ k ι R μ)
  | none => inferInstanceAs (Ring (ι → k))
  | some l => inferInstanceAs (Ring (R l))

instance Rμ.instAlgebra : ∀ μ : Option Λ, Algebra k (Rμ k ι R μ)
  | none => inferInstanceAs (Algebra k (ι → k))
  | some l => inferInstanceAs (Algebra k (R l))

variable (σ : ∀ l, (ι → k) →ₐ[k] R l)

/-- The structure maps `k^ι → R_μ`. -/
def σμ : ∀ μ : Option Λ, (ι → k) →ₐ[k] Rμ k ι R μ
  | none => AlgHom.id k (ι → k)
  | some l => σ l

/-- `e_i` in `R_μ`. -/
def eμ (μ : Option Λ) (i : ι) : Rμ k ι R μ := σμ σ μ (ee i)

theorem eμ_mul_eμ (μ : Option Λ) (i j : ι) :
    eμ σ μ i * eμ σ μ j = if i = j then eμ σ μ i else 0 := by
  simp only [eμ, ← map_mul, ee_mul_ee]; split_ifs <;> simp

theorem sum_eμ (μ : Option Λ) : ∑ i, eμ σ μ i = 1 := by
  simp only [eμ, ← map_sum, sum_ee, map_one]

theorem eμ_ne_zero (hσ : ∀ l, Function.Injective (σ l)) (μ : Option Λ) (i : ι) :
    eμ σ μ i ≠ 0 := sorry

/-- The Peirce component `e_i R_μ e_j`, a `k`-subspace. -/
def peirce (μ : Option Λ) (i j : ι) : Submodule k (Rμ k ι R μ) where
  carrier := {r | eμ σ μ i * r * eμ σ μ j = r}
  add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [mul_add, add_mul, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha; simp only [Set.mem_setOf_eq] at *
    rw [mul_smul_comm, smul_mul_assoc, ha]

theorem eμ_mem_peirce (μ : Option Λ) (i : ι) : eμ σ μ i ∈ peirce σ μ i i := by
  show eμ σ μ i * eμ σ μ i * eμ σ μ i = eμ σ μ i
  simp [eμ_mul_eμ]

/-! ## Letter bases -/

/-- A basis of `e_i R_μ e_j` of the form `T ⊔ {e_i if i = j}`. -/
structure LetterBasis (μ : Option Λ) (i j : ι) where
  /-- The letters: the basis elements other than `e_i`. -/
  T : Type u
  /-- The basis. -/
  b : Basis (T ⊕ PLift (i = j)) k (peirce σ μ i j)
  b_inr : ∀ h, (b (Sum.inr h) : Rμ k ι R μ) = eμ σ μ i

theorem nonempty_letterBasis [hσ : Fact (∀ l, Function.Injective (σ l))] (μ : Option Λ) (i j : ι) :
    Nonempty (LetterBasis σ μ i j) := sorry

variable [hσ : Fact (∀ l, Function.Injective (σ l))]

/-- The chosen letter bases. -/
noncomputable def lb (μ : Option Λ) (i j : ι) : LetterBasis σ μ i j :=
  (nonempty_letterBasis σ μ i j).some

/-- The letters of `R_μ` from `j` to `i` (Bergman's `ⁱTᵢʲ`, mirrored). -/
abbrev Tl (μ : Option Λ) (i j : ι) : Type u := (lb σ μ i j).T

/-- The value of a letter. -/
noncomputable def tval {μ : Option Λ} {i j : ι} (t : Tl σ μ i j) : Rμ k ι R μ :=
  (lb σ μ i j).b (Sum.inl t)

theorem tval_mem {μ : Option Λ} {i j : ι} (t : Tl σ μ i j) : tval σ t ∈ peirce σ μ i j :=
  ((lb σ μ i j).b (Sum.inl t)).2

/-- `k^ι` has no letters. -/
theorem isEmpty_Tl_none (i j : ι) : IsEmpty (Tl σ none i j) := sorry

/-- **Peirce decomposition.** `R_μ e_j` (the left ideal) has the `k`-basis
`{tval t : t ∈ T_μ(i, j), i ∈ ι} ∪ {e_j}`. -/
noncomputable def leftIdealBasis (μ : Option Λ) (j : ι) :
    Basis (Option (Σ i, Tl σ μ i j)) k (Submodule.span (Rμ k ι R μ) {eμ σ μ j}) := sorry

theorem leftIdealBasis_none (μ : Option Λ) (j : ι) :
    (leftIdealBasis σ μ j none : Rμ k ι R μ) = eμ σ μ j := sorry

theorem leftIdealBasis_some (μ : Option Λ) (j : ι) (t : Σ i, Tl σ μ i j) :
    (leftIdealBasis σ μ j (some t) : Rμ k ι R μ) = tval σ t.2 := sorry

end Bergman.Core
