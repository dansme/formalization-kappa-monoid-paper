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

set_option linter.unusedSectionVars false

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
    eμ σ μ i ≠ 0 := by
  have h0 : (ee i : ι → k) ≠ 0 := by
    intro h; have := congrFun h i; simp [ee] at this
  cases μ with
  | none => exact h0
  | some l => exact (map_ne_zero_iff _ (hσ l)).2 h0

/-- The Peirce component `e_i R_μ e_j`, a `k`-subspace. -/
def peirce (μ : Option Λ) (i j : ι) : Submodule k (Rμ k ι R μ) where
  carrier := {r | eμ σ μ i * r * eμ σ μ j = r}
  add_mem' := by intro a b ha hb; simp only [Set.mem_ofPred_eq] at *; rw [mul_add, add_mul, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha; simp only [Set.mem_ofPred_eq] at *
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
    Nonempty (LetterBasis σ μ i j) := by
  classical
  by_cases h : i = j
  · subst h
    set x : peirce σ μ i i := ⟨eμ σ μ i, eμ_mem_peirce σ μ i⟩
    have hx : x ≠ 0 := fun h0 => eμ_ne_zero σ hσ.out μ i (congrArg Subtype.val h0)
    have hs : LinearIndepOn k id ({x} : Set (peirce σ μ i i)) := LinearIndepOn.singleton hx
    let b := Basis.extend hs
    let B := hs.extend (Set.subset_univ _)
    have hxB : x ∈ B := hs.subset_extend _ (Set.mem_singleton x)
    let e : B ≃ {v : B // (v : peirce σ μ i i) ≠ x} ⊕ PLift (i = i) :=
      (Equiv.sumCompl (fun v : B => (v : peirce σ μ i i) ≠ x)).symm.trans
        (Equiv.sumCongr (Equiv.refl _)
          { toFun := fun _ => ⟨rfl⟩
            invFun := fun _ => ⟨⟨x, hxB⟩, by simp⟩
            left_inv := fun v => by
              obtain ⟨v, hv⟩ := v
              simp only [not_not] at hv
              exact Subtype.ext (Subtype.ext hv.symm)
            right_inv := fun _ => rfl })
    refine ⟨⟨_, b.reindex e, fun _ => ?_⟩⟩
    rw [Basis.reindex_apply]
    have : e.symm (Sum.inr ⟨rfl⟩) = ⟨x, hxB⟩ := rfl
    rw [this]
    exact congrArg Subtype.val (congrFun (Basis.coe_extend hs) ⟨x, hxB⟩)
  · have : IsEmpty (PLift (i = j)) := ⟨fun ⟨h'⟩ => h h'⟩
    exact ⟨⟨_, (Basis.ofVectorSpace k (peirce σ μ i j)).reindex (Equiv.sumEmpty _ _).symm,
      fun h' => (IsEmpty.false h').elim⟩⟩

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

theorem eμ_mul_tval {μ : Option Λ} {i j : ι} (t : Tl σ μ i j) : eμ σ μ i * tval σ t = tval σ t := by
  have h := tval_mem σ t
  change eμ σ μ i * tval σ t * eμ σ μ j = tval σ t at h
  rw [← h, ← mul_assoc, ← mul_assoc, eμ_mul_eμ, if_pos rfl]

theorem tval_mul_eμ {μ : Option Λ} {i j : ι} (t : Tl σ μ i j) : tval σ t * eμ σ μ j = tval σ t := by
  have h := tval_mem σ t
  change eμ σ μ i * tval σ t * eμ σ μ j = tval σ t at h
  rw [← h, mul_assoc, eμ_mul_eμ, if_pos rfl]

/-- `k^ι` has no letters. -/
theorem isEmpty_Tl_none (i j : ι) : IsEmpty (Tl σ none i j) := by
  classical
  refine ⟨fun t => ?_⟩
  set b := (lb σ none i j).b
  let r : ι → k := tval σ t
  have hmem : (ee i : ι → k) * r * ee j = r := tval_mem σ t
  have hrx : ∀ x, r x = (if x = i then 1 else 0) * r x * (if x = j then 1 else 0) := fun x => by
    conv_lhs => rw [← hmem]
    simp [ee, Pi.single_apply]
  by_cases h : i = j
  · subst h
    -- every element of `e_i k^ι e_i` is a multiple of `e_i`
    have hc : b (Sum.inl t) = (r i) • b (Sum.inr ⟨rfl⟩) := by
      apply Subtype.ext
      rw [Submodule.coe_smul, (lb σ none i i).b_inr]
      change r = r i • (ee i : ι → k)
      funext x
      rw [hrx x]
      by_cases hx : x = i
      · subst hx; simp [ee]
      · simp [ee, hx]
    have := congrArg (fun v => b.repr v (Sum.inl t)) hc
    simp at this
  · have h0 : b (Sum.inl t) = 0 := by
      apply Subtype.ext
      change r = 0
      funext x
      rw [hrx x]
      by_cases hx : x = i
      · subst hx; simp [h]
      · simp [hx]
    exact b.ne_zero _ h0

/-- `R_μ e_j = ⊕_i e_i R_μ e_j`, as `k`-spaces. -/
noncomputable def peirceEquiv (μ : Option Λ) (j : ι) :
    Submodule.span (Rμ k ι R μ) {eμ σ μ j} ≃ₗ[k] ∀ i, peirce σ μ i j := by
  have hr : ∀ x ∈ Submodule.span (Rμ k ι R μ) {eμ σ μ j}, x * eμ σ μ j = x := by
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [smul_eq_mul, mul_assoc, eμ_mul_eμ, if_pos rfl]
  exact
  { toFun := fun x i => ⟨eμ σ μ i * x, by
      change eμ σ μ i * (eμ σ μ i * x) * eμ σ μ j = eμ σ μ i * x
      rw [← mul_assoc, eμ_mul_eμ, if_pos rfl, mul_assoc, hr x x.2]⟩
    invFun := fun p => ⟨∑ i, (p i : Rμ k ι R μ), Submodule.sum_mem _ fun i _ => by
      rw [← (p i).2]
      exact Submodule.mem_span_singleton.2 ⟨eμ σ μ i * p i, rfl⟩⟩
    map_add' := fun x y => by ext i; simp [mul_add]
    map_smul' := fun c x => by ext i; simp
    left_inv := fun x => by
      ext; simp [← Finset.sum_mul, sum_eμ]
    right_inv := fun p => by
      ext i
      simp only [Finset.mul_sum]
      rw [Finset.sum_eq_single i]
      · have h := (p i).2
        change eμ σ μ i * p i * eμ σ μ j = p i at h
        rw [← h, ← mul_assoc, ← mul_assoc, eμ_mul_eμ, if_pos rfl]
      · intro i' _ hi'
        have h := (p i').2
        change eμ σ μ i' * p i' * eμ σ μ j = p i' at h
        rw [← h, ← mul_assoc, ← mul_assoc, eμ_mul_eμ, if_neg (Ne.symm hi'), zero_mul, zero_mul]
      · simp }

theorem peirceEquiv_symm_apply (μ : Option Λ) (j : ι) (p : ∀ i, peirce σ μ i j) :
    ((peirceEquiv σ μ j).symm p : Rμ k ι R μ) = ∑ i, (p i : Rμ k ι R μ) := rfl

/-- Reindexing the Peirce basis. -/
def peirceIdx (μ : Option Λ) (j : ι) :
    (Σ i, Tl σ μ i j ⊕ PLift (i = j)) ≃ Option (Σ i, Tl σ μ i j) where
  toFun
    | ⟨i, Sum.inl t⟩ => some ⟨i, t⟩
    | ⟨_, Sum.inr _⟩ => none
  invFun
    | some ⟨i, t⟩ => ⟨i, Sum.inl t⟩
    | none => ⟨j, Sum.inr ⟨rfl⟩⟩
  left_inv := by
    rintro ⟨i, t | h⟩
    · rfl
    · obtain ⟨h⟩ := h; subst h; rfl
  right_inv := by rintro (_ | ⟨i, t⟩) <;> rfl

/-- **Peirce decomposition.** `R_μ e_j` (the left ideal) has the `k`-basis
`{tval t : t ∈ T_μ(i, j), i ∈ ι} ∪ {e_j}`. -/
noncomputable def leftIdealBasis (μ : Option Λ) (j : ι) :
    Basis (Option (Σ i, Tl σ μ i j)) k (Submodule.span (Rμ k ι R μ) {eμ σ μ j}) :=
  ((Pi.basis fun i => (lb σ μ i j).b).map (peirceEquiv σ μ j).symm).reindex (peirceIdx σ μ j)

theorem leftIdealBasis_none (μ : Option Λ) (j : ι) :
    (leftIdealBasis σ μ j none : Rμ k ι R μ) = eμ σ μ j := by
  classical
  rw [leftIdealBasis, Basis.reindex_apply, Basis.map_apply]
  change ((peirceEquiv σ μ j).symm (Pi.basis (fun i => (lb σ μ i j).b) ⟨j, Sum.inr ⟨rfl⟩⟩) :
    Rμ k ι R μ) = _
  rw [peirceEquiv_symm_apply, Pi.basis_apply]
  rw [Finset.sum_eq_single j]
  · simp [(lb σ μ j j).b_inr]
  · intro i _ hi; simp [hi]
  · simp

theorem leftIdealBasis_some (μ : Option Λ) (j : ι) (t : Σ i, Tl σ μ i j) :
    (leftIdealBasis σ μ j (some t) : Rμ k ι R μ) = tval σ t.2 := by
  classical
  rw [leftIdealBasis, Basis.reindex_apply, Basis.map_apply]
  change ((peirceEquiv σ μ j).symm (Pi.basis (fun i => (lb σ μ i j).b) ⟨t.1, Sum.inl t.2⟩) :
    Rμ k ι R μ) = _
  rw [peirceEquiv_symm_apply, Pi.basis_apply]
  rw [Finset.sum_eq_single t.1]
  · simp [tval]
  · intro i _ hi; simp [hi]
  · simp

end Bergman.Core
