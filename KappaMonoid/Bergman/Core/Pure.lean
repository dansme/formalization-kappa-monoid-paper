/-
**Purity, leading terms, well-positioned families** (Bergman §5, mirrored), and **Lemma 5.1**.

* `IsPureS l y`: `y ≠ 0` and all its terms of top degree lie on side `l` (Bergman's `λ`-pure);
  `IsPure none y`: `y` is `l`-pure for no `l` (Bergman's `0`-pure).
* `IsLead μ y u`: `y` is not `μ`-pure and `u` is its `μ`-leading term (the greatest top-degree
  term not on side `l`, for `μ = some l`; the leading term, for `μ = none`).
* `WP L`: **Definition 5.2**, well-positioned families of subsets `L μ ⊆ Std`.
* `lead_letter`: **Lemma 5.1**, left multiplication by a letter of `R_l` on an element that is not
  `l`-pure.
-/
import KappaMonoid.Bergman.Core.Support

universe u

set_option linter.unusedSectionVars false

namespace Bergman.Core

open Module

variable {k : Type u} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  {σ : ∀ l, (ι → k) →ₐ[k] R l} [Fact (∀ l, Function.Injective (σ l))]
  {C : Type u} [Ring C] [Algebra k C] {σC : (ι → k) →ₐ[k] C} {inc : ∀ l, R l →ₐ[k] C}
  [Fact (IsCoprod k σ C σC inc)]
  {N : Option Λ → Type u} [∀ μ, AddCommGroup (N μ)] [∀ μ, Module (Rμ k ι R μ) (N μ)]
  [∀ μ, Module k (N μ)] [∀ μ, IsScalarTower k (Rμ k ι R μ) (N μ)] {B : HomBases σ N}

/-- `y` is `l`-pure: nonzero, with all terms of top degree on side `l`. -/
def IsPureS (l : Λ) (y : Std σC inc B) : Prop :=
  y ≠ 0 ∧ ∀ w ∈ y.supp, w.deg = y.deg → w.side = some l

/-- Bergman's `μ`-purity. -/
def IsPure : Option Λ → Std σC inc B → Prop
  | some l, y => IsPureS l y
  | none, y => ∀ l, ¬ IsPureS l y

/-- `y` is not `μ`-pure and `u` is its `μ`-leading term. -/
def IsLead : Option Λ → Std σC inc B → Mono σ B.S → Prop
  | some l, y, u => u ∈ y.supp ∧ u.deg = y.deg ∧ u.side ≠ some l ∧
      ∀ w ∈ y.supp, w.deg = y.deg → w.side ≠ some l → w ≤ u
  | none, y, u => (∃ l, IsPureS l y) ∧ u ∈ y.supp ∧ ∀ w ∈ y.supp, w ≤ u

/-- **Definition 5.2** (well-positioned families). -/
structure WP (L : Option Λ → Set (Std σC inc B)) : Prop where
  pure_some : ∀ l, ∀ y ∈ L (some l), y ≠ 0 → IsPureS l y
  pure_none : ∀ y ∈ L none, IsPure none y
  nolead : ∀ μ₁ μ₂, ∀ y ∈ L μ₁, ∀ x ∈ L μ₂, ∀ (a : C) (u : Mono σ B.S),
    u ∈ msupp σC inc B μ₁ y → IsLead μ₁ (a • x) u → μ₁ = μ₂ ∧ (a • x).deg ≤ x.deg

section Lead

theorem IsLead.mem_supp {μ : Option Λ} {y : Std σC inc B} {u : Mono σ B.S} (h : IsLead μ y u) :
    u ∈ y.supp := by
  cases μ with
  | none => exact h.2.1
  | some l => exact h.1

theorem IsLead.ne_zero {μ : Option Λ} {y : Std σC inc B} {u : Mono σ B.S} (h : IsLead μ y u) :
    y ≠ 0 := by
  rintro rfl
  have := h.mem_supp
  rw [Std.supp_eq_empty.2 rfl] at this
  exact absurd this (Finset.notMem_empty _)

theorem IsLead.deg {μ : Option Λ} {y : Std σC inc B} {u : Mono σ B.S} (h : IsLead μ y u) :
    u.deg = y.deg := by
  cases μ with
  | some l => exact h.2.1
  | none =>
    obtain ⟨w, hw, hwd⟩ := Std.exists_mem_supp h.ne_zero
    exact le_antisymm (Std.deg_le h.2.1) (hwd ▸ Mono.deg_le_of_le (h.2.2 w hw))

theorem IsLead.side_ne {μ : Option Λ} {y : Std σC inc B} {u : Mono σ B.S} (h : IsLead μ y u) :
    u.side ≠ μ := by
  cases μ with
  | some l => exact h.2.2.1
  | none =>
    obtain ⟨l, -, hl⟩ := h.1
    rw [hl u h.mem_supp h.deg]
    exact Option.some_ne_none l

theorem IsLead.not_pure {μ : Option Λ} {y : Std σC inc B} {u : Mono σ B.S} (h : IsLead μ y u) :
    ¬ IsPure μ y := by
  cases μ with
  | some l => exact fun hp => h.2.2.1 (hp.2 u h.1 h.2.1)
  | none => exact fun hp => by obtain ⟨l, hl⟩ := h.1; exact hp l hl

theorem exists_lead {μ : Option Λ} {y : Std σC inc B} (hy : y ≠ 0) (hp : ¬ IsPure μ y) :
    ∃ u, IsLead μ y u := by
  classical
  cases μ with
  | none =>
    have hne : y.supp.Nonempty := Finset.nonempty_iff_ne_empty.2 (mt Std.supp_eq_empty.1 hy)
    refine ⟨y.supp.max' hne, ?_, Finset.max'_mem _ _, fun w hw => Finset.le_max' _ _ hw⟩
    simpa [IsPure] using hp
  | some l =>
    set s := y.supp.filter fun w => w.deg = y.deg ∧ w.side ≠ some l
    have hne : s.Nonempty := by
      by_contra h
      apply hp
      refine ⟨hy, fun w hw hd => ?_⟩
      by_contra hs
      exact h ⟨w, Finset.mem_filter.2 ⟨hw, hd, hs⟩⟩
    have hm := Finset.mem_filter.1 (s.max'_mem hne)
    exact ⟨s.max' hne, hm.1, hm.2.1, hm.2.2, fun w hw hd hs =>
      s.le_max' w (Finset.mem_filter.2 ⟨hw, hd, hs⟩)⟩

theorem IsLead.unique {μ : Option Λ} {y : Std σC inc B} {u u' : Mono σ B.S} (h : IsLead μ y u)
    (h' : IsLead μ y u') : u = u' := by
  cases μ with
  | none => exact le_antisymm (h'.2.2 u h.2.1) (h.2.2 u' h'.2.1)
  | some l => exact le_antisymm (h'.2.2.2 u h.1 h.2.1 h.2.2.1) (h.2.2.2 u' h'.1 h'.2.1 h'.2.2.1)

theorem IsLead.mem_msupp {μ : Option Λ} {y : Std σC inc B} {u : Mono σ B.S} (h : IsLead μ y u) :
    u ∈ msupp σC inc B μ y := mem_msupp_of_mem_supp h.mem_supp h.side_ne

/-- Everything in the `μ`-support is at most the `μ`-leading term. -/
theorem IsLead.le_of_mem_msupp {μ : Option Λ} {y : Std σC inc B} {u v : Mono σ B.S}
    (h : IsLead μ y u) (hv : v ∈ msupp σC inc B μ y) : v ≤ u := by
  cases μ with
  | none => exact h.2.2 v hv
  | some l =>
    obtain ⟨hvs, w, hw, hs⟩ := mem_msupp_some.1 hv
    have hd := deg_of_strip hs
    have hwy := Std.deg_le hw
    by_cases hwd : w.deg = y.deg
    · by_cases hws : w.side = some l
      · -- `v` is the tail of `w`
        refine le_of_lt (Mono.lt_of_deg_lt ?_)
        have hne : w ≠ v := fun he => hvs (he ▸ hws)
        have : v.deg < w.deg := lt_of_le_of_ne hd.1 fun he => hne (hd.2 he.symm)
        rw [h.2.1]; omega
      · have hwv : w = v := by
          obtain ⟨o, rfl⟩ := strip_eq_some_iff.1 hs
          rcases o with _ | ⟨i, t⟩
          · rfl
          · exact absurd rfl hws
        subst hwv
        exact h.2.2.2 w hw hwd hws
    · refine le_of_lt (Mono.lt_of_deg_lt ?_)
      rw [h.2.1]
      have := hd.1
      simp only at this
      omega

/-- The `l`-support of an `l`-pure element lies below its degree. -/
theorem IsPureS.deg_lt_of_mem_msupp {l : Λ} {y : Std σC inc B} (h : IsPureS l y) {v : Mono σ B.S}
    (hv : v ∈ msupp σC inc B (some l) y) : v.deg < y.deg := by
  obtain ⟨hvs, w, hw, hs⟩ := mem_msupp_some.1 hv
  have hd := deg_of_strip hs
  have hwy := Std.deg_le hw
  have h1 := hd.1
  simp only at h1
  by_cases hwd : w.deg = y.deg
  · have hne : w ≠ v := fun he => hvs (he ▸ h.2 w hw hwd)
    have : v.deg < w.deg := lt_of_le_of_ne h1 fun he => hne (hd.2 he.symm)
    omega
  · omega

/-- The coordinate at the `μ`-leading term. -/
theorem IsLead.coord {μ : Option Λ} {y : Std σC inc B} {u : Mono σ B.S} (h : IsLead μ y u) :
    (coord σC inc B μ ⟨u, h.side_ne⟩ y : Rμ k ι R μ) = Std.coeff σC inc B y u • eμ σ μ u.left :=
  coord_of_deg (le_of_eq h.deg.symm)

end Lead

/-! ## Lemma 5.1 -/

theorem Std.mem_supp_sum_smul {s : Finset (Mono σ B.S)} {c : Mono σ B.S → k}
    {z : Mono σ B.S → Std σC inc B} {w' : Mono σ B.S} (h : w' ∈ (∑ w ∈ s, c w • z w).supp) :
    ∃ w ∈ s, w' ∈ (z w).supp := by
  obtain ⟨w, hw, hw'⟩ := Finset.mem_biUnion.1 (Std.supp_sum _ _ h)
  exact ⟨w, hw, Std.supp_smul _ _ hw'⟩

/-- **Lemma 5.1**: if `y` is not `l`-pure with `l`-leading term `u`, and `t` is a letter of
`R_l` which can be put in front of `u`, then `t y` is `l`-pure of degree `deg y + 1`, with leading
term `t u`, having the coefficient that `u` has in `y`. -/
theorem lead_letter {y : Std σC inc B} {u : Mono σ B.S} (t : Letter σ)
    (hu : IsLead (some t.side) y u) (h₁ : t.right = u.left) (h₂ : some t.side ≠ u.side) :
    IsPureS t.side (inc t.side t.val • y) ∧
      (∀ w ∈ (inc t.side t.val • y).supp, w ≤ Mono.cons t u h₁ h₂) ∧
      Std.coeff σC inc B (inc t.side t.val • y) (Mono.cons t u h₁ h₂) = Std.coeff σC inc B y u ∧
      (inc t.side t.val • y).deg = y.deg + 1 := by
  classical
  set v := Mono.cons t u h₁ h₂
  set ty := inc t.side t.val • y
  have hty : ty = ∑ w ∈ y.supp, Std.coeff σC inc B y w • (inc t.side t.val • Std.mono σC inc B w) := by
    conv_lhs => rw [show ty = inc t.side t.val • y from rfl, Std.eq_sum_mono y]
    rw [Finset.smul_sum]
    simp only [smul_comm (inc t.side t.val) (Std.coeff σC inc B y _)]
  have hvd : v.deg = y.deg + 1 := by rw [Mono.deg_cons, hu.2.1]
  -- the terms of `t w`
  have hterm : ∀ w ∈ y.supp, ∀ w' ∈ (inc t.side t.val • Std.mono σC inc B w).supp,
      w' < v ∨ (w' = v ∧ w = u) ∨ (w'.deg = y.deg + 1 → w'.side = some t.side) ∧ w' ≤ v := by
    intro w hw w' hw'
    have hdw := Std.deg_le hw
    have hsm := deg_of_mem_supp_smul (μ := some t.side) (tval σ t.2.2.2) hw'
    by_cases hs : w.side = some t.side
    · left
      exact Mono.lt_of_deg_lt (by have := (hsm.2 hs).1; omega)
    · by_cases hr : t.right = w.left
      · have hc : inc t.side t.val • Std.mono σC inc B w =
            Std.mono σC inc B (Mono.cons t w hr (fun h => hs h.symm)) :=
          (Std.mono_cons σC inc B t w hr _).symm
        rw [hc, Std.supp_mono, Finset.mem_singleton] at hw'
        subst hw'
        by_cases hwd : w.deg = y.deg
        · rcases (hu.2.2.2 w hw hwd hs).lt_or_eq with hlt | heq
          · left; exact Mono.cons_lt_cons (by rw [hwd, hu.2.1]) hlt _ _ _ _ _ _
          · subst heq; right; left; exact ⟨rfl, rfl⟩
        · left
          exact Mono.lt_of_deg_lt (by rw [Mono.deg_cons, hvd]; omega)
      · rw [letter_smul_mono_of_ne t w hr, Std.supp_eq_empty.2 rfl] at hw'
        exact absurd hw' (Finset.notMem_empty _)
  have hle : ∀ w' ∈ ty.supp, w' ≤ v := by
    intro w' hw'
    rw [hty] at hw'
    obtain ⟨w, hw, hw'⟩ := Std.mem_supp_sum_smul hw'
    rcases hterm w hw w' hw' with h | h | h
    · exact h.le
    · exact h.1.le
    · exact h.2
  -- the coefficient of `v`
  have hcoeff : Std.coeff σC inc B ty v = Std.coeff σC inc B y u := by
    rw [hty, map_sum, Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single u]
    · rw [map_smul, Finsupp.smul_apply, show inc t.side t.val • Std.mono σC inc B u =
        Std.mono σC inc B v from (Std.mono_cons σC inc B t u h₁ h₂).symm, Std.coeff_mono,
        if_pos rfl, smul_eq_mul, mul_one]
    · intro w hw hwu
      rw [map_smul, Finsupp.smul_apply]
      by_contra hne
      have hv : v ∈ (inc t.side t.val • Std.mono σC inc B w).supp := by
        rw [Std.mem_supp]; intro h0; exact hne (by rw [h0, smul_zero])
      rcases hterm w hw v hv with h | h | h
      · exact lt_irrefl _ h
      · exact hwu h.2
      · -- `v = t w` forces `w = u`
        by_cases hs : w.side = some t.side
        · have := (deg_of_mem_supp_smul (μ := some t.side) (tval σ t.2.2.2) hv).2 hs
          have hdw := Std.deg_le hw
          omega
        · have hr : t.right = w.left := by
            by_contra hr
            rw [letter_smul_mono_of_ne t w hr, Std.supp_eq_empty.2 rfl] at hv
            exact absurd hv (Finset.notMem_empty _)
          rw [(Std.mono_cons σC inc B t w hr (fun h => hs h.symm)).symm, Std.supp_mono,
            Finset.mem_singleton] at hv
          exact hwu (Mono.cons_injective hv).2.symm
    · intro hu'; exact absurd hu.1 hu'
  have hvmem : v ∈ ty.supp := by
    rw [Std.mem_supp, hcoeff]; exact Std.mem_supp.1 hu.1
  have hdeg : ty.deg = y.deg + 1 := by
    rw [← hvd]
    exact le_antisymm (Finset.sup_le fun w hw => Mono.deg_le_of_le (hle w hw)) (Std.deg_le hvmem)
  have hne0 : ty ≠ 0 := by
    intro h0
    rw [h0, Std.supp_eq_empty.2 rfl] at hvmem
    exact absurd hvmem (Finset.notMem_empty _)
  refine ⟨⟨hne0, fun w' hw' hd => ?_⟩, hle, hcoeff, hdeg⟩
  rw [hty] at hw'
  obtain ⟨w, hw, hw''⟩ := Std.mem_supp_sum_smul hw'
  rw [hdeg] at hd
  rcases hterm w hw w' hw'' with h | h | h
  · -- a term below `v` of the same degree
    have hsm := deg_of_mem_supp_smul (μ := some t.side) (tval σ t.2.2.2) hw''
    have hdw := Std.deg_le hw
    by_cases hs : w.side = some t.side
    · have := (hsm.2 hs).1; omega
    · have := (hsm.1 hs).1
      exact (hsm.1 hs).2.1 (by omega)
  · rw [h.1]; rfl
  · exact h.1 hd

end Bergman.Core
