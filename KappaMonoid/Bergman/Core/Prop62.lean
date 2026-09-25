/-
**Proposition 6.2**: adjusting a presentation until the images are well-positioned.

Given a standard presentation `p` of `M` with finitely generated components and a `C`-linear map
`f : M → Std`, finitely many basic transfers and transvections turn `p` into a presentation whose
images `f (A μ)` are well-positioned (Definition 5.2).

The **index** of a presentation (Bergman §6) is the finitely supported function on the interlaced
copies `U₀ ⊔ U_Λ` of the monomials: at `u₀` it is `1` if `u` is in the `0`-support of `f(A none)`,
at `u_Λ` the number of `l` with `u` in the `l`-support of `f(A l)`.  The copies are interlaced by
degree (`(deg, copy, u)`, lexicographically) and functions are compared lexicographically *from
the top*: this is `Lex (Keyᵒᵈ →₀ ℕ)`, which is well-founded.  Each move lowers the index.
-/
import KappaMonoid.Bergman.Core.Pres
import KappaMonoid.Bergman.Core.Pure

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

/-! ## The index -/

variable (B) in
/-- The interlaced copies `U₀ ⊔ U_Λ`: degree, then copy (`false` for `U₀`), then the monomial. -/
abbrev Key := ℕ ×ₗ (Bool ×ₗ Mono σ B.S)

/-- The key of `u` in the copy of `μ`. -/
def key (μ : Option Λ) (u : Mono σ B.S) : Key B := toLex (u.deg, toLex (μ.isSome, u))

/-- The count of an index at a key. -/
noncomputable def cnt (S : Option Λ → Finset (Mono σ B.S)) (x : Key B) : ℕ :=
  if (ofLex x).1 = (ofLex (ofLex x).2).2.deg then
    (if (ofLex (ofLex x).2).1 then
      (Finset.univ.filter fun l : Λ => (ofLex (ofLex x).2).2 ∈ S (some l)).card
    else if (ofLex (ofLex x).2).2 ∈ S none then 1 else 0)
  else 0

/-- The index of a family of finite sets of monomials. -/
noncomputable def idx (S : Option Λ → Finset (Mono σ B.S)) : Lex ((Key B)ᵒᵈ →₀ ℕ) :=
  toLex (Finsupp.onFinset ((Finset.univ.biUnion fun μ => (S μ).image (key μ)).image OrderDual.toDual)
    (fun x => cnt S (OrderDual.ofDual x)) (by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
      refine ⟨OrderDual.ofDual x, ?_, rfl⟩
      unfold cnt at hx
      split_ifs at hx with h1 h2 h3
      · obtain ⟨l, hl⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hx)
        refine ⟨some l, (ofLex (ofLex (OrderDual.ofDual x)).2).2, (Finset.mem_filter.1 hl).2, ?_⟩
        simp only [key, Option.isSome_some]
        rw [← h1, ← h2]; rfl
      · refine ⟨none, (ofLex (ofLex (OrderDual.ofDual x)).2).2, h3, ?_⟩
        simp only [key, Option.isSome_none]
        rw [← h1, Bool.not_eq_true] at *
        rw [← h2]; rfl
      · exact absurd rfl hx
      · exact absurd rfl hx))

theorem idx_apply (S : Option Λ → Finset (Mono σ B.S)) (x : Key B) :
    ofLex (idx S) (OrderDual.toDual x) = cnt S x := rfl

theorem cnt_key (S : Option Λ → Finset (Mono σ B.S)) (μ : Option Λ) (u : Mono σ B.S) :
    cnt S (key μ u) = match μ with
      | none => if u ∈ S none then 1 else 0
      | some _ => (Finset.univ.filter fun l : Λ => u ∈ S (some l)).card := by
  cases μ <;> simp only [cnt, key, ofLex_toLex, Option.isSome_none, Option.isSome_some,
    if_true, Bool.false_eq_true, if_false] <;> congr

theorem eq_key_of_cnt_ne_zero {S : Option Λ → Finset (Mono σ B.S)} {x : Key B}
    (h : cnt S x ≠ 0) : ∃ μ : Option Λ, ∃ v, x = key μ v := by
  unfold cnt at h
  split_ifs at h with h1 h2
  · obtain ⟨l, -⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h)
    refine ⟨some l, (ofLex (ofLex x).2).2, ?_⟩
    simp only [key, Option.isSome_some]
    rw [← h1, ← h2]; rfl
  · refine ⟨none, (ofLex (ofLex x).2).2, ?_⟩
    simp only [key, Option.isSome_none]
    rw [Bool.not_eq_true] at h2
    rw [← h1, ← h2]; rfl
  · exact absurd rfl h
  · exact absurd rfl h

theorem key_lt_key_iff {μ ν : Option Λ} {u v : Mono σ B.S} :
    key μ u < key ν v ↔ u.deg < v.deg ∨ u.deg = v.deg ∧
      (μ.isSome < ν.isSome ∨ μ.isSome = ν.isSome ∧ u < v) := by
  simp only [key, Prod.Lex.toLex_lt_toLex]

/-- **The decrease criterion.** If every `S' μ` lies in `S μ ∪ T μ`, where all monomials of the
`T μ` have keys below the key of `u` in the copy of `μ₀`, and `u` leaves `S μ₀`, the index drops. -/
theorem idx_lt {S S' T : Option Λ → Finset (Mono σ B.S)} (μ₀ : Option Λ) (u : Mono σ B.S)
    (hS : ∀ μ, S' μ ⊆ S μ ∪ T μ) (hT : ∀ μ, ∀ v ∈ T μ, key μ v < key μ₀ u) (hu : u ∈ S μ₀)
    (hu' : u ∉ S' μ₀) : idx S' < idx S := by
  classical
  -- counts above the key of `u` do not increase
  have hcnt : ∀ x, key μ₀ u ≤ x → cnt S' x ≤ cnt S x := by
    intro x hx
    by_cases h0 : cnt S' x = 0
    · rw [h0]; exact Nat.zero_le _
    obtain ⟨ν, v, rfl⟩ := eq_key_of_cnt_ne_zero h0
    have hnT : ∀ μ, ν.isSome = μ.isSome → v ∉ T μ := fun μ hμ hv => by
      have := hT μ v hv
      have h' : key μ v = key ν v := by simp [key, hμ]
      exact absurd (h' ▸ this) (not_lt.2 hx)
    rw [cnt_key, cnt_key]
    cases ν with
    | none =>
      split_ifs with h1 h2
      · exact le_rfl
      · rcases Finset.mem_union.1 (hS none h1) with h | h
        · exact absurd h h2
        · exact absurd h (hnT none rfl)
      · exact Nat.zero_le _
      · exact le_rfl
    | some l =>
      refine Finset.card_le_card fun l' hl' => ?_
      rw [Finset.mem_filter] at hl' ⊢
      refine ⟨hl'.1, ?_⟩
      rcases Finset.mem_union.1 (hS (some l') hl'.2) with h | h
      · exact h
      · exact absurd h (hnT (some l') rfl)
  -- the count at the key of `u` drops
  have hdrop : cnt S' (key μ₀ u) < cnt S (key μ₀ u) := by
    rw [cnt_key, cnt_key]
    cases μ₀ with
    | none => simp [hu, hu']
    | some l =>
      refine Finset.card_lt_card ⟨fun l' hl' => ?_, fun h => ?_⟩
      · rw [Finset.mem_filter] at hl' ⊢
        refine ⟨hl'.1, ?_⟩
        rcases Finset.mem_union.1 (hS (some l') hl'.2) with h | h
        · exact h
        · exact absurd (hT (some l') u h) (by simp [key])
      · exact hu' (Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨Finset.mem_univ l, hu⟩))).2
  -- the lexicographic comparison from the top
  set D := (((ofLex (idx S')).support ∪ (ofLex (idx S)).support).filter fun x =>
    OrderDual.ofDual x ≥ key μ₀ u ∧ ofLex (idx S') x ≠ ofLex (idx S) x)
  have hDne : D.Nonempty := by
    refine ⟨OrderDual.toDual (key μ₀ u), Finset.mem_filter.2 ⟨?_, le_rfl, ?_⟩⟩
    · rw [Finset.mem_union]; right
      rw [Finsupp.mem_support_iff, idx_apply]; omega
    · rw [idx_apply, idx_apply]; omega
  -- the largest key (in `Key`) where they differ: the smallest in the dual order
  set i := D.min' hDne
  have hi := Finset.mem_filter.1 (D.min'_mem hDne)
  refine ⟨i, fun x hx => ?_, ?_⟩
  · by_contra hne
    have hxD : x ∈ D := by
      refine Finset.mem_filter.2 ⟨?_, ?_, hne⟩
      · by_contra hxs
        simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hxs
        exact hne (hxs.1.trans hxs.2.symm)
      · exact le_trans hi.2.1 (le_of_lt hx)
    exact absurd (D.min'_le x hxD) (not_le.2 hx)
  · have h1 := hcnt (OrderDual.ofDual i) hi.2.1
    rw [← idx_apply, ← idx_apply] at h1
    exact lt_of_le_of_ne h1 hi.2.2

instance : WellFoundedLT (Lex ((Key B)ᵒᵈ →₀ ℕ)) := Finsupp.Lex.wellFoundedLT

/-! ## Supports of the images of a presentation -/

variable {M : Type u} [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]

/-- The images `f (A μ)`. -/
def img (f : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) (μ : Option Λ) :
    Set (Std σC inc B) := Set.range fun a => f (p.j μ a)

/-- The `μ`-support of `f (A μ)`. -/
def ssupp (f : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) (μ : Option Λ) :
    Set (Mono σ B.S) := {u | ∃ a, u ∈ msupp σC inc B μ (f (p.j μ a))}

theorem f_j_smul (f : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) (μ : Option Λ)
    (r : Rμ k ι R μ) (a : p.A μ) : f (p.j μ (r • a)) = incμ σC inc μ r • f (p.j μ a) := by
  rw [p.j_smul, map_smul]

theorem ssupp_finite (f : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) (hp : p.FG)
    (μ : Option Λ) : (ssupp f p μ).Finite := by
  classical
  obtain ⟨s, hs⟩ := (hp μ).fg_top
  refine ((s.finite_toSet.biUnion fun g _ =>
    (msupp σC inc B μ (f (p.j μ g))).finite_toSet)).subset ?_
  rintro u ⟨a, ha⟩
  have key : ∀ a ∈ Submodule.span (Rμ k ι R μ) (s : Set (p.A μ)),
      (msupp σC inc B μ (f (p.j μ a)) : Set (Mono σ B.S)) ⊆
        ⋃ g ∈ (s : Set (p.A μ)), (msupp σC inc B μ (f (p.j μ g)) : Set (Mono σ B.S)) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem g hg => exact Set.subset_biUnion_of_mem (u := fun g => (msupp σC inc B μ (f (p.j μ g)) :
        Set (Mono σ B.S))) hg
    | zero => simp [msupp_zero]
    | add a b _ _ ha hb =>
      intro v hv
      rw [map_add, map_add] at hv
      rcases Finset.mem_union.1 (msupp_add μ _ _ hv) with h | h
      · exact ha h
      · exact hb h
    | smul r a _ ha =>
      intro v hv
      rw [f_j_smul] at hv
      exact ha (msupp_incμ_smul μ r _ hv)
  exact key a (hs ▸ Submodule.mem_top) ha

/-- The finite `μ`-supports. -/
noncomputable def sfin (f : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) (hp : p.FG)
    (μ : Option Λ) : Finset (Mono σ B.S) := (ssupp_finite f p hp μ).toFinset

theorem mem_sfin {f : M →ₗ[C] Std σC inc B} {p : StdPres σ σC inc M} {hp : p.FG} {μ : Option Λ}
    {u : Mono σ B.S} : u ∈ sfin f p hp μ ↔ u ∈ ssupp f p μ := Set.Finite.mem_toFinset _

/-- The support can only shrink when the image does. -/
theorem ssupp_mono {f : M →ₗ[C] Std σC inc B} {p p' : StdPres σ σC inc M} {μ : Option Λ}
    (h : Set.range (p'.j μ) ⊆ Set.range (p.j μ)) : ssupp f p' μ ⊆ ssupp f p μ := by
  rintro u ⟨a, ha⟩
  obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
  exact ⟨b, hb ▸ ha⟩

/-- The three ways a family can fail to be well-positioned. -/
theorem not_wp {L : Option Λ → Set (Std σC inc B)} (h : ¬ WP L) :
    (∃ l, ∃ y ∈ L (some l), y ≠ 0 ∧ ¬ IsPureS l y) ∨ (∃ y ∈ L none, ¬ IsPure none y) ∨
      ∃ μ₁ μ₂, ∃ y ∈ L μ₁, ∃ x ∈ L μ₂, ∃ (a : C) (u : Mono σ B.S),
        u ∈ msupp σC inc B μ₁ y ∧ IsLead μ₁ (a • x) u ∧ ¬ (μ₁ = μ₂ ∧ (a • x).deg ≤ x.deg) := by
  by_contra hc
  simp only [not_or, not_exists, not_and, not_not] at hc
  exact h ⟨fun l y hy h0 => hc.1 l y hy h0, fun y hy => hc.2.1 y hy,
    fun μ₁ μ₂ y hy x hx a u hu hl => by
      have := hc.2.2 μ₁ μ₂ y hy x hx a u hu hl
      tauto⟩

/-- An element of the left ideal `R e_j` is fixed by `e_j` on the right. -/
theorem mul_eμ_of_mem {μ : Option Λ} {j : ι} {v : Rμ k ι R μ}
    (hv : v ∈ Submodule.span (Rμ k ι R μ) {eμ σ μ j}) : v * eμ σ μ j = v := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [smul_eq_mul, mul_assoc, eμ_mul_eμ, if_pos rfl]

/-- The coordinate at `u`, divided by a scalar, as an `R_μ`-linear map on a component. -/
noncomputable def coordOn (f : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) (μ : Option Λ)
    (u : NotSide B μ) (c : k) :
    p.A μ →ₗ[Rμ k ι R μ] Submodule.span (Rμ k ι R μ) {eμ σ μ u.1.left} where
  toFun a := c • coord σC inc B μ u (f (p.j μ a))
  map_add' a b := by rw [map_add, map_add, map_add, smul_add]
  map_smul' r a := by
    rw [f_j_smul, coord_smul, RingHom.id_apply, smul_comm]

theorem coordOn_apply (f : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) (μ : Option Λ)
    (u : NotSide B μ) (c : k) (a : p.A μ) :
    coordOn f p μ u c a = c • coord σC inc B μ u (f (p.j μ a)) := rfl

end Bergman.Core
