/-
**Words of letters acting on leading terms** (Bergman §8, the computation behind Lemma 8.1).

* `ChainAt i s ts`: the letters `ts` can be put, in order, in front of a monomial with left index
  `i` and side `s`; `Mono.pre ts w` is the resulting monomial, and `Std.mono_pre` says it is the
  image of `w` under the product `wordAct inc ts` of the letters.
* `basisOrder o`: the orders used to choose the bases of Bergman §8: for `o = none` the order of
  monomials, for `o = some l` the order "degree, then not on side `l`, then the order of
  monomials", whose greatest term in an element that is not `l`-pure is its `l`-leading term
  (`isLead_of_top`).
* `lead_word`: **Lemma 5.1, iterated**: a word of letters applied to an element with an
  `l`-leading term `v` (`l` the side of the letter applied first) has greatest term `ts v`, with
  the coefficient `v` has.
-/
import KappaMonoid.Bergman.Core.Echelon

universe u

set_option linter.unusedSectionVars false

namespace Bergman.Core

open Module

variable {k : Type u} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  {σ : ∀ l, (ι → k) →ₐ[k] R l} [Fact (∀ l, Function.Injective (σ l))]

/-! ## Chains of letters -/

/-- The left index of `ts · w`, `w` of left index `i`. -/
def leftAt (i : ι) : List (Letter σ) → ι
  | [] => i
  | t :: _ => t.left

/-- The side of `ts · w`, `w` of side `s`. -/
def sideAt (s : Option Λ) : List (Letter σ) → Option Λ
  | [] => s
  | t :: _ => some t.side

/-- The letters `ts` can be put in front of a monomial of left index `i` and side `s`. -/
def ChainAt (i : ι) (s : Option Λ) : List (Letter σ) → Prop
  | [] => True
  | t :: ts => ChainAt i s ts ∧ t.right = leftAt i ts ∧ some t.side ≠ sideAt s ts

/-- The side of the letter applied first (the last one of the list). -/
def firstSide (ts : List (Letter σ)) : Option Λ := ts.getLast?.map Letter.side

theorem wordLeft_eq {S : Option Λ → ι → Type u} (b : Base S) (ws : List (Letter σ)) :
    wordLeft b ws = leftAt b.idx ws := by cases ws <;> rfl

theorem wordSide_eq {S : Option Λ → ι → Type u} (b : Base S) (ws : List (Letter σ)) :
    wordSide b ws = sideAt b.side ws := by cases ws <;> rfl

theorem chain_iff {S : Option Λ → ι → Type u} (b : Base S) (ws : List (Letter σ)) :
    Chain b ws ↔ ChainAt b.idx b.side ws := by
  induction ws with
  | nil => exact Iff.rfl
  | cons t ts ih =>
    show (Chain b ts ∧ _ ∧ _) ↔ (ChainAt _ _ ts ∧ _ ∧ _)
    rw [ih, wordLeft_eq, wordSide_eq]

theorem leftAt_append (i : ι) (ts ws : List (Letter σ)) :
    leftAt i (ts ++ ws) = leftAt (leftAt i ws) ts := by cases ts <;> rfl

theorem sideAt_append (s : Option Λ) (ts ws : List (Letter σ)) :
    sideAt s (ts ++ ws) = sideAt (sideAt s ws) ts := by cases ts <;> rfl

theorem chainAt_append (i : ι) (s : Option Λ) (ts ws : List (Letter σ)) :
    ChainAt i s (ts ++ ws) ↔ ChainAt (leftAt i ws) (sideAt s ws) ts ∧ ChainAt i s ws := by
  induction ts with
  | nil => simp only [List.nil_append, ChainAt, true_and]
  | cons t ts ih =>
    rw [List.cons_append]
    simp only [ChainAt]
    rw [ih, leftAt_append, sideAt_append]
    tauto

theorem ChainAt.mono_side {i : ι} {s s' : Option Λ} : ∀ {ts : List (Letter σ)}, ChainAt i s ts →
    (∀ t ∈ ts.getLast?, some t.side ≠ s') → ChainAt i s' ts
  | [], _, _ => trivial
  | [t], h, h' => ⟨trivial, h.2.1, h' t (by simp)⟩
  | t :: t' :: ts, h, h' =>
    ⟨ChainAt.mono_side h.1 (fun x hx => h' x (by rwa [List.getLast?_cons_cons])), h.2.1, h.2.2⟩

theorem ChainAt.last_ne {i : ι} {s : Option Λ} : ∀ {ts : List (Letter σ)}, ChainAt i s ts →
    ∀ t ∈ ts.getLast?, some t.side ≠ s
  | [], _, t, ht => by simp at ht
  | [t], h, t', ht => by
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at ht
    subst ht; exact h.2.2
  | t :: t' :: ts, h, x, hx => ChainAt.last_ne h.1 x (by rwa [List.getLast?_cons_cons] at hx)

theorem firstSide_cons_cons (t t' : Letter σ) (ts : List (Letter σ)) :
    firstSide (t :: t' :: ts) = firstSide (t' :: ts) := by
  simp [firstSide, List.getLast?_cons_cons]

theorem firstSide_singleton (t : Letter σ) : firstSide [t] = some t.side := by
  simp [firstSide]

theorem firstSide_append (ts ms : List (Letter σ)) (h : ms ≠ []) :
    firstSide (ts ++ ms) = firstSide ms := by
  simp [firstSide, List.getLast?_append_of_ne_nil _ h]

theorem exists_of_firstSide {ts : List (Letter σ)} {l : Λ} (h : firstSide ts = some l) :
    ∃ t ∈ ts.getLast?, t.side = l := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨t, ht, rfl⟩

/-! ## Prefixing a word -/

variable {S : Option Λ → ι → Type u}

theorem chain_pre (ts : List (Letter σ)) (w : Mono σ S) (h : ChainAt w.left w.side ts) :
    Chain w.base (ts ++ w.word) := by
  rw [chain_iff, chainAt_append]
  refine ⟨?_, (chain_iff _ _).1 w.chain⟩
  rw [← wordLeft_eq, ← wordSide_eq]; exact h

/-- The monomial `ts w`. -/
def Mono.pre (ts : List (Letter σ)) (w : Mono σ S) (h : ChainAt w.left w.side ts) : Mono σ S :=
  ⟨w.base, ts ++ w.word, chain_pre ts w h⟩

@[simp] theorem Mono.pre_nil (w : Mono σ S) (h) : Mono.pre [] w h = w := Mono.ext rfl rfl

theorem Mono.left_pre (ts : List (Letter σ)) (w : Mono σ S) (h) :
    (Mono.pre ts w h).left = leftAt w.left ts := by
  show wordLeft w.base (ts ++ w.word) = _
  rw [wordLeft_eq, leftAt_append, ← wordLeft_eq]; rfl

theorem Mono.side_pre (ts : List (Letter σ)) (w : Mono σ S) (h) :
    (Mono.pre ts w h).side = sideAt w.side ts := by
  show wordSide w.base (ts ++ w.word) = _
  rw [wordSide_eq, sideAt_append, ← wordSide_eq]; rfl

theorem Mono.deg_pre (ts : List (Letter σ)) (w : Mono σ S) (h) :
    (Mono.pre ts w h).deg = ts.length + w.deg := List.length_append

theorem Mono.pre_cons (t : Letter σ) (ts : List (Letter σ)) (w : Mono σ S)
    (h : ChainAt w.left w.side (t :: ts)) :
    Mono.pre (t :: ts) w h = Mono.cons t (Mono.pre ts w h.1)
      (h.2.1.trans (Mono.left_pre ts w h.1).symm)
      (fun e => h.2.2 (e.trans (Mono.side_pre ts w h.1))) := Mono.ext rfl rfl

theorem Mono.pre_singleton (t : Letter σ) (w : Mono σ S) (h : ChainAt w.left w.side [t]) :
    Mono.pre [t] w h = Mono.cons t w h.2.1 h.2.2 := Mono.ext rfl rfl

/-- A monomial is a word applied to its base element. -/
theorem Mono.eq_pre_ofBase (w : Mono σ S) :
    w = Mono.pre w.word (Mono.ofBase w.base) ((chain_iff _ _).1 w.chain) :=
  Mono.ext rfl (List.append_nil _).symm

/-! ## Words acting on the standard module -/

variable {C : Type u} [Ring C] [Algebra k C]

/-- The product `tₙ ⋯ t₁ ∈ C` of a word of letters. -/
noncomputable def wordAct (inc : ∀ l, R l →ₐ[k] C) (ts : List (Letter σ)) : C :=
  (ts.map fun t => inc t.side t.val).prod

variable {σC : (ι → k) →ₐ[k] C} {inc : ∀ l, R l →ₐ[k] C} [Fact (IsCoprod k σ C σC inc)]
  {N : Option Λ → Type u} [∀ μ, AddCommGroup (N μ)] [∀ μ, Module (Rμ k ι R μ) (N μ)]
  [∀ μ, Module k (N μ)] [∀ μ, IsScalarTower k (Rμ k ι R μ) (N μ)] {B : HomBases σ N}

@[simp] theorem wordAct_nil : wordAct inc ([] : List (Letter σ)) = 1 := by simp [wordAct]

theorem wordAct_cons (t : Letter σ) (ts : List (Letter σ)) :
    wordAct inc (t :: ts) = inc t.side t.val * wordAct inc ts := by simp [wordAct]

theorem Std.mono_pre (ts : List (Letter σ)) (w : Mono σ B.S) (h) :
    Std.mono σC inc B (Mono.pre ts w h) = wordAct inc ts • Std.mono σC inc B w := by
  induction ts with
  | nil => rw [Mono.pre_nil, wordAct_nil, one_smul]
  | cons t ts ih => rw [Mono.pre_cons, Std.mono_cons, ih h.1, wordAct_cons, mul_smul]

/-- Stripping the letter in front. -/
theorem strip_cons (t : Letter σ) (w : Mono σ B.S) (h₁ h₂) :
    strip B (some t.side) (Mono.cons t w h₁ h₂) = some ⟨w, fun h => h₂ h.symm⟩ := by
  obtain ⟨l, i, j, t'⟩ := t
  change j = w.left at h₁
  subst h₁
  exact strip_join_inr (some l) ⟨w, fun h => h₂ h.symm⟩ (some ⟨i, t'⟩)

/-! ## Homogeneity -/

theorem Std.coeff_σC_smul (c : ι → k) (y : Std σC inc B) (w : Mono σ B.S) :
    Std.coeff σC inc B (σC c • y) w = c w.left * Std.coeff σC inc B y w := by
  have : (Finsupp.lapply w ∘ₗ (Std.coeff σC inc B).toLinearMap ∘ₗ smulLin (k := k) (σC c)) =
      c w.left • (Finsupp.lapply w ∘ₗ (Std.coeff σC inc B).toLinearMap) := by
    refine (Std.monoBasis σC inc B).ext fun w' => ?_
    simp only [LinearMap.comp_apply, smulLin_apply, LinearEquiv.coe_coe, Std.monoBasis_apply,
      LinearMap.smul_apply, Finsupp.lapply_apply, σC_smul_mono, map_smul,
      smul_eq_mul, Std.coeff_mono]
    split_ifs with h
    · subst h; rfl
    · simp
  exact LinearMap.congr_fun this y

theorem left_of_mem_supp_homog {j : ι} {y : Std σC inc B} (hy : σC (ee j) • y = y)
    {w : Mono σ B.S} (hw : w ∈ y.supp) : w.left = j := by
  rw [Std.mem_supp] at hw
  by_contra hne
  apply hw
  rw [← hy, Std.coeff_σC_smul]
  simp [ee, hne]

/-! ## The orders `basisOrder` -/

/-- `true` unless the monomial is on side `l` (always `true` for `o = none`). -/
def sideBit : Option Λ → Mono σ S → Bool
  | none, _ => true
  | some l, w => decide (w.side ≠ some l)

/-- The order used to choose the bases of Bergman §8. -/
noncomputable def basisOrder (o : Option Λ) (w : Mono σ S) : ℕ ×ₗ (Bool ×ₗ Mono σ S) :=
  toLex (w.deg, toLex (sideBit o w, w))

theorem basisOrder_injective (o : Option Λ) : Function.Injective (basisOrder (σ := σ) (S := S) o) :=
  fun _ _ h => congrArg (fun p => (ofLex (ofLex p).2).2) h

theorem basisOrder_le_iff {o : Option Λ} {w w' : Mono σ S} :
    basisOrder o w ≤ basisOrder o w' ↔ w.deg < w'.deg ∨ w.deg = w'.deg ∧
      (sideBit o w < sideBit o w' ∨ sideBit o w = sideBit o w' ∧ w ≤ w') := by
  rw [basisOrder, basisOrder, Prod.Lex.toLex_le_toLex, Prod.Lex.toLex_le_toLex]

theorem deg_le_of_basisOrder_le {o : Option Λ} {w w' : Mono σ S}
    (h : basisOrder o w ≤ basisOrder o w') : w.deg ≤ w'.deg := by
  rcases basisOrder_le_iff.1 h with h | h
  · exact h.le
  · exact h.1.le

theorem isTopF_iff {f : Mono σ B.S → ℕ ×ₗ (Bool ×ₗ Mono σ B.S)} {y : Std σC inc B}
    {v : Mono σ B.S} :
    IsTopF f (Std.coeff σC inc B y) v ↔ v ∈ y.supp ∧ ∀ w ∈ y.supp, f w ≤ f v := Iff.rfl

theorem IsTopF.deg_eq {o : Option Λ} {y : Std σC inc B} {v : Mono σ B.S}
    (h : IsTopF (basisOrder o) (Std.coeff σC inc B y) v) : v.deg = y.deg := by
  have hy : y ≠ 0 := by rintro rfl; exact absurd h.1 (by simp)
  obtain ⟨w, hw, hwd⟩ := Std.exists_mem_supp hy
  exact le_antisymm (Std.deg_le h.1) (hwd ▸ deg_le_of_basisOrder_le (h.2 w hw))

/-- The greatest term for `basisOrder o` is greatest for the order of monomials, when the terms of
top degree are not on side `o`. -/
theorem IsTopF.le_of_bit {o : Option Λ} {y : Std σC inc B} {v : Mono σ B.S}
    (h : IsTopF (basisOrder o) (Std.coeff σC inc B y) v)
    (hb : ∀ w ∈ y.supp, w.deg = y.deg → sideBit o w = true) : ∀ w ∈ y.supp, w ≤ v := by
  intro w hw
  rcases basisOrder_le_iff.1 (h.2 w hw) with hd | ⟨hd, hb' | ⟨-, hle⟩⟩
  · exact (Mono.lt_of_deg_lt hd).le
  · have hvd := h.deg_eq
    rw [hb v h.1 hvd, hb w hw (hd.trans hvd)] at hb'
    exact absurd hb' (lt_irrefl _)
  · exact hle

theorem IsTopF.le_none {y : Std σC inc B} {v : Mono σ B.S}
    (h : IsTopF (basisOrder none) (Std.coeff σC inc B y) v) : ∀ w ∈ y.supp, w ≤ v :=
  h.le_of_bit fun _ _ _ => rfl

/-- For an element that is not `l`-pure, the greatest term for `basisOrder (some l)` is its
`l`-leading term. -/
theorem IsTopF.isLead {l : Λ} {y : Std σC inc B} {v : Mono σ B.S}
    (h : IsTopF (basisOrder (some l)) (Std.coeff σC inc B y) v) (hp : ¬ IsPureS l y) :
    IsLead (some l) y v := by
  have hy : y ≠ 0 := by rintro rfl; exact absurd h.1 (by simp)
  have hvd := h.deg_eq
  obtain ⟨w₀, hw₀, hw₀d, hw₀s⟩ : ∃ w ∈ y.supp, w.deg = y.deg ∧ w.side ≠ some l := by
    by_contra hc
    push Not at hc
    exact hp ⟨hy, hc⟩
  have hvs : v.side ≠ some l := by
    intro hvs
    rcases basisOrder_le_iff.1 (h.2 w₀ hw₀) with hd | ⟨-, hb | ⟨hb, -⟩⟩
    · omega
    · have hv' : sideBit (some l) v = false := by simp [sideBit, hvs]
      rw [hv'] at hb
      exact absurd hb (by cases sideBit (some l) w₀ <;> decide)
    · simp [sideBit, hvs, hw₀s] at hb
  refine ⟨h.1, hvd, hvs, fun w hw hwd hws => ?_⟩
  rcases basisOrder_le_iff.1 (h.2 w hw) with hd | ⟨-, hb | ⟨-, hle⟩⟩
  · omega
  · simp [sideBit, hvs, hws] at hb
  · exact hle

/-- **Lemma A**: a greatest term not on side `l` is the `l`-leading term. -/
theorem isLead_of_max {l : Λ} {y : Std σC inc B} {v : Mono σ B.S} (hv : v ∈ y.supp)
    (hmax : ∀ w ∈ y.supp, w ≤ v) (hs : v.side ≠ some l) : IsLead (some l) y v := by
  have hd : v.deg = y.deg :=
    le_antisymm (Std.deg_le hv) (Finset.sup_le fun w hw => Mono.deg_le_of_le (hmax w hw))
  exact ⟨hv, hd, hs, fun w hw _ _ => hmax w hw⟩

theorem isLead_none_of_max {l : Λ} {y : Std σC inc B} {v : Mono σ B.S} (hp : IsPureS l y)
    (hv : v ∈ y.supp) (hmax : ∀ w ∈ y.supp, w ≤ v) : IsLead none y v :=
  ⟨⟨l, hp⟩, hv, hmax⟩

/-- A single monomial not on side `μ` is its own `μ`-leading term. -/
theorem isLead_mono {μ : Option Λ} {u : Mono σ B.S} (hu : u.side ≠ μ) :
    IsLead μ (Std.mono σC inc B u) u := by
  have hmem : u ∈ (Std.mono σC inc B u).supp := by rw [Std.supp_mono]; simp
  have hmax : ∀ w ∈ (Std.mono σC inc B u).supp, w ≤ u := by
    intro w hw; rw [Std.supp_mono, Finset.mem_singleton] at hw; rw [hw]
  cases μ with
  | some l => exact isLead_of_max hmem hmax hu
  | none =>
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 hu
    refine isLead_none_of_max (l := l) ⟨fun h0 => ?_, fun w hw _ => ?_⟩ hmem hmax
    · rw [h0, Std.supp_eq_empty.2 rfl] at hmem; exact absurd hmem (by simp)
    · rw [Std.supp_mono, Finset.mem_singleton] at hw; rw [hw, hl]

/-! ## Lemma 5.1, iterated -/

/-- **Lemma 5.1, iterated.** -/
theorem lead_word {y : Std σC inc B} {v : Mono σ B.S} (t : Letter σ) (ts : List (Letter σ))
    (h : ChainAt v.left v.side (t :: ts)) {l : Λ} (hl : firstSide (t :: ts) = some l)
    (hv : IsLead (some l) y v) :
    IsPureS t.side (wordAct inc (t :: ts) • y) ∧
      (∀ w ∈ (wordAct inc (t :: ts) • y).supp, w ≤ Mono.pre (t :: ts) v h) ∧
      Std.coeff σC inc B (wordAct inc (t :: ts) • y) (Mono.pre (t :: ts) v h) =
        Std.coeff σC inc B y v ∧
      (wordAct inc (t :: ts) • y).deg = y.deg + (ts.length + 1) := by
  induction ts generalizing t with
  | nil =>
    rw [firstSide_singleton, Option.some.injEq] at hl
    subst hl
    rw [wordAct_cons, wordAct_nil, mul_one, Mono.pre_singleton]
    obtain ⟨h1, h2, h3, h4⟩ := lead_letter t hv h.2.1 h.2.2
    exact ⟨h1, h2, h3, by rw [h4]; rfl⟩
  | cons t' ts ih =>
    rw [firstSide_cons_cons] at hl
    obtain ⟨h1, h2, h3, h4⟩ := ih t' h.1 hl
    set z := wordAct inc (t' :: ts) • y
    set K' := Mono.pre (t' :: ts) v h.1
    have hK' : K' ∈ z.supp := by
      rw [Std.mem_supp, h3]; exact Std.mem_supp.1 hv.mem_supp
    have hK's : K'.side = some t'.side := Mono.side_pre _ _ _
    have hlead : IsLead (some t.side) z K' :=
      isLead_of_max hK' h2 (by rw [hK's]; exact fun e => h.2.2 (e.symm.trans rfl))
    have e₁ : t.right = K'.left := h.2.1.trans (Mono.left_pre _ _ _).symm
    have e₂ : some t.side ≠ K'.side := fun e => h.2.2 (e.trans (Mono.side_pre _ _ _))
    obtain ⟨g1, g2, g3, g4⟩ := lead_letter t hlead e₁ e₂
    have hpre : Mono.pre (t :: t' :: ts) v h = Mono.cons t K' e₁ e₂ := Mono.ext rfl rfl
    have hact : wordAct inc (t :: t' :: ts) • y = inc t.side t.val • z := by
      rw [wordAct_cons, mul_smul]
    rw [hpre, hact]
    refine ⟨g1, g2, g3.trans h3, ?_⟩
    rw [g4, h4]; simp only [List.length_cons]; ring

end Bergman.Core
