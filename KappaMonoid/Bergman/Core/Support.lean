/-
**Support, degree and coordinates in a standard module** (Bergman §5, mirrored).

For `y ∈ Std` (a `k`-linear combination of monomials):

* `supp y`, the monomials occurring in `y`, and `deg y`, the largest degree occurring;
* `strip μ w`: for a monomial `w`, the monomial `u ∈ U_{~μ}` with `w = u` or `w = t u` for a letter
  `t` of `R_μ` (none if `w` is a base element of `N_μ`);
* `msupp μ y`, Bergman's `μ`-support: for `μ = some l` the monomials `strip (some l) w`,
  `w ∈ supp y`; for `μ = none` all of `supp y` (Bergman counts the base elements of `N_0` in the
  `0`-support);
* `coord μ u y ∈ R_μ e_{left u}`, the coefficient of `u` in the free part of `Std` over `R_μ`
  (Bergman's `c_{μu}`), which is `R_μ`-linear and nonzero exactly when `u` is in the `μ`-support.
-/
import KappaMonoid.Bergman.Core.Std

universe u

set_option linter.unusedSectionVars false

namespace Bergman.Core

open Module

variable {k : Type u} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  {σ : ∀ l, (ι → k) →ₐ[k] R l} [Fact (∀ l, Function.Injective (σ l))]
  {C : Type u} [Ring C] [Algebra k C] (σC : (ι → k) →ₐ[k] C) (inc : ∀ l, R l →ₐ[k] C)
  [Fact (IsCoprod k σ C σC inc)]
  {N : Option Λ → Type u} [∀ μ, AddCommGroup (N μ)] [∀ μ, Module (Rμ k ι R μ) (N μ)]
  [∀ μ, Module k (N μ)] [∀ μ, IsScalarTower k (Rμ k ι R μ) (N μ)] (B : HomBases σ N)

/-! ## Coefficients, support, degree -/

/-- The coefficients of an element of `Std`. -/
noncomputable def Std.coeff : Std σC inc B ≃ₗ[k] (Mono σ B.S →₀ k) := LinearEquiv.refl k _

variable {σC inc B}

/-- The monomials occurring in `y`. -/
noncomputable def Std.supp (y : Std σC inc B) : Finset (Mono σ B.S) := (Std.coeff σC inc B y).support

/-- The degree: the largest degree of a monomial occurring (`0` for `y = 0`). -/
noncomputable def Std.deg (y : Std σC inc B) : ℕ := y.supp.sup Mono.deg

theorem Std.mem_supp {y : Std σC inc B} {w : Mono σ B.S} :
    w ∈ y.supp ↔ Std.coeff σC inc B y w ≠ 0 := Finsupp.mem_support_iff

theorem Std.coeff_mono (w w' : Mono σ B.S) :
    Std.coeff σC inc B (Std.mono σC inc B w) w' = if w = w' then 1 else 0 := by
  change (Finsupp.single w 1 : Mono σ B.S →₀ k) w' = _
  rw [Finsupp.single_apply]

theorem Std.coeff_mono' (w : Mono σ B.S) :
    Std.coeff σC inc B (Std.mono σC inc B w) = Finsupp.single w 1 := rfl

theorem Std.supp_mono (w : Mono σ B.S) : (Std.mono σC inc B w).supp = {w} := by
  ext w'
  rw [Std.mem_supp, Std.coeff_mono, Finset.mem_singleton]
  split_ifs with h <;> simp [h, eq_comm]

theorem Std.deg_mono (w : Mono σ B.S) : (Std.mono σC inc B w).deg = w.deg := by
  rw [Std.deg, Std.supp_mono, Finset.sup_singleton]

theorem Std.deg_le {y : Std σC inc B} {w : Mono σ B.S} (h : w ∈ y.supp) : w.deg ≤ y.deg :=
  Finset.le_sup (f := Mono.deg) h

theorem Std.supp_eq_empty {y : Std σC inc B} : y.supp = ∅ ↔ y = 0 := by
  rw [Std.supp, Finsupp.support_eq_empty, LinearEquiv.map_eq_zero_iff]

theorem Std.exists_mem_supp {y : Std σC inc B} (hy : y ≠ 0) : ∃ w ∈ y.supp, w.deg = y.deg := by
  have hne : y.supp.Nonempty := Finset.nonempty_iff_ne_empty.2 (mt Std.supp_eq_empty.1 hy)
  obtain ⟨w, hw, hw'⟩ := Finset.exists_mem_eq_sup _ hne Mono.deg
  exact ⟨w, hw, hw'.symm⟩

theorem Std.supp_add (y z : Std σC inc B) : (y + z).supp ⊆ y.supp ∪ z.supp := by
  simpa [Std.supp] using Finsupp.support_add

theorem Std.supp_smul (c : k) (y : Std σC inc B) : (c • y).supp ⊆ y.supp := by
  simpa [Std.supp] using Finsupp.support_smul

theorem Std.supp_neg (y : Std σC inc B) : (-y).supp = y.supp := by
  simp [Std.supp]

theorem Std.supp_sum {α : Type*} (s : Finset α) (y : α → Std σC inc B) :
    (∑ a ∈ s, y a).supp ⊆ s.biUnion fun a => (y a).supp := by
  simpa [Std.supp] using Finsupp.support_finsetSum

/-- Every element is the combination of its monomials. -/
theorem Std.eq_sum_mono (y : Std σC inc B) :
    y = ∑ w ∈ y.supp, Std.coeff σC inc B y w • Std.mono σC inc B w := by
  apply (Std.coeff σC inc B).injective
  rw [map_sum]
  simp only [map_smul, Std.coeff_mono', Finsupp.smul_single, smul_eq_mul, mul_one]
  exact (Finsupp.sum_single _).symm

/-- Two elements with the same coefficients are equal. -/
theorem Std.ext_coeff {y z : Std σC inc B} (h : ∀ w, Std.coeff σC inc B y w = Std.coeff σC inc B z w) :
    y = z := (Std.coeff σC inc B).injective (Finsupp.ext h)

/-! ## Stripping a letter -/

variable (B) in
/-- The monomial `u ∈ U_{~μ}` with `w = u` or `w = t u`, `t` a letter of `R_μ`; `none` for a base
element of `N_μ`. -/
noncomputable def strip (μ : Option Λ) (w : Mono σ B.S) : Option (NotSide B μ) :=
  (monoSplit B μ w).elim (fun _ => none) (fun p => some p.1)

theorem strip_join_inl (μ : Option Λ) (x) : strip B μ (monoJoin B μ (.inl x)) = none := by
  rw [strip, monoSplit_monoJoin]; rfl

theorem strip_join_inr (μ : Option Λ) (u : NotSide B μ) (o) :
    strip B μ (monoJoin B μ (.inr ⟨u, o⟩)) = some u := by
  rw [strip, monoSplit_monoJoin]; rfl

theorem strip_eq_some_iff {μ : Option Λ} {w : Mono σ B.S} {u : NotSide B μ} :
    strip B μ w = some u ↔ ∃ o, w = monoJoin B μ (.inr ⟨u, o⟩) := by
  obtain ⟨x, rfl⟩ := monoJoin_surjective B μ w
  constructor
  · intro h
    rcases x with x | ⟨u', o⟩
    · rw [strip_join_inl] at h; exact absurd h (by simp)
    · rw [strip_join_inr] at h
      cases h
      exact ⟨o, rfl⟩
  · rintro ⟨o, ho⟩
    rw [monoJoin_injective B μ ho, strip_join_inr]

theorem strip_self {μ : Option Λ} (u : NotSide B μ) : strip B μ u.1 = some u :=
  strip_join_inr μ u none

theorem deg_join_inr (μ : Option Λ) (u : NotSide B μ) (o : Option (Σ i, Tl σ μ i u.1.left)) :
    (monoJoin B μ (.inr ⟨u, o⟩)).deg = u.1.deg + if o.isSome then 1 else 0 := by
  rcases o with _ | ⟨i, t⟩
  · rfl
  · cases μ with
    | none => exact (isEmpty_Tl_none σ i _).elim t
    | some l => rfl

theorem side_join_some (l : Λ) (u : NotSide B (some l)) (i : ι) (t : Tl σ (some l) i u.1.left) :
    (monoJoin B (some l) (.inr ⟨u, some ⟨i, t⟩⟩)).side = some l := rfl

/-- If `strip μ w = u`, then `deg u ≤ deg w`, with equality only for `w = u`. -/
theorem deg_of_strip {μ : Option Λ} {w : Mono σ B.S} {u : NotSide B μ} (h : strip B μ w = some u) :
    u.1.deg ≤ w.deg ∧ (w.deg = u.1.deg → w = u.1) := by
  obtain ⟨o, rfl⟩ := strip_eq_some_iff.1 h
  rw [deg_join_inr]
  rcases o with _ | o
  · exact ⟨le_rfl, fun _ => rfl⟩
  · simp

/-! ## The action of `k^ι` -/

theorem σC_smul_mono (c : ι → k) (w : Mono σ B.S) :
    σC c • Std.mono σC inc B w = c w.left • Std.mono σC inc B w := by
  have hc : c = ∑ i, c i • (ee i : ι → k) := by
    funext x; simp [ee, Pi.single_apply]
  have he : ∀ i, σC (ee i) • Std.mono σC inc B w =
      if w.left = i then Std.mono σC inc B w else 0 := fun i =>
    (Std.incμ_smul σC inc B none (eμ σ none i) _).trans (Std.act_eμ_mono σC inc B none i w)
  conv_lhs => rw [hc]
  rw [map_sum, Finset.sum_smul]
  simp only [map_smul, smul_assoc, he, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem Std.supp_σC_smul (c : ι → k) (y : Std σC inc B) : (σC c • y).supp ⊆ y.supp := by
  conv_lhs => rw [Std.eq_sum_mono y]
  rw [Finset.smul_sum]
  refine (Std.supp_sum _ _).trans fun w hw => ?_
  obtain ⟨w', hw', hw⟩ := Finset.mem_biUnion.1 hw
  rw [smul_comm, σC_smul_mono, smul_smul] at hw
  have := Std.supp_smul _ _ hw
  rw [Std.supp_mono, Finset.mem_singleton] at this
  rw [this]; exact hw'

/-! ## The `μ`-support -/

variable (σC inc B) in
/-- Bergman's `μ`-support. -/
noncomputable def msupp : Option Λ → Std σC inc B → Finset (Mono σ B.S)
  | none, y => y.supp
  | some l, y => y.supp.biUnion fun w => ((strip B (some l) w).map Subtype.val).toFinset

theorem mem_msupp_some {l : Λ} {y : Std σC inc B} {u : Mono σ B.S} :
    u ∈ msupp σC inc B (some l) y ↔ ∃ h : u.side ≠ some l, ∃ w ∈ y.supp, strip B (some l) w = some ⟨u, h⟩ := by
  simp only [msupp, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def, Option.map_eq_some_iff]
  constructor
  · rintro ⟨w, hw, ⟨u', hu'⟩, h, rfl⟩
    exact ⟨hu', w, hw, h⟩
  · rintro ⟨h, w, hw, hs⟩
    exact ⟨w, hw, ⟨u, h⟩, hs, rfl⟩

theorem msupp_none (y : Std σC inc B) : msupp σC inc B none y = y.supp := rfl

/-- Monomials of `y` not on side `μ` are in the `μ`-support. -/
theorem mem_msupp_of_mem_supp {μ : Option Λ} {y : Std σC inc B} {w : Mono σ B.S} (hw : w ∈ y.supp)
    (hs : w.side ≠ μ) : w ∈ msupp σC inc B μ y := by
  cases μ with
  | none => exact hw
  | some l => exact mem_msupp_some.2 ⟨hs, w, hw, strip_self ⟨w, hs⟩⟩

theorem deg_le_of_mem_msupp {μ : Option Λ} {y : Std σC inc B} {u : Mono σ B.S}
    (h : u ∈ msupp σC inc B μ y) : u.deg ≤ y.deg := by
  cases μ with
  | none => exact Std.deg_le h
  | some l =>
    obtain ⟨hu, w, hw, hs⟩ := mem_msupp_some.1 h
    exact (deg_of_strip hs).1.trans (Std.deg_le hw)

/-- For `μ = some l`, a monomial of the `l`-support of degree `deg y` is itself in `y`. -/
theorem mem_supp_of_mem_msupp {l : Λ} {y : Std σC inc B} {u : Mono σ B.S}
    (h : u ∈ msupp σC inc B (some l) y) (hd : y.deg ≤ u.deg) : u ∈ y.supp := by
  obtain ⟨hu, w, hw, hs⟩ := mem_msupp_some.1 h
  have h1 := deg_of_strip hs
  have := Std.deg_le hw
  have h11 : u.deg ≤ w.deg := h1.1
  have e : w = u := h1.2 (by show w.deg = u.deg; omega)
  rw [← e]
  exact hw

theorem msupp_add (μ : Option Λ) (y z : Std σC inc B) :
    msupp σC inc B μ (y + z) ⊆ msupp σC inc B μ y ∪ msupp σC inc B μ z := by
  cases μ with
  | none => exact Std.supp_add y z
  | some l =>
    intro u hu
    obtain ⟨h, w, hw, hs⟩ := mem_msupp_some.1 hu
    rcases Finset.mem_union.1 (Std.supp_add y z hw) with hw' | hw'
    · exact Finset.mem_union_left _ (mem_msupp_some.2 ⟨h, w, hw', hs⟩)
    · exact Finset.mem_union_right _ (mem_msupp_some.2 ⟨h, w, hw', hs⟩)

theorem msupp_smul (μ : Option Λ) (c : k) (y : Std σC inc B) :
    msupp σC inc B μ (c • y) ⊆ msupp σC inc B μ y := by
  cases μ with
  | none => exact Std.supp_smul c y
  | some l =>
    intro u hu
    obtain ⟨h, w, hw, hs⟩ := mem_msupp_some.1 hu
    exact mem_msupp_some.2 ⟨h, w, Std.supp_smul c y hw, hs⟩

theorem msupp_neg (μ : Option Λ) (y : Std σC inc B) :
    msupp σC inc B μ (-y) = msupp σC inc B μ y := by
  cases μ <;> simp [msupp, Std.supp_neg]

theorem msupp_zero (μ : Option Λ) : msupp σC inc B μ (0 : Std σC inc B) = ∅ := by
  cases μ <;> simp [msupp, Std.supp_eq_empty.2 rfl]

/-! ## Coordinates -/

variable (σC inc B) in
/-- Bergman's coordinate `c_{μu} : Std → R_μ e_{left u}`. -/
noncomputable def coord (μ : Option Λ) (u : NotSide B μ) :
    Std σC inc B →ₗ[k] Submodule.span (Rμ k ι R μ) {eμ σ μ u.1.left} :=
  DFinsupp.lapply u ∘ₗ LinearMap.snd k _ _ ∘ₗ (Std.Φ σC inc B μ).toLinearMap

theorem coord_smul (μ : Option Λ) (u : NotSide B μ) (r : Rμ k ι R μ) (y : Std σC inc B) :
    coord σC inc B μ u (incμ σC inc μ r • y) = r • coord σC inc B μ u y := by
  simp [coord, Std.Φ_incμ_smul]

theorem repr_coord (μ : Option Λ) (u : NotSide B μ) (y : Std σC inc B) (o) :
    (leftIdealBasis σ μ u.1.left).repr (coord σC inc B μ u y) o =
      Std.coeff σC inc B y (monoJoin B μ (.inr ⟨u, o⟩)) := by
  classical
  have : ((Finsupp.lapply o).comp ((leftIdealBasis σ μ u.1.left).repr.toLinearMap.comp
      (coord σC inc B μ u))) = (Finsupp.lapply (monoJoin B μ (.inr ⟨u, o⟩))).comp
        (Std.coeff σC inc B).toLinearMap :=
    (Std.monoBasis σC inc B).ext fun w => by
      obtain ⟨x, rfl⟩ := monoJoin_surjective B μ w
      simp only [LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
        Std.monoBasis_apply]
      rw [Std.coeff_mono]
      simp only [coord, LinearMap.comp_apply, LinearEquiv.coe_coe, Std.Φ_mono_join,
        LinearMap.snd_apply, DFinsupp.lapply_apply]
      rcases x with ⟨j, s⟩ | ⟨u', o'⟩
      · rw [targetBasis_inl]
        simp only [DFinsupp.zero_apply, map_zero, Finsupp.zero_apply]
        rw [if_neg]
        intro h
        have := monoJoin_injective B μ h
        exact absurd this (by simp)
      · rw [targetBasis_inr]
        by_cases hu : u' = u
        · subst hu
          rw [DFinsupp.single_eq_same, Basis.repr_self, Finsupp.single_apply]
          by_cases ho : o' = o
          · subst ho; simp
          · rw [if_neg ho, if_neg]
            intro h
            have := monoJoin_injective B μ h
            simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
            exact ho this
        · rw [DFinsupp.single_eq_of_ne (Ne.symm hu), map_zero, Finsupp.zero_apply, if_neg]
          intro h
          have := monoJoin_injective B μ h
          simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at this
          exact hu this.1
  exact LinearMap.congr_fun this y

theorem coord_ne_zero_iff {μ : Option Λ} {u : NotSide B μ} {y : Std σC inc B} :
    coord σC inc B μ u y ≠ 0 ↔ ∃ w ∈ y.supp, strip B μ w = some u := by
  rw [Ne, ← (leftIdealBasis σ μ u.1.left).repr.map_eq_zero_iff, ← Ne, Finsupp.ne_iff]
  simp only [repr_coord, Finsupp.zero_apply, strip_eq_some_iff, Std.mem_supp]
  constructor
  · rintro ⟨o, ho⟩
    exact ⟨_, ho, o, rfl⟩
  · rintro ⟨w, hw, o, rfl⟩
    exact ⟨o, hw⟩

theorem mem_msupp_iff_coord {μ : Option Λ} {y : Std σC inc B} (u : NotSide B μ) :
    u.1 ∈ msupp σC inc B μ y ↔ coord σC inc B μ u y ≠ 0 := by
  rw [coord_ne_zero_iff]
  cases μ with
  | none =>
    constructor
    · intro h; exact ⟨u.1, h, strip_self u⟩
    · rintro ⟨w, hw, hs⟩
      obtain ⟨o, rfl⟩ := strip_eq_some_iff.1 hs
      rcases o with _ | ⟨i, t⟩
      · exact hw
      · exact (isEmpty_Tl_none σ i _).elim t
  | some l =>
    rw [mem_msupp_some]
    exact ⟨fun ⟨_, w, hw, hs⟩ => ⟨w, hw, hs⟩, fun ⟨w, hw, hs⟩ => ⟨u.2, w, hw, hs⟩⟩

/-- **The `μ`-support shrinks under `R_μ`.** -/
theorem msupp_incμ_smul (μ : Option Λ) (r : Rμ k ι R μ) (y : Std σC inc B) :
    msupp σC inc B μ (incμ σC inc μ r • y) ⊆ msupp σC inc B μ y := by
  intro u hu
  by_cases hs : u.side = μ
  · -- only possible for `μ = none`: base elements of `N_0`
    cases μ with
    | some l =>
      obtain ⟨h, -⟩ := mem_msupp_some.1 hu
      exact absurd hs h
    | none => exact Std.supp_σC_smul r y hu
  · have e := mem_msupp_iff_coord (y := incμ σC inc μ r • y) (⟨u, hs⟩ : NotSide B μ)
    have e' := mem_msupp_iff_coord (y := y) (⟨u, hs⟩ : NotSide B μ)
    refine e'.2 fun h => e.1 hu ?_
    rw [coord_smul, h, smul_zero]

/-- A coordinate at a monomial of maximal degree is the coefficient times `e`. -/
theorem coord_of_deg {μ : Option Λ} {u : NotSide B μ} {y : Std σC inc B} (hd : y.deg ≤ u.1.deg) :
    (coord σC inc B μ u y : Rμ k ι R μ) = Std.coeff σC inc B y u.1 • eμ σ μ u.1.left := by
  have h := (leftIdealBasis σ μ u.1.left).linearCombination_repr (coord σC inc B μ u y)
  have hz : ∀ o, o ≠ none → (leftIdealBasis σ μ u.1.left).repr (coord σC inc B μ u y) o = 0 := by
    intro o ho
    rw [repr_coord]
    by_contra hne
    have := Std.deg_le (Std.mem_supp.2 hne)
    rw [deg_join_inr] at this
    rcases o with _ | o
    · exact ho rfl
    · simp at this; omega
  rw [← h, Finsupp.linearCombination_apply, Finsupp.sum_eq_single none (fun o _ ho => by
    rw [hz o ho, zero_smul]) (by simp), repr_coord]
  simp [leftIdealBasis_none]
  rfl

/-! ## How `R_μ` acts on monomials -/

/-- The monomials of an element of `N_μ ⊂ Std` are base elements of `N_μ`. -/
theorem strip_of_mem_supp_incl {μ : Option Λ} {n : N μ} {w : Mono σ B.S}
    (hw : w ∈ (Std.incl σC inc B μ n).supp) : strip B μ w = none := by
  have hn : Std.incl σC inc B μ n = ∑ x ∈ ((B.basis μ).repr n).support,
      (B.basis μ).repr n x • Std.mono σC inc B (monoJoin B μ (.inl x)) := by
    conv_lhs => rw [← (B.basis μ).linearCombination_repr n]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun ⟨j, s⟩ _ => ?_
    rw [map_smul, Std.incl_basis]; rfl
  rw [hn] at hw
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.1 (Std.supp_sum _ _ hw)
  have := Std.supp_smul _ _ hx
  rw [Std.supp_mono, Finset.mem_singleton] at this
  rw [this, strip_join_inl]

/-- The monomials of `Φ⁻¹ (0, (u ↦ v))` all strip to `u`. -/
theorem strip_of_mem_supp_single {μ : Option Λ} (u : NotSide B μ)
    (v : Submodule.span (Rμ k ι R μ) {eμ σ μ u.1.left}) {w : Mono σ B.S}
    (hw : w ∈ ((Std.Φ σC inc B μ).symm (0, DFinsupp.single u v)).supp) : strip B μ w = some u := by
  set b := leftIdealBasis σ μ u.1.left
  have hx : (Std.Φ σC inc B μ).symm (0, DFinsupp.single u v) = ∑ o ∈ (b.repr v).support,
      b.repr v o • Std.mono σC inc B (monoJoin B μ (.inr ⟨u, o⟩)) := by
    apply (Std.Φ σC inc B μ).injective
    rw [LinearEquiv.apply_symm_apply, map_sum]
    simp only [map_smul, Std.Φ_mono_join, targetBasis_inr, Prod.smul_mk, smul_zero]
    refine Prod.ext (by rw [Prod.fst_sum]; simp) ?_
    rw [Prod.snd_sum]
    simp only [← DFinsupp.single_smul]
    have hsum : v = ∑ o ∈ (b.repr v).support, b.repr v o • b o := by
      conv_lhs => rw [← b.linearCombination_repr v]
      rfl
    conv_lhs => rw [hsum]
    exact map_sum (DFinsupp.singleAddHom (fun u : NotSide B μ =>
      ↥(Submodule.span (Rμ k ι R μ) {eμ σ μ u.1.left})) u) _ _
  rw [hx] at hw
  obtain ⟨o, -, ho⟩ := Finset.mem_biUnion.1 (Std.supp_sum _ _ hw)
  have := Std.supp_smul _ _ ho
  rw [Std.supp_mono, Finset.mem_singleton] at this
  rw [this, strip_join_inr]

/-- **`R_μ` preserves the stripped monomial**: every monomial of `r w` strips (for `μ`) to the
same monomial as `w`. -/
theorem strip_of_mem_supp_smul {μ : Option Λ} (r : Rμ k ι R μ) {w w' : Mono σ B.S}
    (hw' : w' ∈ (incμ σC inc μ r • Std.mono σC inc B w).supp) : strip B μ w' = strip B μ w := by
  obtain ⟨x, rfl⟩ := monoJoin_surjective B μ w
  rcases x with x | ⟨u, o⟩
  · rw [strip_join_inl]
    have : Std.mono σC inc B (monoJoin B μ (.inl x)) = Std.incl σC inc B μ (B.basis μ x) := by
      rw [Std.incl_basis]; rfl
    rw [this, ← Std.incl_smul] at hw'
    exact strip_of_mem_supp_incl hw'
  · rw [strip_join_inr]
    have : incμ σC inc μ r • Std.mono σC inc B (monoJoin B μ (.inr ⟨u, o⟩)) =
        (Std.Φ σC inc B μ).symm (0, DFinsupp.single u (r • leftIdealBasis σ μ u.1.left o)) := by
      rw [LinearEquiv.eq_symm_apply, Std.Φ_incμ_smul, Std.Φ_mono_join, targetBasis_inr,
        Prod.smul_mk, smul_zero, DFinsupp.single_smul]
    rw [this] at hw'
    exact strip_of_mem_supp_single u _ hw'

/-- `r w` has degree `≤ deg w + 1`, and its terms of degree `deg w + 1` are on side `μ`; if `w` is
itself on side `μ`, all terms have degree `≤ deg w` and those of degree `deg w` are on side `μ`. -/
theorem deg_of_mem_supp_smul {μ : Option Λ} (r : Rμ k ι R μ) {w w' : Mono σ B.S}
    (hw' : w' ∈ (incμ σC inc μ r • Std.mono σC inc B w).supp) :
    (w.side ≠ μ → (w'.deg ≤ w.deg + 1 ∧ (w'.deg = w.deg + 1 → w'.side = μ) ∧
      (w'.deg ≤ w.deg → w' = w))) ∧
    (w.side = μ → w'.deg ≤ w.deg ∧ (w'.deg = w.deg → w'.side = μ)) := by
  have hs := strip_of_mem_supp_smul r hw'
  obtain ⟨x, rfl⟩ := monoJoin_surjective B μ w
  obtain ⟨y, rfl⟩ := monoJoin_surjective B μ w'
  rcases x with x | ⟨u, o⟩ <;> rcases y with y | ⟨u', o'⟩ <;>
    simp only [strip_join_inl, strip_join_inr, reduceCtorEq, Option.some.injEq] at hs
  · -- both base elements of `N_μ`
    obtain ⟨j, s⟩ := x; obtain ⟨j', s'⟩ := y
    exact ⟨fun h => absurd rfl h, fun _ => ⟨le_rfl, fun _ => rfl⟩⟩
  · subst hs
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [deg_join_inr, deg_join_inr]
      rcases o with _ | o <;> rcases o' with _ | o'
      · exact ⟨by simp, by simp, fun _ => rfl⟩
      · refine ⟨by simp, fun _ => ?_, by simp⟩
        cases μ with
        | none => obtain ⟨i, t⟩ := o'; exact (isEmpty_Tl_none σ i _).elim t
        | some l => obtain ⟨i, t⟩ := o'; rfl
      · exact absurd (by obtain ⟨i, t⟩ := o; cases μ with
          | none => exact (isEmpty_Tl_none σ i _).elim t
          | some l => rfl) h
      · exact absurd (by obtain ⟨i, t⟩ := o; cases μ with
          | none => exact (isEmpty_Tl_none σ i _).elim t
          | some l => rfl) h
    · rw [deg_join_inr, deg_join_inr]
      rcases o with _ | o
      · exact absurd h u'.2
      · rcases o' with _ | o'
        · exact ⟨by simp, fun h' => by simp at h'⟩
        · refine ⟨by simp, fun _ => ?_⟩
          cases μ with
          | none => obtain ⟨i, t⟩ := o'; exact (isEmpty_Tl_none σ i _).elim t
          | some l => obtain ⟨i, t⟩ := o'; rfl

/-- Left multiplication by a letter on a monomial it cannot be applied to (wrong index). -/
theorem letter_smul_mono_of_ne (t : Letter σ) (w : Mono σ B.S) (h : t.right ≠ w.left) :
    inc t.side t.val • Std.mono σC inc B w = 0 := by
  have ht : tval σ t.2.2.2 = tval σ t.2.2.2 * eμ σ (some t.1) t.2.2.1 := (tval_mul_eμ σ t.2.2.2).symm
  change incμ σC inc (some t.1) (tval σ t.2.2.2) • _ = _
  rw [ht, map_mul, mul_smul, Std.incμ_smul σC inc B (some t.1) (eμ σ (some t.1) t.2.2.1),
    Std.act_eμ_mono, if_neg (show ¬ (w.left = t.2.2.1) from fun h' => h h'.symm), smul_zero]
end Bergman.Core
