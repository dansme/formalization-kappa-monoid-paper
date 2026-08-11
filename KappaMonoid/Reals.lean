/-
Examples 3.3(2)(3) and the corresponding entries of Examples 3.12 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

Braiding in `ℝ≥0`: two families are `ℵ₀⁻`-braided exactly when they have the same series sum and
their supports are both finite or both infinite.  The support condition is what obstructs the two
`ℵ₀`-monoid structures on `ℝ≥0 ∪ {∞}` of Examples 2.3(1)(2) from being braided over `ℝ≥0`, and the
universal `ℵ₀`-extension is instead `ℝ≥0 ∪ ℝ̃>0 ∪ {∞}`, a second copy of the positive reals
recording that a sum was reached only with infinite support.
-/
import KappaMonoid.Braiding
import KappaMonoid.Examples
import KappaMonoid.Universal

universe u v

open Cardinal Function Set
open scoped ENNReal NNReal Classical

namespace KappaMonoid

open KMonoid LMonoid

/-! ## Series sums of families of nonnegative reals

Everything is phrased through `esum`, the sum of the family as an unordered series valued in
`ℝ≥0∞` — this is the paper's "sum of the convergent series (which may be `∞`)", and being a `tsum`
in `ℝ≥0∞` it is unconditional, hence independent of the order of the family. -/

/-- The series sum of a family of nonnegative reals, valued in `ℝ≥0∞`. -/
noncomputable def esum {ι : Type u} (x : ι → ℝ≥0) : ℝ≥0∞ := ∑' i, (x i : ℝ≥0∞)

/-- The series sum is unconditional: it does not see a reindexing, even across universes. -/
theorem esum_comp_equiv {ι : Type u} {ι' : Type v} (e : ι ≃ ι') (x : ι' → ℝ≥0) :
    esum (x ∘ e) = esum x :=
  e.tsum_eq fun i => ((x i : ℝ≥0) : ℝ≥0∞)

/-- The `n`-th partial sum of a family indexed by `ℕ`. -/
noncomputable def psum (x : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0 := ∑ i ∈ Finset.range n, x i

theorem psum_zero (x : ℕ → ℝ≥0) : psum x 0 = 0 := rfl

theorem psum_mono (x : ℕ → ℝ≥0) : Monotone (psum x) := fun _ _ h =>
  Finset.sum_le_sum_of_subset (by simpa using h)

theorem coe_psum (x : ℕ → ℝ≥0) (n : ℕ) :
    ((psum x n : ℝ≥0) : ℝ≥0∞) = ∑ i ∈ Finset.range n, (x i : ℝ≥0∞) :=
  ENNReal.ofNNReal_finsetSum _ _

/-- Partial sums never exceed the total. -/
theorem coe_psum_le_esum (x : ℕ → ℝ≥0) (n : ℕ) : ((psum x n : ℝ≥0) : ℝ≥0∞) ≤ esum x := by
  rw [coe_psum]
  exact ENNReal.sum_le_tsum _

/-- With infinite support no partial sum *reaches* the total: there is always a positive entry
beyond it. -/
theorem coe_psum_lt_esum {x : ℕ → ℝ≥0} (hx : (Function.support x).Infinite) (n : ℕ) :
    ((psum x n : ℝ≥0) : ℝ≥0∞) < esum x := by
  classical
  obtain ⟨j, hj, hjn⟩ := hx.exists_gt n
  have hjne : ((x j : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa using Function.mem_support.mp hj
  have hnotmem : j ∉ Finset.range n := by simp [Nat.not_lt.mpr hjn.le]
  calc ((psum x n : ℝ≥0) : ℝ≥0∞) < ((psum x n : ℝ≥0) : ℝ≥0∞) + (x j : ℝ≥0∞) :=
        ENNReal.lt_add_right (ENNReal.coe_ne_top) hjne
    _ = ∑ i ∈ insert j (Finset.range n), (x i : ℝ≥0∞) := by
        rw [Finset.sum_insert hnotmem, coe_psum, add_comm]
    _ ≤ esum x := ENNReal.sum_le_tsum _

/-- If the total exceeds `t`, then so does some partial sum beyond any prescribed index. -/
theorem exists_psum_ge {y : ℕ → ℝ≥0} {t : ℝ≥0} (h : (t : ℝ≥0∞) < esum y) (c : ℕ) :
    ∃ m, c < m ∧ t ≤ psum y m := by
  classical
  rw [esum, ENNReal.tsum_eq_iSup_sum] at h
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp h
  refine ⟨max (c + 1) (s.sup id + 1), lt_of_lt_of_le (Nat.lt_succ_self c) (le_max_left _ _), ?_⟩
  have hsub : s ⊆ Finset.range (max (c + 1) (s.sup id + 1)) := by
    intro i hi
    have hle : i ≤ s.sup id := Finset.le_sup (f := id) hi
    simp only [Finset.mem_range]
    omega
  have hle : ∑ i ∈ s, ((y i : ℝ≥0) : ℝ≥0∞)
      ≤ ((psum y (max (c + 1) (s.sup id + 1)) : ℝ≥0) : ℝ≥0∞) := by
    rw [coe_psum]
    exact Finset.sum_le_sum_of_subset hsub
  exact_mod_cast (lt_of_lt_of_le hs hle).le

/-! ## The braiding of two infinitely supported families in `ℝ≥0`

The construction of the paper's "inductive argument": alternately grow an interval along `x` until
its partial sum catches up with the `y`-partial sum reached so far, then an interval along `y`
until it catches up with the new `x`-partial sum.  Both steps are possible precisely because with
infinite support no partial sum reaches the common total (`coe_psum_lt_esum`), so there is always
room to overshoot.  The deficits `u`, `v` of `BraidingData` are then the differences of the
partial sums reached so far. -/

section RealBraid

variable (x y : ℕ → ℝ≥0)

/-- The recursion driving the braiding: the state after `k` steps is the pair of right endpoints
`(bI k, bJ k)` of the intervals built so far. -/
noncomputable def realBraidState (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (hsum : esum x = esum y) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | (k + 1) =>
      let s := realBraidState hx hy hsum k
      let bI' := (exists_psum_ge (y := x) (t := psum y s.2)
        ((coe_psum_lt_esum hy s.2).trans_eq hsum.symm) s.1).choose
      (bI', (exists_psum_ge (y := y) (t := psum x bI')
        ((coe_psum_lt_esum hx bI').trans_eq hsum) s.2).choose)

variable {x y}
variable (hx : (Function.support x).Infinite) (hy : (Function.support y).Infinite)
  (hsum : esum x = esum y)

/-- The `x`-boundary sequence. -/
noncomputable def realBraidBI (k : ℕ) : ℕ := (realBraidState x y hx hy hsum k).1

/-- The `y`-boundary sequence. -/
noncomputable def realBraidBJ (k : ℕ) : ℕ := (realBraidState x y hx hy hsum k).2

/-- The deficit of `y` behind `x`, playing the role of `u` in `BraidingData`. -/
noncomputable def realBraidU (k : ℕ) : ℝ≥0 :=
  psum x (realBraidBI hx hy hsum (k + 1)) - psum y (realBraidBJ hx hy hsum k)

/-- The deficit of `x` behind `y`, playing the role of `v` in `BraidingData`. -/
noncomputable def realBraidV (k : ℕ) : ℝ≥0 :=
  psum y (realBraidBJ hx hy hsum k) - psum x (realBraidBI hx hy hsum k)

theorem realBraidBI_zero : realBraidBI hx hy hsum 0 = 0 := rfl

theorem realBraidBJ_zero : realBraidBJ hx hy hsum 0 = 0 := rfl

theorem realBraidV_zero : realBraidV hx hy hsum 0 = 0 := by
  rw [realBraidV, realBraidBI_zero, realBraidBJ_zero, psum_zero, psum_zero, tsub_self]

/-- The defining property of `bI (k+1)`: it goes strictly beyond `bI k`, and its `x`-partial sum
catches up with the `y`-partial sum at `bJ k`. -/
theorem realBraidBI_succ_spec (k : ℕ) :
    realBraidBI hx hy hsum k < realBraidBI hx hy hsum (k + 1) ∧
      psum y (realBraidBJ hx hy hsum k) ≤ psum x (realBraidBI hx hy hsum (k + 1)) :=
  (exists_psum_ge (y := x) (t := psum y (realBraidBJ hx hy hsum k))
    ((coe_psum_lt_esum hy _).trans_eq hsum.symm) (realBraidBI hx hy hsum k)).choose_spec

/-- The defining property of `bJ (k+1)`: it goes strictly beyond `bJ k`, and its `y`-partial sum
catches up with the `x`-partial sum at `bI (k+1)`. -/
theorem realBraidBJ_succ_spec (k : ℕ) :
    realBraidBJ hx hy hsum k < realBraidBJ hx hy hsum (k + 1) ∧
      psum x (realBraidBI hx hy hsum (k + 1)) ≤ psum y (realBraidBJ hx hy hsum (k + 1)) :=
  (exists_psum_ge (y := y) (t := psum x (realBraidBI hx hy hsum (k + 1)))
    ((coe_psum_lt_esum hx _).trans_eq hsum) (realBraidBJ hx hy hsum k)).choose_spec

theorem realBraidBI_lt_succ (k : ℕ) :
    realBraidBI hx hy hsum k < realBraidBI hx hy hsum (k + 1) :=
  (realBraidBI_succ_spec hx hy hsum k).1

theorem realBraidBJ_lt_succ (k : ℕ) :
    realBraidBJ hx hy hsum k < realBraidBJ hx hy hsum (k + 1) :=
  (realBraidBJ_succ_spec hx hy hsum k).1

/-- The invariant: at every stage the `x`-partial sum lags behind the `y`-partial sum. -/
theorem realBraid_psum_le (k : ℕ) :
    psum x (realBraidBI hx hy hsum k) ≤ psum y (realBraidBJ hx hy hsum k) := by
  cases k with
  | zero => rw [realBraidBI_zero, realBraidBJ_zero, psum_zero, psum_zero]
  | succ k => exact (realBraidBJ_succ_spec hx hy hsum k).2

/-- Consecutive partial sums differ by the sum over the interval between them. -/
theorem psum_add_sum_Ico (z : ℕ → ℝ≥0) {m n : ℕ} (h : m ≤ n) :
    psum z m + ∑ i ∈ Finset.Ico m n, z i = psum z n := by
  rw [psum, psum, Finset.range_eq_Ico, Finset.range_eq_Ico,
    Finset.sum_Ico_consecutive z (Nat.zero_le m) h]

/-- The defining equation for `x`: the sum over the `k`-th `x`-interval is `v k + u k`. -/
theorem realBraidBI_sum_eq (k : ℕ) :
    ∑ i ∈ Finset.Ico (realBraidBI hx hy hsum k) (realBraidBI hx hy hsum (k + 1)), x i
      = realBraidV hx hy hsum k + realBraidU hx hy hsum k := by
  have hAB := realBraid_psum_le hx hy hsum k
  have hBC := (realBraidBI_succ_spec hx hy hsum k).2
  have hIco := psum_add_sum_Ico x (le_of_lt (realBraidBI_lt_succ hx hy hsum k))
  have hvu : realBraidV hx hy hsum k + realBraidU hx hy hsum k
      = psum x (realBraidBI hx hy hsum (k + 1)) - psum x (realBraidBI hx hy hsum k) :=
    (add_comm _ _).trans (tsub_add_tsub_cancel hBC hAB)
  rw [hvu]
  exact eq_tsub_of_add_eq ((add_comm _ _).trans hIco)

/-- The defining equation for `y`: the sum over the `k`-th `y`-interval is `v (k+1) + u k`. -/
theorem realBraidBJ_sum_eq (k : ℕ) :
    ∑ j ∈ Finset.Ico (realBraidBJ hx hy hsum k) (realBraidBJ hx hy hsum (k + 1)), y j
      = realBraidV hx hy hsum (k + 1) + realBraidU hx hy hsum k := by
  have hBC := (realBraidBI_succ_spec hx hy hsum k).2
  have hCD := (realBraidBJ_succ_spec hx hy hsum k).2
  have hIco := psum_add_sum_Ico y (le_of_lt (realBraidBJ_lt_succ hx hy hsum k))
  have hvu : realBraidV hx hy hsum (k + 1) + realBraidU hx hy hsum k
      = psum y (realBraidBJ hx hy hsum (k + 1)) - psum y (realBraidBJ hx hy hsum k) :=
    tsub_add_tsub_cancel hCD hBC
  rw [hvu]
  exact eq_tsub_of_add_eq ((add_comm _ _).trans hIco)

end RealBraid

/-! ## Examples 3.3(2): the classification of braided families in `ℝ≥0` -/

/-- On a finitely supported family the series sum is the finite sum. -/
theorem coe_finsum_eq_esum {ι : Type u} {z : ι → ℝ≥0} (hz : (Function.support z).Finite) :
    ((∑ᶠ i, z i : ℝ≥0) : ℝ≥0∞) = esum z := by
  have hzc : (Function.support fun i => ((z i : ℝ≥0) : ℝ≥0∞)).Finite := by
    refine Set.Finite.subset hz fun i hi => ?_
    simpa using hi
  rw [esum, tsum_eq_finsum (f := fun i => ((z i : ℝ≥0) : ℝ≥0∞)) hzc]
  exact (ENNReal.ofNNRealHom : ℝ≥0 →+* ℝ≥0∞).toAddMonoidHom.map_finsum hz

theorem esum_ne_top_of_finite_support {ι : Type u} {z : ι → ℝ≥0}
    (hz : (Function.support z).Finite) : esum z ≠ ⊤ := by
  rw [← coe_finsum_eq_esum hz]
  exact ENNReal.coe_ne_top

/-- Two finitely supported families in `ℝ≥0` with the same series sum are braided (Lemma 3.4(1)). -/
theorem isBraided_nnreal_of_finite_support {ι : Type u} (x y : ι → ℝ≥0)
    (hx : (Function.support x).Finite) (hy : (Function.support y).Finite)
    (hsum : esum x = esum y) :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    IsBraided (ℵ₀ : Cardinal.{u}) x y := by
  letI := LMonoid.ofAddCommMonoid ℝ≥0
  have hx' : #(Function.support x) < ℵ₀ := Cardinal.lt_aleph0_iff_set_finite.mpr hx
  have hy' : #(Function.support y) < ℵ₀ := Cardinal.lt_aleph0_iff_set_finite.mpr hy
  refine isBraided_of_small_support x y hx' hy' ?_
  rw [LMonoid.lsumOf_eq_finsum hx' x, LMonoid.lsumOf_eq_finsum hy' y,
    finsum_mem_support, finsum_mem_support]
  -- the finite sums agree because their images in `ℝ≥0∞` are the two series sums
  exact_mod_cast (coe_finsum_eq_esum hx).trans (hsum.trans (coe_finsum_eq_esum hy).symm)

/-- **Examples 3.3(2)**, the substantive half: two families in `ℝ≥0` with infinite support and the
same series sum are `ℵ₀⁻`-braided, over an index type of cardinality at most `ℵ₀`.

As in Examples 3.3(1) the data is built over `ι` directly: transport a bijection `φ : ℕ ≃ ι`, run
the construction of `realBraidState` on `x ∘ φ`, `y ∘ φ`, and place all the pieces at the single
basepoint `φ 0`, carrying the intervals of `ℕ` over to subsets of `ι` as images under `φ`. -/
theorem isBraided_nnreal_of_infinite_support {ι : Type u} (hι : #ι ≤ ℵ₀) (x y : ι → ℝ≥0)
    (hx : (Function.support x).Infinite) (hy : (Function.support y).Infinite)
    (hsum : esum x = esum y) :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    IsBraided (ℵ₀ : Cardinal.{u}) x y := by
  letI := LMonoid.ofAddCommMonoid ℝ≥0
  classical
  have hιInf : Infinite ι := by
    rcases finite_or_infinite ι with hfin | hinf
    · haveI := hfin
      exact absurd (Set.toFinite (Function.support x)) hx
    · exact hinf
  have hUL : #(ULift.{u} ℕ) = ℵ₀ := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
  have h1 : #(ULift.{u} ℕ) ≤ #ι := by rw [hUL]; exact Cardinal.infinite_iff.mp hιInf
  have h2 : #ι ≤ #(ULift.{u} ℕ) := by rw [hUL]; exact hι
  obtain ⟨e0⟩ := Cardinal.eq.mp (le_antisymm h1 h2)
  set φ : ℕ ≃ ι := Equiv.ulift.symm.trans e0 with hφ
  set x3 : ℕ → ℝ≥0 := x ∘ φ with hx3def
  set y3 : ℕ → ℝ≥0 := y ∘ φ with hy3def
  have hx3 : (Function.support x3).Infinite := by
    rw [hx3def, Function.support_comp_eq_preimage]
    intro hfin
    apply hx
    rw [← Set.image_preimage_eq (Function.support x) φ.surjective]
    exact hfin.image _
  have hy3 : (Function.support y3).Infinite := by
    rw [hy3def, Function.support_comp_eq_preimage]
    intro hfin
    apply hy
    rw [← Set.image_preimage_eq (Function.support y) φ.surjective]
    exact hfin.image _
  have hsum3 : esum x3 = esum y3 := by
    rw [hx3def, hy3def, esum_comp_equiv φ x, esum_comp_equiv φ y]
    exact hsum
  have hbI : StrictMono (realBraidBI hx3 hy3 hsum3) :=
    strictMono_nat_of_lt_succ (realBraidBI_lt_succ hx3 hy3 hsum3)
  have hbJ : StrictMono (realBraidBJ hx3 hy3 hsum3) :=
    strictMono_nat_of_lt_succ (realBraidBJ_lt_succ hx3 hy3 hsum3)
  set a₀ : ι := φ 0 with ha₀def
  set I : ι × ℕ → Set ι := fun p =>
    if p.1 = a₀ then
      φ '' Set.Ico (realBraidBI hx3 hy3 hsum3 p.2) (realBraidBI hx3 hy3 hsum3 (p.2 + 1))
    else ∅ with hIdef
  set J : ι × ℕ → Set ι := fun p =>
    if p.1 = a₀ then
      φ '' Set.Ico (realBraidBJ hx3 hy3 hsum3 p.2) (realBraidBJ hx3 hy3 hsum3 (p.2 + 1))
    else ∅ with hJdef
  refine ⟨BraidingData.mk_finsum I J
    (fun p => by
      rw [hIdef]; dsimp only
      split
      · exact (Set.finite_Ico _ _).image _
      · exact Set.finite_empty)
    (fun p => by
      rw [hJdef]; dsimp only
      split
      · exact (Set.finite_Ico _ _).image _
      · exact Set.finite_empty)
    (fun p q hpq => by
      rw [hIdef]; dsimp only
      by_cases hp : p.1 = a₀ <;> by_cases hq : q.1 = a₀
      · rw [if_pos hp, if_pos hq]
        exact Set.disjoint_image_of_injective φ.injective
          (ico_pairwise_disjoint hbI (fun he => hpq (Prod.ext (hp.trans hq.symm) he)))
      · rw [if_pos hp, if_neg hq]; exact disjoint_bot_right
      · rw [if_neg hp, if_pos hq]; exact disjoint_bot_left
      · rw [if_neg hp, if_neg hq]; exact disjoint_bot_left)
    (fun p q hpq => by
      rw [hJdef]; dsimp only
      by_cases hp : p.1 = a₀ <;> by_cases hq : q.1 = a₀
      · rw [if_pos hp, if_pos hq]
        exact Set.disjoint_image_of_injective φ.injective
          (ico_pairwise_disjoint hbJ (fun he => hpq (Prod.ext (hp.trans hq.symm) he)))
      · rw [if_pos hp, if_neg hq]; exact disjoint_bot_right
      · rw [if_neg hp, if_pos hq]; exact disjoint_bot_left
      · rw [if_neg hp, if_neg hq]; exact disjoint_bot_left)
    (Set.eq_univ_of_forall fun i => by
      have hcov := iUnion_Ico_eq_univ_of_strictMono (realBraidBI_zero hx3 hy3 hsum3) hbI
      have hi : φ.symm i ∈
          (⋃ k, Set.Ico (realBraidBI hx3 hy3 hsum3 k) (realBraidBI hx3 hy3 hsum3 (k + 1))) := by
        rw [hcov]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hi
      refine Set.mem_iUnion.mpr ⟨(a₀, k), ?_⟩
      rw [hIdef]; dsimp only
      rw [if_pos rfl]
      exact ⟨φ.symm i, hk, φ.apply_symm_apply i⟩)
    (Set.eq_univ_of_forall fun i => by
      have hcov := iUnion_Ico_eq_univ_of_strictMono (realBraidBJ_zero hx3 hy3 hsum3) hbJ
      have hi : φ.symm i ∈
          (⋃ k, Set.Ico (realBraidBJ hx3 hy3 hsum3 k) (realBraidBJ hx3 hy3 hsum3 (k + 1))) := by
        rw [hcov]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hi
      refine Set.mem_iUnion.mpr ⟨(a₀, k), ?_⟩
      rw [hJdef]; dsimp only
      rw [if_pos rfl]
      exact ⟨φ.symm i, hk, φ.apply_symm_apply i⟩)
    (fun p => if p.1 = a₀ then realBraidU hx3 hy3 hsum3 p.2 else 0)
    (fun p => if p.1 = a₀ then realBraidV hx3 hy3 hsum3 p.2 else 0)
    (fun a => by
      by_cases h : a = a₀
      · simp [h, realBraidV_zero]
      · simp [h])
    (fun p => by
      by_cases hp : p.1 = a₀
      · simp only [hIdef, if_pos hp]
        rw [finsum_mem_image φ.injective.injOn,
          show (Set.Ico (realBraidBI hx3 hy3 hsum3 p.2) (realBraidBI hx3 hy3 hsum3 (p.2 + 1))
                : Set ℕ)
            = (↑(Finset.Ico (realBraidBI hx3 hy3 hsum3 p.2)
                (realBraidBI hx3 hy3 hsum3 (p.2 + 1))) : Set ℕ)
            from (Finset.coe_Ico _ _).symm, finsum_mem_coe_finset]
        exact realBraidBI_sum_eq hx3 hy3 hsum3 p.2
      · simp [hIdef, if_neg hp])
    (fun p => by
      have hfst : (bsucc p).1 = p.1 := rfl
      by_cases hp : p.1 = a₀
      · simp only [hJdef, hfst, if_pos hp]
        rw [finsum_mem_image φ.injective.injOn,
          show (Set.Ico (realBraidBJ hx3 hy3 hsum3 p.2) (realBraidBJ hx3 hy3 hsum3 (p.2 + 1))
              : Set ℕ)
            = (↑(Finset.Ico (realBraidBJ hx3 hy3 hsum3 p.2)
                (realBraidBJ hx3 hy3 hsum3 (p.2 + 1))) : Set ℕ)
            from (Finset.coe_Ico _ _).symm, finsum_mem_coe_finset]
        exact realBraidBJ_sum_eq hx3 hy3 hsum3 p.2
      · simp only [hJdef, hfst, if_neg hp]
        simp)⟩

/-! ### Braided families have the same series sum

Lemma 3.2 applied in the `ℵ₀`-monoid `ℝ≥0∞` of Examples 2.3(2): the inclusion `ℝ≥0 ↪ ℝ≥0∞` is an
`ℵ₀⁻`-homomorphism, and it turns `ℵ₀`-sums into series sums. -/

/-- The inclusion `ℝ≥0 ↪ ℝ≥0∞` is an `ℵ₀⁻`-homomorphism: a `λ⁻`-sum at `λ = ℵ₀` is a finite sum,
which the inclusion preserves. -/
theorem isLHom_coe_ennreal :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    letI : KMonoid (ℵ₀ : Cardinal.{u}) ℝ≥0∞ := ENNRealExample.instKMonoid
    IsLHom (le_refl (ℵ₀ : Cardinal.{u})) (fun a : ℝ≥0 => (a : ℝ≥0∞)) := by
  letI := LMonoid.ofAddCommMonoid ℝ≥0
  letI : KMonoid (ℵ₀ : Cardinal.{u}) ℝ≥0∞ := ENNRealExample.instKMonoid
  refine ⟨rfl, fun {ι} h x => ?_⟩
  haveI : Finite ι := Cardinal.lt_aleph0_iff_finite.mp h
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [LMonoid.lsumOf_aleph0_eq_finsum h x, ENNRealExample.instKMonoid_sumOf h.le, tsum_fintype]
  push_cast
  rfl

/-- The `ℵ₀`-sum of a family of nonnegative reals, computed in `ℝ≥0∞`, is its series sum. -/
theorem sumOf_coe_eq_esum {ι : Type u} (hι : #ι ≤ (ℵ₀ : Cardinal.{u})) (x : ι → ℝ≥0) :
    letI : KMonoid (ℵ₀ : Cardinal.{u}) ℝ≥0∞ := ENNRealExample.instKMonoid
    KMonoid.sumOf (κ := (ℵ₀ : Cardinal.{u})) hι (fun i => ((x i : ℝ≥0) : ℝ≥0∞)) = esum x := rfl

/-- Braided families in `ℝ≥0` have the same series sum. -/
theorem esum_eq_of_isBraided {ι : Type u} (hι : #ι ≤ (ℵ₀ : Cardinal.{u})) {x y : ι → ℝ≥0}
    (h : letI := LMonoid.ofAddCommMonoid ℝ≥0
      IsBraided (ℵ₀ : Cardinal.{u}) x y) : esum x = esum y := by
  letI := LMonoid.ofAddCommMonoid ℝ≥0
  letI : KMonoid (ℵ₀ : Cardinal.{u}) ℝ≥0∞ := ENNRealExample.instKMonoid
  have hb := sumOf_map_eq_of_isBraided (le_refl (ℵ₀ : Cardinal.{u})) isLHom_coe_ennreal hι h
  exact (sumOf_coe_eq_esum hι x).symm.trans (hb.trans (sumOf_coe_eq_esum hι y))

/-- `ℝ≥0` is reduced. -/
theorem isConical_nnreal : IsConical ℝ≥0 := fun _ _ h => add_eq_zero.mp h

/-! ### Examples 3.3(2): the classification -/

/-- **Examples 3.3(2)**: two families in `ℝ≥0`, over an index type of cardinality at most `ℵ₀`, are
`ℵ₀⁻`-braided exactly when they have the same series sum and their supports are either both finite
or both infinite.

The support condition is forced: braidedness preserves smallness of support in a reduced monoid
(`IsBraided.mk_support_lt`), and it is symmetric. -/
theorem isBraided_nnreal_iff {ι : Type u} (hι : #ι ≤ (ℵ₀ : Cardinal.{u})) (x y : ι → ℝ≥0) :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    IsBraided (ℵ₀ : Cardinal.{u}) x y ↔
      (esum x = esum y ∧ ((Function.support x).Finite ↔ (Function.support y).Finite)) := by
  letI := LMonoid.ofAddCommMonoid ℝ≥0
  constructor
  · intro h
    refine ⟨esum_eq_of_isBraided hι h, ?_⟩
    constructor
    · intro hxfin
      exact Cardinal.lt_aleph0_iff_set_finite.mp
        (h.mk_support_lt isConical_nnreal (Cardinal.lt_aleph0_iff_set_finite.mpr hxfin))
    · intro hyfin
      exact Cardinal.lt_aleph0_iff_set_finite.mp
        (h.symm.mk_support_lt isConical_nnreal (Cardinal.lt_aleph0_iff_set_finite.mpr hyfin))
  · rintro ⟨hsum, hfin⟩
    by_cases hx : (Function.support x).Finite
    · exact isBraided_nnreal_of_finite_support x y hx (hfin.mp hx) hsum
    · exact isBraided_nnreal_of_infinite_support hι x y hx (fun hc => hx (hfin.mpr hc)) hsum

/-! ### Neither `ℵ₀`-monoid structure on `ℝ≥0 ∪ {∞}` is braided over `ℝ≥0`

A positive real is the sum of a finitely supported family and also of an infinitely supported one,
and by the classification those two families are not braided.  For `ℝ≥0∞` they nevertheless have
the same `ℵ₀`-sum, so `braided` fails; for the trivial extension the witness is instead a pair of
infinitely supported families with different series sums, both of which sum to `∞`. -/

/-- The geometric family `(2⁻¹)^n`: infinite support, series sum `2`. -/
noncomputable def geom (n : ℕ) : ℝ≥0 := (2⁻¹ : ℝ≥0) ^ n

theorem geom_ne_zero (n : ℕ) : geom n ≠ 0 := by
  rw [geom]
  positivity

theorem support_geom : Function.support geom = Set.univ :=
  Set.eq_univ_of_forall fun n => geom_ne_zero n

theorem infinite_support_geom : (Function.support geom).Infinite := by
  rw [support_geom]
  exact Set.infinite_univ

theorem esum_geom : esum geom = 2 := by
  have hcoe : ∀ n, ((geom n : ℝ≥0) : ℝ≥0∞) = ((2⁻¹ : ℝ≥0∞)) ^ n := by
    intro n
    rw [geom]
    push_cast
    norm_num
  rw [esum, tsum_congr hcoe, ENNReal.tsum_geometric]
  norm_num

/-- Twice the geometric family: infinite support, series sum `4`. -/
theorem esum_two_geom : esum (fun n => 2 * geom n) = 4 := by
  have hcoe : ∀ n, ((2 * geom n : ℝ≥0) : ℝ≥0∞) = 2 * ((geom n : ℝ≥0) : ℝ≥0∞) := by
    intro n
    push_cast
    rfl
  rw [esum, tsum_congr hcoe, ENNReal.tsum_mul_left]
  rw [show ∑' n, ((geom n : ℝ≥0) : ℝ≥0∞) = 2 from esum_geom]
  norm_num

theorem infinite_support_two_geom : (Function.support fun n => 2 * geom n).Infinite := by
  have hsupp : (Function.support fun n => 2 * geom n) = Set.univ :=
    Set.eq_univ_of_forall fun n => by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or]
      exact ⟨two_ne_zero, geom_ne_zero n⟩
  rw [hsupp]
  exact Set.infinite_univ

/-- The single-entry family with value `2`: finite support, series sum `2`. -/
noncomputable def single2 (n : ℕ) : ℝ≥0 := if n = 0 then 2 else 0

theorem finite_support_single2 : (Function.support single2).Finite := by
  refine Set.Finite.subset (Set.finite_singleton 0) fun n hn => ?_
  simp only [Set.mem_singleton_iff]
  by_contra hne
  exact hn (by simp [single2, hne])

theorem esum_single2 : esum single2 = 2 := by
  classical
  rw [esum, tsum_eq_single 0 fun n hn => by simp [single2, hn]]
  simp [single2]

/-- **Examples 3.3(2)**: the two families `single2` and `geom` witness that `ℝ≥0∞` — the
`ℵ₀`-monoid structure of Examples 2.3(2) on `ℝ≥0 ∪ {∞}` — is *not* `ℵ₀⁻`-braided over `ℝ≥0`: they
have the same `ℵ₀`-sum but different support behaviour, so they are not braided. -/
theorem not_isBraided_single2_geom :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    ¬ IsBraided (ℵ₀ : Cardinal.{0}) single2 geom := by
  letI := LMonoid.ofAddCommMonoid ℝ≥0
  intro h
  have hfin := ((isBraided_nnreal_iff (le_of_eq Cardinal.mk_nat) single2 geom).mp h).2
  exact infinite_support_geom (hfin.mp finite_support_single2)

/-- **Examples 3.3(2)**: `geom` and `2 · geom` witness that the *trivial* `ℵ₀`-extension of `ℝ≥0`
(Examples 2.3(1)) is not `ℵ₀⁻`-braided over `ℝ≥0` either: both families have infinite support, so
both sum to `∞` there, but their series sums differ, so they are not braided. -/
theorem not_isBraided_geom_two_geom :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    ¬ IsBraided (ℵ₀ : Cardinal.{0}) geom (fun n => 2 * geom n) := by
  letI := LMonoid.ofAddCommMonoid ℝ≥0
  intro h
  have hsum := esum_eq_of_isBraided (le_of_eq Cardinal.mk_nat) h
  rw [esum_geom, esum_two_geom] at hsum
  norm_num at hsum

/-! ## Examples 3.3(2): the `ℵ₀`-monoid `H = ℝ≥0 ∪ ℝ̃>0 ∪ {∞}`

The paper's construction.  An element is a value in `ℝ≥0∞` together with a tilde flag, where only a
value that is neither `0` nor `∞` may carry the flag — so there is exactly one `0` and one `∞`, as
required.  The `ℵ₀`-sum of a family is the series sum of the values, marked with a tilde unless the
family is plain and finitely supported: the flag records that the sum was reached only with
infinite support, or from a tilded summand. -/

/-- The carrier `H = ℝ≥0 ∪ ℝ̃>0 ∪ {∞}` of Examples 3.3(2). -/
def RTilde : Type := {p : ℝ≥0∞ × Bool // p.2 = true → p.1 ≠ 0 ∧ p.1 ≠ ⊤}

namespace RTilde

/-- The underlying value in `ℝ≥0∞`. -/
def val (h : RTilde) : ℝ≥0∞ := h.1.1

/-- Whether the element lies in the tilde copy `ℝ̃>0`. -/
def tilded (h : RTilde) : Bool := h.1.2

theorem ext {h h' : RTilde} (hv : h.val = h'.val) (ht : h.tilded = h'.tilded) : h = h' :=
  Subtype.ext (Prod.ext hv ht)

theorem val_ne_zero {h : RTilde} (ht : h.tilded = true) : h.val ≠ 0 := (h.2 ht).1

theorem val_ne_top {h : RTilde} (ht : h.tilded = true) : h.val ≠ ⊤ := (h.2 ht).2

/-- The plain copy of `ℝ≥0`. -/
def ofReal (a : ℝ≥0) : RTilde := ⟨(a, false), by simp⟩

/-- The tilde copy of `ℝ>0`. -/
def tilde (a : ℝ≥0) (ha : a ≠ 0) : RTilde :=
  ⟨(a, true), fun _ => ⟨by simpa using ha, ENNReal.coe_ne_top⟩⟩

/-- The element `∞`. -/
def top : RTilde := ⟨(⊤, false), by simp⟩

instance : Zero RTilde := ⟨ofReal 0⟩

@[simp] theorem val_ofReal (a : ℝ≥0) : (ofReal a).val = (a : ℝ≥0∞) := rfl

@[simp] theorem tilded_ofReal (a : ℝ≥0) : (ofReal a).tilded = false := rfl

@[simp] theorem val_tilde (a : ℝ≥0) (ha : a ≠ 0) : (tilde a ha).val = (a : ℝ≥0∞) := rfl

@[simp] theorem tilded_tilde (a : ℝ≥0) (ha : a ≠ 0) : (tilde a ha).tilded = true := rfl

@[simp] theorem val_top : (top : RTilde).val = ⊤ := rfl

@[simp] theorem tilded_top : (top : RTilde).tilded = false := rfl

@[simp] theorem val_zero : (0 : RTilde).val = 0 := rfl

@[simp] theorem tilded_zero : (0 : RTilde).tilded = false := rfl

/-- The tilde copy omits `0`, so `0` is the only element of value `0`. -/
theorem eq_zero_of_val_eq_zero {h : RTilde} (hv : h.val = 0) : h = 0 := by
  refine ext hv ?_
  cases ht : h.tilded with
  | false => rfl
  | true => exact absurd hv (val_ne_zero ht)

theorem val_eq_zero_iff {h : RTilde} : h.val = 0 ↔ h = 0 :=
  ⟨eq_zero_of_val_eq_zero, fun h => by rw [h, val_zero]⟩

/-- There is only one element of value `∞`. -/
theorem eq_top_of_val_eq_top {h : RTilde} (hv : h.val = ⊤) : h = top := by
  refine ext hv ?_
  cases ht : h.tilded with
  | false => rfl
  | true => exact absurd hv (val_ne_top ht)

/-- Equality of the flags follows from their equality as propositions. -/
theorem tilded_eq_of_iff {h h' : RTilde} (hiff : h.tilded = false ↔ h'.tilded = false) :
    h.tilded = h'.tilded := by
  cases hh : h.tilded <;> cases hh' : h'.tilded <;> simp_all

/-! ### The summation -/

/-- A family stays in the plain copy exactly when every entry does and only finitely many entries
are nonzero. -/
def IsPlain {ι : Type u} (x : ι → RTilde) : Prop :=
  (∀ i, (x i).tilded = false) ∧ (Function.support x).Finite

/-- If a family is not plain, then some entry — a tilded one, or one of the infinitely many nonzero
ones — has nonzero value, so the total is nonzero. -/
theorem tsum_val_ne_zero {ι : Type u} {x : ι → RTilde} (hpl : ¬ IsPlain x) :
    (∑' i, (x i).val) ≠ 0 := by
  intro h0
  have hz : ∀ i, x i = 0 := fun i => eq_zero_of_val_eq_zero (ENNReal.tsum_eq_zero.mp h0 i)
  refine hpl ⟨fun i => by rw [hz i, tilded_zero], ?_⟩
  have hsupp : Function.support x = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun i hi => hi (hz i)
  rw [hsupp]
  exact Set.finite_empty

/-- The tilde flag of an `ℵ₀`-sum: set unless the total is `∞` — where the answer is the single
element `∞` — or the family is plain and finitely supported. -/
noncomputable def sigmaFlag {ι : Type u} (x : ι → RTilde) : Bool :=
  if (∑' i, (x i).val) = ⊤ ∨ IsPlain x then false else true

theorem sigmaFlag_eq_false_iff {ι : Type u} (x : ι → RTilde) :
    sigmaFlag x = false ↔ ((∑' i, (x i).val) = ⊤ ∨ IsPlain x) := by
  unfold sigmaFlag
  by_cases h : (∑' i, (x i).val) = ⊤ ∨ IsPlain x
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun hc => absurd hc (by simp), fun hc => absurd hc h⟩

/-- The `ℵ₀`-summation of `H`: the series sum of the values, tilded unless the family is plain and
finitely supported. -/
noncomputable def sigma {ι : Type u} (x : ι → RTilde) : RTilde :=
  ⟨(∑' i, (x i).val, sigmaFlag x), fun ht => by
    have ht' : sigmaFlag x = true := ht
    have h := (sigmaFlag_eq_false_iff x).not.mp (by simp [ht'])
    exact ⟨tsum_val_ne_zero fun hp => h (Or.inr hp), fun hc => h (Or.inl hc)⟩⟩

@[simp] theorem val_sigma {ι : Type u} (x : ι → RTilde) : (sigma x).val = ∑' i, (x i).val := rfl

@[simp] theorem tilded_sigma {ι : Type u} (x : ι → RTilde) : (sigma x).tilded = sigmaFlag x := rfl

/-- The result is plain exactly when the family was, the case of an infinite total aside. -/
theorem tilded_sigma_eq_false_iff {ι : Type u} (x : ι → RTilde) :
    (sigma x).tilded = false ↔ ((∑' i, (x i).val) = ⊤ ∨ IsPlain x) :=
  sigmaFlag_eq_false_iff x

/-- A family whose values sum to `∞` sums to `∞`. -/
theorem sigma_of_val_eq_top {ι : Type u} {x : ι → RTilde} (htop : (∑' i, (x i).val) = ⊤) :
    sigma x = top := by
  refine ext (by rw [val_sigma, htop, val_top]) ?_
  rw [tilded_top]
  exact (tilded_sigma_eq_false_iff x).mpr (Or.inl htop)

theorem sigma_eq_zero_iff {ι : Type u} (x : ι → RTilde) : sigma x = 0 ↔ ∀ i, x i = 0 := by
  rw [← val_eq_zero_iff, val_sigma, ENNReal.tsum_eq_zero]
  exact ⟨fun h i => eq_zero_of_val_eq_zero (h i), fun h i => by rw [h i, val_zero]⟩

/-! ### The three axioms -/

theorem sigma_comp_equiv {ι ι' : Type u} (e : ι ≃ ι') (x : ι' → RTilde) :
    sigma (x ∘ e) = sigma x := by
  have hval : (∑' i, ((x ∘ e) i).val) = ∑' i', (x i').val := e.tsum_eq fun i' => (x i').val
  have hsupp : Function.support (x ∘ e) = e ⁻¹' Function.support x := rfl
  have hpl : IsPlain (x ∘ e) ↔ IsPlain x := by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i' => by rw [← e.apply_symm_apply i']; exact h1 (e.symm i'), ?_⟩
      rw [← Set.image_preimage_eq (Function.support x) e.surjective, ← hsupp]
      exact h2.image _
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => h1 (e i), ?_⟩
      rw [hsupp]
      exact h2.preimage e.injective.injOn
  refine ext (by rw [val_sigma, val_sigma, hval]) (tilded_eq_of_iff ?_)
  rw [tilded_sigma_eq_false_iff, tilded_sigma_eq_false_iff, hval]
  exact or_congr Iff.rfl hpl

theorem sigma_unique {ι : Type u} [Unique ι] (x : ι → RTilde) : sigma x = x default := by
  have hval : (∑' i, (x i).val) = (x default).val :=
    tsum_eq_single default fun i hi => absurd (Unique.eq_default i) hi
  refine ext (by rw [val_sigma, hval]) (tilded_eq_of_iff ?_)
  rw [tilded_sigma_eq_false_iff, hval]
  constructor
  · rintro (htop | ⟨h1, _⟩)
    · cases ht : (x default).tilded with
      | false => rfl
      | true => exact absurd htop (val_ne_top ht)
    · exact h1 default
  · intro hd
    refine Or.inr ⟨fun i => by rw [Unique.eq_default i]; exact hd, ?_⟩
    exact Set.toFinite _

/-- The row sums of a family with finite total are themselves finite. -/
theorem tsum_row_ne_top {ι : Type u} {ρ : ι → Type u} (x : ∀ i, ρ i → RTilde)
    (htop : (∑' p : (i : ι) × ρ i, (x p.1 p.2).val) ≠ ⊤) (i : ι) :
    (∑' j, (x i j).val) ≠ ⊤ := by
  refine fun hrow => htop ?_
  have hle : (∑' j, (x i j).val) ≤ ∑' i', ∑' j, (x i' j).val :=
    ENNReal.le_tsum i
  rw [← ENNReal.tsum_sigma fun i j => (x i j).val] at hle
  exact top_unique (hrow ▸ hle)

/-- The key compatibility: for a family with finite total, the family of row sums is plain exactly
when the whole double family is.  This is what makes the marking of `sigma` associative. -/
theorem isPlain_sigma_iff {ι : Type u} {ρ : ι → Type u} (x : ∀ i, ρ i → RTilde)
    (htop : (∑' p : (i : ι) × ρ i, (x p.1 p.2).val) ≠ ⊤) :
    IsPlain (fun i => sigma (x i)) ↔ IsPlain (fun p : (i : ι) × ρ i => x p.1 p.2) := by
  classical
  have hrow : ∀ i, (∑' j, (x i j).val) ≠ ⊤ := tsum_row_ne_top x htop
  have hrowpl : ∀ i, (sigma (x i)).tilded = false ↔ IsPlain (x i) := by
    intro i
    rw [tilded_sigma_eq_false_iff]
    exact ⟨fun h => h.elim (fun hc => absurd hc (hrow i)) id, Or.inr⟩
  constructor
  · rintro ⟨h1, h2⟩
    have hrowpl' : ∀ i, IsPlain (x i) := fun i => (hrowpl i).mp (h1 i)
    refine ⟨fun p => (hrowpl' p.1).1 p.2, ?_⟩
    refine Set.Finite.subset (Set.Finite.biUnion h2 fun i _ =>
      ((hrowpl' i).2.image (fun j : ρ i => (⟨i, j⟩ : (i : ι) × ρ i)))) ?_
    rintro ⟨i, j⟩ hij
    refine Set.mem_biUnion (show i ∈ Function.support fun i => sigma (x i) from ?_) ⟨j, hij, rfl⟩
    intro hcon
    exact hij ((sigma_eq_zero_iff (x i)).mp hcon j)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (hrowpl i).mpr ⟨fun j => h1 ⟨i, j⟩, ?_⟩, ?_⟩
    · refine Set.Finite.of_finite_image (f := fun j : ρ i => (⟨i, j⟩ : (i : ι) × ρ i)) ?_ ?_
      · refine Set.Finite.subset h2 ?_
        rintro _ ⟨j, hj, rfl⟩
        exact hj
      · exact Set.injOn_of_injective fun a b hab => by simpa using hab
    · refine Set.Finite.subset (h2.image Sigma.fst) ?_
      intro i hi
      obtain ⟨j, hj⟩ := not_forall.mp (fun hc => hi ((sigma_eq_zero_iff (x i)).mpr hc))
      exact ⟨⟨i, j⟩, hj, rfl⟩

theorem sigma_sigma {ι : Type u} {ρ : ι → Type u} (x : ∀ i, ρ i → RTilde) :
    sigma (fun i => sigma (x i)) = sigma (fun p : (i : ι) × ρ i => x p.1 p.2) := by
  have hvals : (∑' i, (sigma (x i)).val) = ∑' p : (i : ι) × ρ i, (x p.1 p.2).val := by
    rw [tsum_congr fun i => val_sigma (x i)]
    exact (ENNReal.tsum_sigma fun i j => (x i j).val).symm
  refine ext (by rw [val_sigma, val_sigma, hvals]) (tilded_eq_of_iff ?_)
  rw [tilded_sigma_eq_false_iff, tilded_sigma_eq_false_iff, hvals]
  by_cases htop : (∑' p : (i : ι) × ρ i, (x p.1 p.2).val) = ⊤
  · simp [htop]
  · exact or_congr Iff.rfl (isPlain_sigma_iff x htop)

/-! ### `H` as an `ℵ₀`-monoid -/

/-- `Σ` on `H`. -/
noncomputable def sumData : SumData (Order.succ (ℵ₀ : Cardinal.{u})) RTilde where
  isRegular := Cardinal.isRegular_succ le_rfl
  sum _ x := sigma x
  sum_congr _ _ e x := sigma_comp_equiv e x
  sum_unique := fun {ι} _ _ x => sigma_unique x
  sum_sigma _ _ x _ := sigma_sigma x

theorem sumData_zero :
    (sumData : SumData (Order.succ (ℵ₀ : Cardinal.{u})) RTilde).zero = 0 := by
  show sigma (PEmpty.elim : PEmpty.{u + 1} → RTilde) = 0
  refine (sigma_eq_zero_iff _).mpr fun i => i.elim

/-- **Examples 3.3(2)**: `H = ℝ≥0 ∪ ℝ̃>0 ∪ {∞}` is an `ℵ₀`-monoid. -/
@[instance_reducible]
noncomputable def instKMonoid : KMonoid (ℵ₀ : Cardinal.{u}) RTilde where
  toLMonoid := sumData.toLMonoidOfZero sumData_zero
  aleph0_le := le_rfl

/-- The `ℵ₀`-sum of `H` is `sigma`. -/
@[simp] theorem instKMonoid_sumOf {ι : Type u} (h : #ι ≤ (ℵ₀ : Cardinal.{u})) (x : ι → RTilde) :
    letI := instKMonoid
    KMonoid.sumOf (κ := (ℵ₀ : Cardinal.{u})) h x = sigma x := rfl

/-- Addition on `H` adds the values. -/
theorem val_add (a b : RTilde) :
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
    (a + b).val = a.val + b.val := by
  letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
  show (sigma (Sum.elim (fun _ : PUnit.{u + 1} => a) (fun _ : PUnit.{u + 1} => b))).val = _
  rw [val_sigma, tsum_fintype]
  simp

/-- `H` is reduced. -/
theorem isConical :
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
    IsConical RTilde := by
  letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
  intro a b hab
  have hval : a.val + b.val = 0 := by
    rw [← val_add a b, hab, val_zero]
  obtain ⟨h1, h2⟩ := add_eq_zero.mp hval
  exact ⟨eq_zero_of_val_eq_zero h1, eq_zero_of_val_eq_zero h2⟩

/-! ### `H` is `ℵ₀⁻`-braided over `ℝ≥0` -/

theorem support_ofReal_comp {ι : Type u} (x : ι → ℝ≥0) :
    Function.support (fun i => ofReal (x i)) = Function.support x := by
  ext i
  simp only [Function.mem_support, ne_eq, ← val_eq_zero_iff, val_ofReal]
  exact ⟨fun h hc => h (by rw [hc]; rfl), fun h hc => h (by exact_mod_cast hc)⟩

theorem tsum_val_ofReal_comp {ι : Type u} (x : ι → ℝ≥0) :
    (∑' i, (ofReal (x i)).val) = esum x := rfl

theorem isPlain_ofReal_comp_iff {ι : Type u} (x : ι → ℝ≥0) :
    IsPlain (fun i => ofReal (x i)) ↔ (Function.support x).Finite := by
  rw [IsPlain, support_ofReal_comp]
  exact ⟨fun h => h.2, fun h => ⟨fun _ => rfl, h⟩⟩

/-- The `ℵ₀`-sum of a family from the plain copy: its value is the series sum, and it is tilded
exactly when the family is not finitely supported (the total being finite). -/
theorem sigma_ofReal_comp {ι : Type u} (x : ι → ℝ≥0) :
    (sigma fun i => ofReal (x i)).val = esum x ∧
      ((sigma fun i => ofReal (x i)).tilded = false ↔
        (esum x = ⊤ ∨ (Function.support x).Finite)) := by
  refine ⟨rfl, ?_⟩
  rw [tilded_sigma_eq_false_iff, tsum_val_ofReal_comp, isPlain_ofReal_comp_iff]

/-- A geometric family with prescribed series sum `a`. -/
noncomputable def geomTo (a : ℝ≥0) (n : ℕ) : ℝ≥0 := (a * 2⁻¹) * (2⁻¹) ^ n

theorem esum_geomTo (a : ℝ≥0) : esum (geomTo a) = (a : ℝ≥0∞) := by
  have hcoe : ∀ n, ((geomTo a n : ℝ≥0) : ℝ≥0∞)
      = ((a : ℝ≥0∞) * 2⁻¹) * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    rw [geomTo]
    push_cast
    norm_num
  rw [esum, tsum_congr hcoe, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    show ((1 : ℝ≥0∞) - 2⁻¹)⁻¹ = 2 by norm_num, mul_assoc,
    show (2⁻¹ : ℝ≥0∞) * 2 = 1 from ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

theorem infinite_support_geomTo {a : ℝ≥0} (ha : a ≠ 0) :
    (Function.support (geomTo a)).Infinite := by
  have hsupp : Function.support (geomTo a) = Set.univ := by
    refine Set.eq_univ_of_forall fun n => ?_
    simp only [Function.mem_support, geomTo, ne_eq, mul_eq_zero, not_or]
    refine ⟨⟨ha, by norm_num⟩, ?_⟩
    positivity
  rw [hsupp]
  exact Set.infinite_univ

/-- **Examples 3.3(2)**: `H = ℝ≥0 ∪ ℝ̃>0 ∪ {∞}` is `ℵ₀⁻`-braided over `ℝ≥0`, along the inclusion of
the plain copy.

The three generation cases are the paper's three kinds of element: a plain `a` is a one-term sum,
a tilded `ã` is the sum of a geometric family with sum `a` — which has infinite support, hence gets
the tilde — and `∞` is the sum of infinitely many `1`s.  Braidedness is the classification
`isBraided_nnreal_iff`: equal `ℵ₀`-sums in `H` say exactly that the series sums agree *and* that
the two families are simultaneously finitely supported. -/
theorem isBraidedOver_rtilde :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
    IsBraidedOver (ℵ₀ : Cardinal.{u}) ℵ₀ ℝ≥0 RTilde le_rfl ofReal := by
  letI := LMonoid.ofAddCommMonoid ℝ≥0
  letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
  classical
  -- a countable index type for the two infinite constructions
  have hUL : #(ULift.{u} ℕ) = #(Idx (ℵ₀ : Cardinal.{u})) := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0, mk_Idx]
  obtain ⟨e0⟩ := Cardinal.eq.mp hUL
  set e : ℕ ≃ Idx (ℵ₀ : Cardinal.{u}) := Equiv.ulift.symm.trans e0 with hedef
  refine ⟨⟨rfl, fun {ι} h x => ?_⟩, fun a b hab => ?_, fun h => ?_, fun x y hxy => ?_⟩
  · -- the inclusion is an `ℵ₀⁻`-homomorphism
    haveI : Finite ι := Cardinal.lt_aleph0_iff_finite.mp h
    haveI : Fintype ι := Fintype.ofFinite ι
    have hfin : (Function.support x).Finite := Set.toFinite _
    have hgoal : ofReal (lsumOf (lam := (ℵ₀ : Cardinal.{u})) h x)
        = sigma (fun i => ofReal (x i)) := by
      refine ext ?_ ?_
      · rw [val_ofReal, val_sigma, tsum_val_ofReal_comp, esum, tsum_fintype,
          LMonoid.lsumOf_aleph0_eq_finsum h x]
        push_cast
        rfl
      · rw [tilded_ofReal]
        exact ((sigma_ofReal_comp x).2.mpr (Or.inr hfin)).symm
    exact hgoal
  · -- injectivity
    have hv := congrArg val hab
    rw [val_ofReal, val_ofReal] at hv
    exact_mod_cast hv
  · -- `ℝ≥0` generates `H`
    by_cases htop : h.val = ⊤
    · -- `∞` is the sum of infinitely many `1`s
      refine ⟨fun _ => 1, ?_⟩
      rw [eq_top_of_val_eq_top htop]
      refine (sigma_of_val_eq_top ?_).symm
      haveI : Infinite (Idx (ℵ₀ : Cardinal.{u})) := infinite_Idx le_rfl
      show (∑' _ : Idx (ℵ₀ : Cardinal.{u}), ((1 : ℝ≥0) : ℝ≥0∞)) = ⊤
      simpa using ENNReal.tsum_const_eq_top_of_ne_zero (α := Idx (ℵ₀ : Cardinal.{u}))
        (c := ((1 : ℝ≥0) : ℝ≥0∞)) (by simp)
    · -- a finite value: one term if plain, a geometric family if tilded
      set a : ℝ≥0 := h.val.toNNReal with hadef
      have ha : ((a : ℝ≥0) : ℝ≥0∞) = h.val := ENNReal.coe_toNNReal htop
      cases hfl : h.tilded with
      | false =>
          obtain ⟨i₀⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
          refine ⟨fun i => if i = i₀ then a else 0, ?_⟩
          have hks : (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{u}))
              fun i => ofReal (if i = i₀ then a else 0)) = ofReal a := by
            rw [KMonoid.ksum_single i₀ _ fun i hi => by rw [if_neg hi]; rfl, if_pos rfl]
          have hval : ofReal a = h :=
            ext (by rw [val_ofReal]; exact ha) (by rw [tilded_ofReal, hfl])
          exact (hks.trans hval).symm
      | true =>
          have ha0 : a ≠ 0 := by
            intro hc
            refine val_ne_zero hfl ?_
            rw [← ha, hc]
            simp
          refine ⟨fun i => geomTo a (e.symm i), ?_⟩
          have hesum : esum (fun i => geomTo a (e.symm i)) = h.val := by
            rw [show esum (fun i => geomTo a (e.symm i)) = esum (geomTo a) from
              esum_comp_equiv e.symm (geomTo a), esum_geomTo, ha]
          have hinf : ¬ (Function.support fun i => geomTo a (e.symm i)).Finite := by
            intro hc
            refine infinite_support_geomTo ha0 ?_
            have himg : Function.support (fun i => geomTo a (e.symm i))
                = e '' Function.support (geomTo a) := by
              ext i
              simp only [Function.mem_support, Set.mem_image]
              constructor
              · intro hne
                exact ⟨e.symm i, hne, e.apply_symm_apply i⟩
              · rintro ⟨n, hn, rfl⟩
                simpa [e.symm_apply_apply] using hn
            rw [himg] at hc
            exact Set.Finite.of_finite_image hc e.injective.injOn
          rw [show (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{u}))
              fun i => ofReal (geomTo a (e.symm i)))
            = sigma (fun i => ofReal (geomTo a (e.symm i))) from rfl]
          refine (ext ?_ ?_).symm
          · rw [val_sigma, tsum_val_ofReal_comp, hesum]
          · rw [hfl]
            cases hs : (sigma fun i => ofReal (geomTo a (e.symm i))).tilded with
            | false =>
                rcases (sigma_ofReal_comp _).2.mp hs with hc | hc
                · rw [hesum] at hc
                  exact absurd hc htop
                · exact absurd hc hinf
            | true => rfl
  · -- families with equal `ℵ₀`-sums are braided
    have hxy' : sigma (fun i => ofReal (x i)) = sigma (fun i => ofReal (y i)) := hxy
    have hval : esum x = esum y := by
      have hv := congrArg val hxy'
      rw [val_sigma, val_sigma, tsum_val_ofReal_comp, tsum_val_ofReal_comp] at hv
      exact hv
    refine (isBraided_nnreal_iff (le_of_eq (mk_Idx _)) x y).mpr ⟨hval, ?_⟩
    have hfl := congrArg tilded hxy'
    by_cases htop : esum x = ⊤
    · -- neither family can be finitely supported
      exact ⟨fun hc => absurd htop (esum_ne_top_of_finite_support hc),
        fun hc => absurd (hval ▸ htop : esum y = ⊤) (esum_ne_top_of_finite_support hc)⟩
    · -- otherwise the flags read off finiteness of the supports
      have hx := (sigma_ofReal_comp x).2
      have hy := (sigma_ofReal_comp y).2
      constructor
      · intro hc
        rcases hy.mp (hfl ▸ hx.mpr (Or.inr hc)) with hcc | hcc
        · exact absurd (hval.trans hcc) htop
        · exact hcc
      · intro hc
        rcases hx.mp (hfl.symm ▸ hy.mpr (Or.inr hc)) with hcc | hcc
        · exact absurd hcc htop
        · exact hcc

/-- **Examples 3.12** for `ℝ≥0`: by Theorem 3.11(2) the universal `ℵ₀`-extension of `ℝ≥0` is
`ℝ≥0 ∪ ℝ̃>0 ∪ {∞}`. -/
theorem isUniversalKExtension_rtilde :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
    IsUniversalKExtension (ℵ₀ : Cardinal.{u}) ℵ₀ ℝ≥0 RTilde le_rfl ofReal := by
  letI := LMonoid.ofAddCommMonoid ℝ≥0
  letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
  exact isBraidedOver_rtilde.isUniversalKExtension le_rfl

/-! ### `H` is not `ℵ₀⁻`-braided over itself

The paper's last remark in Examples 3.3(2): repeat the argument that defeated `ℝ≥0 ∪ {∞}`, with
`{0} ∪ ℝ̃>0` in place of `ℝ≥0`.  A single tilded `2̃` and a tilded geometric family have the same
`ℵ₀`-sum `2̃`, but one has finite and the other infinite support, so they are not braided. -/

theorem tilde_ne_zero (a : ℝ≥0) (ha : a ≠ 0) : tilde a ha ≠ 0 := by
  intro hc
  exact val_ne_zero (tilded_tilde a ha) (by rw [hc, val_zero])

/-- **Examples 3.3(2)**, last claim: `H` is not `ℵ₀⁻`-braided over itself — there are two families
in `H` with the same `ℵ₀`-sum that are not `ℵ₀⁻`-braided. -/
theorem not_isBraidedOver_rtilde_self :
    letI : KMonoid (ℵ₀ : Cardinal.{0}) RTilde := instKMonoid
    letI := KMonoid.toLMonoidOfLE RTilde Cardinal.isRegular_aleph0 (le_refl (ℵ₀ : Cardinal.{0}))
    ¬ IsBraidedOver (ℵ₀ : Cardinal.{0}) ℵ₀ RTilde RTilde le_rfl id := by
  letI : KMonoid (ℵ₀ : Cardinal.{0}) RTilde := instKMonoid
  letI := KMonoid.toLMonoidOfLE RTilde Cardinal.isRegular_aleph0 (le_refl (ℵ₀ : Cardinal.{0}))
  intro hbr
  classical
  -- a countable index type
  have hUL : #(ULift.{0} ℕ) = #(Idx (ℵ₀ : Cardinal.{0})) := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0, mk_Idx]
  obtain ⟨e0⟩ := Cardinal.eq.mp hUL
  set e : ℕ ≃ Idx (ℵ₀ : Cardinal.{0}) := Equiv.ulift.symm.trans e0 with hedef
  obtain ⟨i₀⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{0}))
  have h2 : (2 : ℝ≥0) ≠ 0 := two_ne_zero
  -- the single tilded `2̃`, and the tilded geometric family
  set X : Idx (ℵ₀ : Cardinal.{0}) → RTilde :=
    fun i => if i = i₀ then tilde 2 h2 else 0 with hXdef
  set Y : Idx (ℵ₀ : Cardinal.{0}) → RTilde :=
    fun i => tilde (geom (e.symm i)) (geom_ne_zero _) with hYdef
  -- both have `ℵ₀`-sum `2̃`
  have hXsum : KMonoid.ksum (κ := (ℵ₀ : Cardinal.{0})) X = tilde 2 h2 := by
    rw [hXdef, KMonoid.ksum_single i₀ _ fun i hi => if_neg hi, if_pos rfl]
  have hYsum : KMonoid.ksum (κ := (ℵ₀ : Cardinal.{0})) Y = tilde 2 h2 := by
    have hks : (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{0})) Y) = sigma Y := rfl
    have hval : (∑' i, (Y i).val) = 2 := by
      rw [hYdef]
      show (∑' i, ((geom (e.symm i) : ℝ≥0) : ℝ≥0∞)) = 2
      rw [show (∑' i, ((geom (e.symm i) : ℝ≥0) : ℝ≥0∞)) = esum (geom ∘ e.symm) from rfl,
        esum_comp_equiv e.symm geom, esum_geom]
    rw [hks]
    refine ext ?_ ?_
    · rw [val_sigma, hval, val_tilde]
      norm_num
    · rw [tilded_tilde]
      cases hs : (sigma Y).tilded with
      | false =>
          rcases (tilded_sigma_eq_false_iff Y).mp hs with hc | hc
          · rw [hval] at hc
            exact absurd hc (by norm_num)
          · exact absurd (hc.1 i₀) (by rw [hYdef, tilded_tilde]; simp)
      | true => rfl
  -- so they are braided over `H`, which contradicts their support behaviour
  have hbraid := hbr.braided X Y (by exact hXsum.trans hYsum.symm)
  have hXfin : #(Function.support X) < (ℵ₀ : Cardinal.{0}) := by
    refine Cardinal.lt_aleph0_iff_set_finite.mpr (Set.Finite.subset (Set.finite_singleton i₀) ?_)
    intro i hi
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact hi (by rw [hXdef]; exact if_neg hne)
  have hYinf : ¬ #(Function.support Y) < (ℵ₀ : Cardinal.{0}) := by
    intro hc
    have hfin := Cardinal.lt_aleph0_iff_set_finite.mp hc
    have huniv : Function.support Y = Set.univ :=
      Set.eq_univ_of_forall fun i => by
        rw [hYdef]
        exact tilde_ne_zero _ _
    rw [huniv] at hfin
    haveI : Infinite (Idx (ℵ₀ : Cardinal.{0})) := infinite_Idx le_rfl
    exact Set.infinite_univ hfin
  exact hYinf (hbraid.mk_support_lt (lam := (ℵ₀ : Cardinal.{0})) isConical hXfin)

end RTilde

end KappaMonoid
