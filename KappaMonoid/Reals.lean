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
open scoped ENNReal NNReal

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
  have key : ∀ z : ι → ℝ≥0, (Function.support z).Finite → ((∑ᶠ i, z i : ℝ≥0) : ℝ≥0∞) = esum z := by
    intro z hz
    have hzc : (Function.support fun i => ((z i : ℝ≥0) : ℝ≥0∞)).Finite := by
      refine Set.Finite.subset hz fun i hi => ?_
      simpa using hi
    rw [esum, tsum_eq_finsum (f := fun i => ((z i : ℝ≥0) : ℝ≥0∞)) hzc]
    exact (ENNReal.ofNNRealHom : ℝ≥0 →+* ℝ≥0∞).toAddMonoidHom.map_finsum hz
  exact_mod_cast (key x hx).trans (hsum.trans (key y hy).symm)

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

end KappaMonoid
