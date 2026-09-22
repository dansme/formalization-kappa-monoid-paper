/-
Braiding in `ℝ≥0`: two families are `ℵ₀⁻`-braided exactly when they have the same series sum and
their supports are both finite or both infinite.  The support condition is what obstructs the two
`ℵ₀`-monoid structures on `ℝ≥0 ∪ {∞}` of Examples 2.3(1)(2) from being braided over `ℝ≥0`; the
universal `ℵ₀`-extension is built in `Examples/RTilde.lean`.
-/
import KappaMonoid.Braiding
import KappaMonoid.Examples.ENNReal
import KappaMonoid.Examples.TrivExt
import KappaMonoid.Examples.Diophantine

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

/-- Infinitude of the support survives reindexing along a bijection. -/
theorem infinite_support_comp_equiv {ι : Type v} (e : ℕ ≃ ι) {x : ℕ → ℝ≥0}
    (hx : (Function.support x).Infinite) :
    (Function.support fun i => x (e.symm i)).Infinite := by
  have himg : (Function.support fun i => x (e.symm i)) = e '' Function.support x := by
    ext i
    simp only [Function.mem_support, Set.mem_image]
    constructor
    · intro hne
      exact ⟨e.symm i, hne, e.apply_symm_apply i⟩
    · rintro ⟨n, hn, rfl⟩
      simpa [e.symm_apply_apply] using hn
  rw [himg]
  exact hx.image e.injective.injOn

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
  let := LMonoid.ofAddCommMonoid ℝ≥0
  have hx' : #(Function.support x) < ℵ₀ := Cardinal.lt_aleph0_iff_set_finite.mpr hx
  have hy' : #(Function.support y) < ℵ₀ := Cardinal.lt_aleph0_iff_set_finite.mpr hy
  refine isBraided_of_small_support x y hx' hy' ?_
  rw [LMonoid.lsumOf_eq_finsum hx' x, LMonoid.lsumOf_eq_finsum hy' y,
    finsum_mem_support, finsum_mem_support]
  -- the finite sums agree because their images in `ℝ≥0∞` are the two series sums
  exact_mod_cast (coe_finsum_eq_esum hx).trans (hsum.trans (coe_finsum_eq_esum hy).symm)

/-- **Examples 3.3(2)**, the substantive half: two families in `ℝ≥0` with infinite support and the
same series sum are `ℵ₀⁻`-braided, over an index type of cardinality at most `ℵ₀`.

As in Examples 3.3(1): transport a bijection `φ : ℕ ≃ ι`, run the construction of
`realBraidState` on `x ∘ φ`, `y ∘ φ`, and hand the block boundaries, carries and deficits to
`IsBraided.of_nat_blocks`. -/
theorem isBraided_nnreal_of_infinite_support {ι : Type u} (hι : #ι ≤ ℵ₀) (x y : ι → ℝ≥0)
    (hx : (Function.support x).Infinite) (hy : (Function.support y).Infinite)
    (hsum : esum x = esum y) :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    IsBraided (ℵ₀ : Cardinal.{u}) x y := by
  let := LMonoid.ofAddCommMonoid ℝ≥0
  classical
  have hιInf : Infinite ι := by
    rcases finite_or_infinite ι with hfin | hinf
    · have := hfin
      exact absurd (Set.toFinite (Function.support x)) hx
    · exact hinf
  obtain ⟨φ⟩ := Cardinal.nonempty_equiv_nat_of_le_aleph0 hι hιInf
  have hsupp : ∀ z : ι → ℝ≥0, (Function.support z).Infinite →
      (Function.support (z ∘ φ)).Infinite := by
    intro z hz hfin
    rw [Function.support_comp_eq_preimage] at hfin
    apply hz
    rw [← Set.image_preimage_eq (Function.support z) φ.surjective]
    exact hfin.image _
  have hx3 : (Function.support (x ∘ φ)).Infinite := hsupp x hx
  have hy3 : (Function.support (y ∘ φ)).Infinite := hsupp y hy
  have hsum3 : esum (x ∘ φ) = esum (y ∘ φ) := by
    rw [esum_comp_equiv φ x, esum_comp_equiv φ y]; exact hsum
  exact IsBraided.of_nat_blocks φ (realBraidBI hx3 hy3 hsum3) (realBraidBJ hx3 hy3 hsum3)
    (strictMono_nat_of_lt_succ (realBraidBI_lt_succ hx3 hy3 hsum3))
    (strictMono_nat_of_lt_succ (realBraidBJ_lt_succ hx3 hy3 hsum3))
    (realBraidBI_zero hx3 hy3 hsum3) (realBraidBJ_zero hx3 hy3 hsum3)
    (realBraidU hx3 hy3 hsum3) (realBraidV hx3 hy3 hsum3) (realBraidV_zero hx3 hy3 hsum3)
    (realBraidBI_sum_eq hx3 hy3 hsum3) (realBraidBJ_sum_eq hx3 hy3 hsum3)

/-! ### Braided families have the same series sum

Lemma 3.2 applied in the `ℵ₀`-monoid `ℝ≥0∞` of Examples 2.3(2): the inclusion `ℝ≥0 ↪ ℝ≥0∞` is an
`ℵ₀⁻`-homomorphism, and it turns `ℵ₀`-sums into series sums. -/

/-- The inclusion `ℝ≥0 ↪ ℝ≥0∞` is an `ℵ₀⁻`-homomorphism: a `λ⁻`-sum at `λ = ℵ₀` is a finite sum,
which the inclusion preserves. -/
theorem isLHom_coe_ennreal :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    letI : KMonoid (ℵ₀ : Cardinal.{u}) ℝ≥0∞ := ENNRealExample.instKMonoid
    IsLHom (Order.le_succ (ℵ₀ : Cardinal.{u})) (fun a : ℝ≥0 => (a : ℝ≥0∞)) := by
  let := LMonoid.ofAddCommMonoid ℝ≥0
  let : KMonoid (ℵ₀ : Cardinal.{u}) ℝ≥0∞ := ENNRealExample.instKMonoid
  refine ⟨rfl, fun {ι} h x => ?_⟩
  have : Finite ι := Cardinal.lt_aleph0_iff_finite.mp h
  have : Fintype ι := Fintype.ofFinite ι
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
  let := LMonoid.ofAddCommMonoid ℝ≥0
  let : KMonoid (ℵ₀ : Cardinal.{u}) ℝ≥0∞ := ENNRealExample.instKMonoid
  have hb := sumOf_map_eq_of_isBraided (Order.le_succ (ℵ₀ : Cardinal.{u})) isLHom_coe_ennreal hι h
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
  let := LMonoid.ofAddCommMonoid ℝ≥0
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
  let _ : LMonoid (ℵ₀ : Cardinal.{0}) ℝ≥0 := LMonoid.ofAddCommMonoid ℝ≥0
  intro h
  have hfin := ((isBraided_nnreal_iff (le_of_eq Cardinal.mk_nat) single2 geom).mp h).2
  exact infinite_support_geom (hfin.mp finite_support_single2)

/-- **Examples 3.3(2)**: `geom` and `2 · geom` witness that the *trivial* `ℵ₀`-extension of `ℝ≥0`
(Examples 2.3(1)) is not `ℵ₀⁻`-braided over `ℝ≥0` either: both families have infinite support, so
both sum to `∞` there, but their series sums differ, so they are not braided. -/
theorem not_isBraided_geom_two_geom :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    ¬ IsBraided (ℵ₀ : Cardinal.{0}) geom (fun n => 2 * geom n) := by
  let _ : LMonoid (ℵ₀ : Cardinal.{0}) ℝ≥0 := LMonoid.ofAddCommMonoid ℝ≥0
  intro h
  have hsum := esum_eq_of_isBraided (le_of_eq Cardinal.mk_nat) h
  rw [esum_geom, esum_two_geom] at hsum
  norm_num at hsum

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

/-! ### Neither `ℵ₀`-monoid structure on `ℝ≥0 ∪ {∞}` is braided over `ℝ≥0`

The two witnesses above refute the braiding condition itself; these two statements package them as
the assertion Examples 3.3(2) makes. -/

/-- A countable index type for the families below. -/
theorem nonempty_idx_equiv_nat : Nonempty (Idx (ℵ₀ : Cardinal.{0}) ≃ ℕ) :=
  Cardinal.eq.mp ((mk_Idx (ℵ₀ : Cardinal.{0})).trans Cardinal.mk_nat.symm)

/-- **Examples 3.3(2)**: `ℝ≥0∞`, the `ℵ₀`-monoid structure of Examples 2.3(2) on `ℝ≥0 ∪ {∞}`, is
*not* `ℵ₀⁻`-braided over `ℝ≥0`.  Witness: `single2` and `geom` have the same sum `2` but different
support behaviour. -/
theorem not_isBraidedOver_ennreal :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    letI : KMonoid (ℵ₀ : Cardinal.{0}) ℝ≥0∞ := ENNRealExample.instKMonoid
    ¬ IsBraidedOver (ℵ₀ : Cardinal.{0}) ℵ₀ ℝ≥0 ℝ≥0∞ (Order.le_succ ℵ₀)
        (fun a : ℝ≥0 => ((a : ℝ≥0) : ℝ≥0∞)) := by
  let _ : LMonoid (ℵ₀ : Cardinal.{0}) ℝ≥0 := LMonoid.ofAddCommMonoid ℝ≥0
  let _ : KMonoid (ℵ₀ : Cardinal.{0}) ℝ≥0∞ := ENNRealExample.instKMonoid
  intro hbr
  obtain ⟨e⟩ := nonempty_idx_equiv_nat
  have hsum : (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{0})) fun i => ((single2 (e i) : ℝ≥0) : ℝ≥0∞))
      = KMonoid.ksum (κ := (ℵ₀ : Cardinal.{0})) fun i => ((geom (e i) : ℝ≥0) : ℝ≥0∞) := by
    rw [← KMonoid.sumOf_Idx, ← KMonoid.sumOf_Idx,
      ENNRealExample.instKMonoid_sumOf (le_of_eq (mk_Idx _)),
      ENNRealExample.instKMonoid_sumOf (le_of_eq (mk_Idx _)),
      e.tsum_eq fun n => ((single2 n : ℝ≥0) : ℝ≥0∞),
      e.tsum_eq fun n => ((geom n : ℝ≥0) : ℝ≥0∞)]
    exact esum_single2.trans esum_geom.symm
  have hb := (hbr.braided _ _ hsum).comp_equiv e.symm
  simp only [Equiv.apply_symm_apply] at hb
  exact not_isBraided_single2_geom hb

/-- **Examples 3.3(2)**: the *trivial* `ℵ₀`-extension of `ℝ≥0` (Examples 2.3(1)) is not
`ℵ₀⁻`-braided over `ℝ≥0` either.  Witness: `geom` and `2 · geom` both have infinite support, so
both sum to `∞` there, but their series sums differ. -/
theorem not_isBraidedOver_trivExt_nnreal :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    letI := TrivExt.instKMonoid (M := ℝ≥0) (κ := (ℵ₀ : Cardinal.{0})) isConical_nnreal le_rfl
    ¬ IsBraidedOver (ℵ₀ : Cardinal.{0}) ℵ₀ ℝ≥0 (WithTop ℝ≥0) (Order.le_succ ℵ₀)
        (fun a : ℝ≥0 => ((a : ℝ≥0) : WithTop ℝ≥0)) := by
  let _ : LMonoid (ℵ₀ : Cardinal.{0}) ℝ≥0 := LMonoid.ofAddCommMonoid ℝ≥0
  let _ : KMonoid (ℵ₀ : Cardinal.{0}) (WithTop ℝ≥0) :=
    TrivExt.instKMonoid (M := ℝ≥0) (κ := (ℵ₀ : Cardinal.{0})) isConical_nnreal le_rfl
  intro hbr
  obtain ⟨e⟩ := nonempty_idx_equiv_nat
  have hinf : ∀ f : ℕ → ℝ≥0, (∀ n, f n ≠ 0) →
      (Function.support fun i : Idx (ℵ₀ : Cardinal.{0}) => ((f (e i) : ℝ≥0) : WithTop ℝ≥0)).Infinite := by
    intro f hf
    have : Infinite (Idx (ℵ₀ : Cardinal.{0})) := infinite_Idx le_rfl
    have hsupp : (Function.support fun i : Idx (ℵ₀ : Cardinal.{0}) =>
        ((f (e i) : ℝ≥0) : WithTop ℝ≥0)) = Set.univ :=
      Set.eq_univ_of_forall fun i => by
        simp only [Function.mem_support, ne_eq, WithTop.coe_eq_zero]
        exact hf (e i)
    rw [hsupp]
    exact Set.infinite_univ
  have hsum : (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{0})) fun i => ((geom (e i) : ℝ≥0) : WithTop ℝ≥0))
      = KMonoid.ksum (κ := (ℵ₀ : Cardinal.{0}))
          fun i => (((2 * geom (e i) : ℝ≥0)) : WithTop ℝ≥0) := by
    rw [TrivExt.instKMonoid_ksum isConical_nnreal le_rfl,
      TrivExt.instKMonoid_ksum isConical_nnreal le_rfl,
      TrivExt.sigma_eq_top_of_infinite (hinf geom geom_ne_zero).not_finite,
      TrivExt.sigma_eq_top_of_infinite
        (hinf (fun n => 2 * geom n) fun n => mul_ne_zero two_ne_zero (geom_ne_zero n)).not_finite]
  have hb := (hbr.braided _ _ hsum).comp_equiv e.symm
  simp only [Equiv.apply_symm_apply] at hb
  exact not_isBraided_geom_two_geom hb

end KappaMonoid
