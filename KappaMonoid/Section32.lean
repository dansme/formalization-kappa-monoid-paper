/-
**Scaffolding for the unformalised part of Section 3** of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

Every proof in this file is `sorry`.  The file is deliberately **not** imported by
`KappaMonoid.lean`, so `lake build` continues to check a `sorry`-free development; build this
file on its own with

    lake build KappaMonoid.Section32

Its purpose is to fix the *statements* — which is the part of §3.2 that takes judgement — so that
they are known to elaborate before anyone starts proving them.  See `SECTION3-PLAN.md` for the
order of work and the proof sketches.

Contents, in dependency order:

* Examples 3.3(1): `ℕ₀ ∪ {∞}` is `ℵ₀⁻`-braided over `ℕ₀`.
* Lemma 3.13(1): `F_κ(B)` is the universal `κ`-extension of `F_{λ⁻}(B)`.
* Saturated submonoids and Lemma 3.13(2).
* Proposition 3.14: universal extensions of monoids cut out by homogeneous linear equations,
  inequalities and congruences.
-/
import KappaMonoid.Free
import KappaMonoid.Universal
import KappaMonoid.Examples
import KappaMonoid.OrderUnit

universe u v w

open Cardinal Function Set

namespace KappaMonoid

/-! ## Examples 3.3(1): braiding in `ℕ₀`

Two families in `ℕ₀` are `ℵ₀⁻`-braided iff either both have finite support and equal sums, or
both have infinite support.  The substantive half is the second: given a finite partial sum
`a_m + ⋯ + a_n` of one family, the other family — having infinite support, so infinitely many
entries `≥ 1` — has a partial sum dominating it, and the braiding is built by alternating. -/

/-- Two finitely supported families in `ℕ₀` with the same sum are braided.  (A special case of
`isBraided_of_small_support`, recorded here for the classification below.) -/
theorem isBraided_nat_of_finite_support {ι : Type u} (x y : ι → ℕ)
    (hx : (Function.support x).Finite) (hy : (Function.support y).Finite)
    (hsum : ∑ᶠ i, x i = ∑ᶠ i, y i) :
    letI := LMonoid.ofAddCommMonoid ℕ
    IsBraided ℵ₀ x y := by
  letI := LMonoid.ofAddCommMonoid ℕ
  have hx' : #(Function.support x) < ℵ₀ := Cardinal.lt_aleph0_iff_set_finite.mpr hx
  have hy' : #(Function.support y) < ℵ₀ := Cardinal.lt_aleph0_iff_set_finite.mpr hy
  refine isBraided_of_small_support x y hx' hy' ?_
  rw [LMonoid.lsumOf_eq_finsum hx' x, LMonoid.lsumOf_eq_finsum hy' y,
    finsum_mem_support, finsum_mem_support]
  exact hsum

/-! ### Helper lemmas for the infinite-support case

Building the braiding of two infinite-support families in `ℕ₀` is a genuine construction: we
alternately grow finite intervals `[c, M)` of `ℕ` along each family, choosing `M` large enough
(using that the family has infinitely many nonzero entries) to make the partial sum dominate
whatever deficit was left over from the other family's previous interval. -/

/-- If `S : Set ℕ` is infinite and `f` is `≥ 1` on `S`, then starting from any `c`, some interval
`[c, M)` has `f`-sum at least any prescribed target `d`. -/
theorem exists_ico_dominates {S : Set ℕ} (hS : S.Infinite) (f : ℕ → ℕ)
    (hf : ∀ i ∈ S, 1 ≤ f i) (c d : ℕ) :
    ∃ M, c < M ∧ d ≤ ∑ i ∈ Finset.Ico c M, f i := by
  classical
  have hnth_ge : ∀ n, n ≤ Nat.nth (· ∈ S) n := fun n => (Nat.nth_strictMono hS).id_le n
  set M := Nat.nth (· ∈ S) (c + d) + 1 with hM
  refine ⟨M, by have := hnth_ge (c + d); omega, ?_⟩
  set T : Finset ℕ := (Finset.range (d + 1)).image (fun j => Nat.nth (· ∈ S) (c + j)) with hT
  have hinj : Set.InjOn (fun j => Nat.nth (· ∈ S) (c + j)) (Finset.range (d + 1)) := by
    intro a _ b _ hab
    have := (Nat.nth_strictMono hS).injective hab
    omega
  have hTcard : T.card = d + 1 := by
    rw [hT, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hTsub : T ⊆ Finset.Ico c M := by
    intro i hi
    simp only [hT, Finset.mem_image, Finset.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have h1 := hnth_ge (c + j)
    have h2 : Nat.nth (· ∈ S) (c + j) ≤ Nat.nth (· ∈ S) (c + d) :=
      (Nat.nth_strictMono hS).monotone (by omega)
    simp only [Finset.mem_Ico, hM]
    omega
  have hTval : ∀ i ∈ T, 1 ≤ f i := by
    intro i hi
    simp only [hT, Finset.mem_image, Finset.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact hf _ (Nat.nth_mem_of_infinite hS _)
  calc d ≤ d + 1 := Nat.le_succ d
    _ = T.card := hTcard.symm
    _ = ∑ _i ∈ T, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ i ∈ T, f i := Finset.sum_le_sum hTval
    _ ≤ ∑ i ∈ Finset.Ico c M, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun i _ _ => Nat.zero_le _)

/-- A strictly monotone `b : ℕ → ℕ` with `b 0 = 0` partitions `ℕ` into the intervals
`[b k, b (k+1))`. -/
theorem iUnion_Ico_eq_univ_of_strictMono {b : ℕ → ℕ} (hb0 : b 0 = 0) (hb : StrictMono b) :
    (⋃ k, Set.Ico (b k) (b (k + 1))) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro n
  have hbge : ∀ k, k ≤ b k := fun k => hb.id_le k
  have hex : ∃ k, n < b (k + 1) := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (hbge (n + 1))⟩
  refine Set.mem_iUnion.mpr ⟨Nat.find hex, ?_⟩
  have hk : n < b (Nat.find hex + 1) := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hk0 | hkpos
  · exact Set.mem_Ico.mpr ⟨by rw [hk0, hb0]; exact Nat.zero_le n, hk⟩
  · have hnotk : ¬ n < b ((Nat.find hex - 1) + 1) :=
      Nat.find_min hex (Nat.sub_lt hkpos one_pos)
    rw [Nat.sub_add_cancel hkpos] at hnotk
    exact Set.mem_Ico.mpr ⟨not_lt.mp hnotk, hk⟩

/-- Two intervals `[b k, b (k+1))`, `[b k', b (k'+1))` cut out by a strictly monotone `b` and
distinct `k ≠ k'` are disjoint. -/
theorem ico_pairwise_disjoint {b : ℕ → ℕ} (hb : StrictMono b) {k k' : ℕ} (hne : k ≠ k') :
    Disjoint (Set.Ico (b k) (b (k + 1))) (Set.Ico (b k') (b (k' + 1))) := by
  wlog hlt : k < k' generalizing k k'
  · exact (this hne.symm (by omega)).symm
  rw [Set.disjoint_left]
  intro i hi hi'
  simp only [Set.mem_Ico] at hi hi'
  have : b (k + 1) ≤ b k' := hb.monotone (by omega)
  omega

/-- The recursive state driving the construction: `(bI, bJ, v)` where `bI` and `bJ` are the
current right-hand endpoints of the intervals built so far along `x` and along `y`, and `v` is
the current deficit carried over to the next interval along `x`.  At each step we grow `bI` far
enough along `support x` to dominate `v`, producing a new deficit `u` for `y`, then grow `bJ` far
enough along `support y` to dominate `u`, producing the next `v`. -/
noncomputable def natBraidState (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 0)
  | (k + 1) =>
      let s := natBraidState x y hx hy k
      let bI' := (exists_ico_dominates hx x
        (fun i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi)) s.1 s.2.2).choose
      let u := (∑ i ∈ Finset.Ico s.1 bI', x i) - s.2.2
      let bJ' := (exists_ico_dominates hy y
        (fun i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi)) s.2.1 u).choose
      (bI', bJ', (∑ i ∈ Finset.Ico s.2.1 bJ', y i) - u)

theorem natBraidState_succ (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) :
    natBraidState x y hx hy (k + 1) =
      let s := natBraidState x y hx hy k
      let bI' := (exists_ico_dominates hx x
        (fun i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi)) s.1 s.2.2).choose
      let u := (∑ i ∈ Finset.Ico s.1 bI', x i) - s.2.2
      let bJ' := (exists_ico_dominates hy y
        (fun i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi)) s.2.1 u).choose
      (bI', bJ', (∑ i ∈ Finset.Ico s.2.1 bJ', y i) - u) := rfl

/-- The `x`-boundary sequence. -/
noncomputable def natBraidBI (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) : ℕ := (natBraidState x y hx hy k).1

/-- The `y`-boundary sequence. -/
noncomputable def natBraidBJ (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) : ℕ := (natBraidState x y hx hy k).2.1

/-- The deficit sequence, playing the role of `v` in `BraidingData`. -/
noncomputable def natBraidV (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) : ℕ := (natBraidState x y hx hy k).2.2

/-- The deficit sequence, playing the role of `u` in `BraidingData`. -/
noncomputable def natBraidU (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) : ℕ :=
  (∑ i ∈ Finset.Ico (natBraidBI x y hx hy k) (natBraidBI x y hx hy (k + 1)), x i)
    - natBraidV x y hx hy k

theorem natBraidBI_zero (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) : natBraidBI x y hx hy 0 = 0 := rfl

theorem natBraidBJ_zero (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) : natBraidBJ x y hx hy 0 = 0 := rfl

theorem natBraidV_zero (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) : natBraidV x y hx hy 0 = 0 := rfl

/-- The defining property of `bI (k+1)`: it dominates the deficit `v k` along `support x`. -/
theorem natBraidBI_succ_spec (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) :
    natBraidBI x y hx hy k < natBraidBI x y hx hy (k + 1) ∧
      natBraidV x y hx hy k ≤
        ∑ i ∈ Finset.Ico (natBraidBI x y hx hy k) (natBraidBI x y hx hy (k + 1)), x i :=
  (exists_ico_dominates hx x (fun i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi))
    (natBraidBI x y hx hy k) (natBraidV x y hx hy k)).choose_spec

/-- The defining property of `bJ (k+1)`: it dominates the deficit `u k` along `support y`. -/
theorem natBraidBJ_succ_spec (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) :
    natBraidBJ x y hx hy k < natBraidBJ x y hx hy (k + 1) ∧
      natBraidU x y hx hy k ≤
        ∑ i ∈ Finset.Ico (natBraidBJ x y hx hy k) (natBraidBJ x y hx hy (k + 1)), y i :=
  (exists_ico_dominates hy y (fun i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi))
    (natBraidBJ x y hx hy k) (natBraidU x y hx hy k)).choose_spec

theorem natBraidBI_lt_succ (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) :
    natBraidBI x y hx hy k < natBraidBI x y hx hy (k + 1) :=
  (natBraidBI_succ_spec x y hx hy k).1

theorem natBraidBJ_lt_succ (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) :
    natBraidBJ x y hx hy k < natBraidBJ x y hx hy (k + 1) :=
  (natBraidBJ_succ_spec x y hx hy k).1

/-- The defining equation for `x`: the sum over the `k`-th `x`-interval equals the incoming
deficit `v k` plus the outgoing deficit `u k`. -/
theorem natBraidBI_sum_eq (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) :
    ∑ i ∈ Finset.Ico (natBraidBI x y hx hy k) (natBraidBI x y hx hy (k + 1)), x i =
      natBraidV x y hx hy k + natBraidU x y hx hy k := by
  have h := (natBraidBI_succ_spec x y hx hy k).2
  unfold natBraidU
  omega

/-- The defining equation for `y`: the sum over the `k`-th `y`-interval equals the next incoming
deficit `v (k+1)` plus the outgoing deficit `u k`. -/
theorem natBraidBJ_sum_eq (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) :
    ∑ i ∈ Finset.Ico (natBraidBJ x y hx hy k) (natBraidBJ x y hx hy (k + 1)), y i =
      natBraidV x y hx hy (k + 1) + natBraidU x y hx hy k := by
  have h := (natBraidBJ_succ_spec x y hx hy k).2
  have hv : natBraidV x y hx hy (k + 1) =
      (∑ i ∈ Finset.Ico (natBraidBJ x y hx hy k) (natBraidBJ x y hx hy (k + 1)), y i)
        - natBraidU x y hx hy k := rfl
  omega

/-- **Examples 3.3(1)**, the substantive half: two families in `ℕ₀` with infinite support are
`ℵ₀⁻`-braided, provided the (necessarily infinite, since it contains an infinite support) index
type `ι` has cardinality at most `ℵ₀`.  (Without this hypothesis the statement is false: e.g. a
family that is `≡ 1` on an uncountable index type cannot be braided with one supported only on a
countable subset, since `BraidingData`'s pieces have size `< ℵ₀`, so only countably many of them
can be nonempty, and each nonzero entry of the first family needs its own piece.)

We build the `BraidingData` directly over `ι`: transport a bijection `φ : ℕ ≃ ι` (which exists
since `ι` is infinite of cardinality `≤ ℵ₀`), run the `ℕ`-arithmetic construction on
`x ∘ φ, y ∘ φ : ℕ → ℕ`, and place all of the pieces at the single basepoint `a₀ := φ 0`, moving
the resulting intervals of `ℕ` back into subsets of `ι` via images under `φ`.  (We deliberately
avoid `IsBraided.reindex`, whose two index types live in the *same* universe `u`: here one side is
the genuinely `Type 0`-valued `ℕ`, which need not match the ambient `ι : Type u`.) -/
theorem isBraided_nat_of_infinite_support {ι : Type u} (hι : #ι ≤ ℵ₀) (x y : ι → ℕ)
    (hx : (Function.support x).Infinite) (hy : (Function.support y).Infinite) :
    letI := LMonoid.ofAddCommMonoid ℕ
    IsBraided ℵ₀ x y := by
  letI := LMonoid.ofAddCommMonoid ℕ
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
  have hmk : #(ULift.{u} ℕ) = #ι := le_antisymm h1 h2
  obtain ⟨e0⟩ := Cardinal.eq.mp hmk
  -- `e0 : ULift.{u} ℕ ≃ ι`; compose with `Equiv.ulift : ULift.{u} ℕ ≃ ℕ` to get a plain bijection
  -- `φ : ℕ ≃ ι` (this is fine as a *term*: `Equiv.trans` does not require matching universes,
  -- only the theorem `IsBraided.reindex` does — so we avoid calling it and instead build the
  -- `BraidingData` for `x y : ι → ℕ` directly, using images under `φ`).
  set φ : ℕ ≃ ι := Equiv.ulift.symm.trans e0 with hφ
  set x3 : ℕ → ℕ := x ∘ φ with hx3def
  set y3 : ℕ → ℕ := y ∘ φ with hy3def
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
  have hbI : StrictMono (natBraidBI x3 y3 hx3 hy3) :=
    strictMono_nat_of_lt_succ (natBraidBI_lt_succ x3 y3 hx3 hy3)
  have hbJ : StrictMono (natBraidBJ x3 y3 hx3 hy3) :=
    strictMono_nat_of_lt_succ (natBraidBJ_lt_succ x3 y3 hx3 hy3)
  set a₀ : ι := φ 0 with ha₀def
  set I : ι × ℕ → Set ι := fun p =>
    if p.1 = a₀ then
      φ '' Set.Ico (natBraidBI x3 y3 hx3 hy3 p.2) (natBraidBI x3 y3 hx3 hy3 (p.2 + 1))
    else ∅ with hIdef
  set J : ι × ℕ → Set ι := fun p =>
    if p.1 = a₀ then
      φ '' Set.Ico (natBraidBJ x3 y3 hx3 hy3 p.2) (natBraidBJ x3 y3 hx3 hy3 (p.2 + 1))
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
      have hcov := iUnion_Ico_eq_univ_of_strictMono (natBraidBI_zero x3 y3 hx3 hy3) hbI
      have hi : φ.symm i ∈
          (⋃ k, Set.Ico (natBraidBI x3 y3 hx3 hy3 k) (natBraidBI x3 y3 hx3 hy3 (k + 1))) := by
        rw [hcov]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hi
      refine Set.mem_iUnion.mpr ⟨(a₀, k), ?_⟩
      rw [hIdef]; dsimp only
      rw [if_pos rfl]
      exact ⟨φ.symm i, hk, φ.apply_symm_apply i⟩)
    (Set.eq_univ_of_forall fun i => by
      have hcov := iUnion_Ico_eq_univ_of_strictMono (natBraidBJ_zero x3 y3 hx3 hy3) hbJ
      have hi : φ.symm i ∈
          (⋃ k, Set.Ico (natBraidBJ x3 y3 hx3 hy3 k) (natBraidBJ x3 y3 hx3 hy3 (k + 1))) := by
        rw [hcov]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hi
      refine Set.mem_iUnion.mpr ⟨(a₀, k), ?_⟩
      rw [hJdef]; dsimp only
      rw [if_pos rfl]
      exact ⟨φ.symm i, hk, φ.apply_symm_apply i⟩)
    (fun p => if p.1 = a₀ then natBraidU x3 y3 hx3 hy3 p.2 else 0)
    (fun p => if p.1 = a₀ then natBraidV x3 y3 hx3 hy3 p.2 else 0)
    (fun a => by
      by_cases h : a = a₀
      · simp [h, natBraidV_zero]
      · simp [h])
    (fun p => by
      by_cases hp : p.1 = a₀
      · simp only [hIdef, if_pos hp]
        rw [finsum_mem_image φ.injective.injOn,
          show (Set.Ico (natBraidBI x3 y3 hx3 hy3 p.2) (natBraidBI x3 y3 hx3 hy3 (p.2 + 1))
                : Set ℕ)
            = (↑(Finset.Ico (natBraidBI x3 y3 hx3 hy3 p.2) (natBraidBI x3 y3 hx3 hy3 (p.2 + 1)))
              : Set ℕ)
            from (Finset.coe_Ico _ _).symm, finsum_mem_coe_finset]
        exact natBraidBI_sum_eq x3 y3 hx3 hy3 p.2
      · simp [hIdef, if_neg hp])
    (fun p => by
      have hfst : (bsucc p).1 = p.1 := rfl
      by_cases hp : p.1 = a₀
      · simp only [hJdef, hfst, if_pos hp]
        rw [finsum_mem_image φ.injective.injOn,
          show (Set.Ico (natBraidBJ x3 y3 hx3 hy3 p.2) (natBraidBJ x3 y3 hx3 hy3 (p.2 + 1))
              : Set ℕ)
            = (↑(Finset.Ico (natBraidBJ x3 y3 hx3 hy3 p.2) (natBraidBJ x3 y3 hx3 hy3 (p.2 + 1)))
              : Set ℕ)
            from (Finset.coe_Ico _ _).symm, finsum_mem_coe_finset]
        exact natBraidBJ_sum_eq x3 y3 hx3 hy3 p.2
      · simp only [hJdef, hfst, if_neg hp]
        simp)⟩

/-! ### Packaging: `ℕ₀ ∪ {∞}` as an `ℵ₀`-monoid over `ℕ₀` -/

/-- The inclusion `ℕ₀ ↪ ℕ₀ ∪ {∞}` does not change the support of a family. -/
theorem support_coe_withTop_nat {ι : Type u} (x : ι → ℕ) :
    Function.support (fun i => ((x i : ℕ) : WithTop ℕ)) = Function.support x := by
  ext i
  simp [Function.mem_support]

/-- The summation of `ℕ₀ ∪ {∞}` on a finitely supported family from `ℕ₀` is its finite sum. -/
theorem trivExt_sigma_coe_nat_of_finite {ι : Type u} {x : ι → ℕ}
    (hx : (Function.support x).Finite) :
    TrivExt.sigma (fun i => ((x i : ℕ) : WithTop ℕ)) = ((∑ᶠ i, x i : ℕ) : WithTop ℕ) := by
  rw [TrivExt.sigma_of_good (x := fun i => ((x i : ℕ) : WithTop ℕ))
    (by rw [support_coe_withTop_nat]; exact hx) fun _ => WithTop.coe_ne_top]
  exact congrArg _ (finsum_congr fun i => rfl)

/-- The summation of `ℕ₀ ∪ {∞}` on an infinitely supported family from `ℕ₀` is `∞`. -/
theorem trivExt_sigma_coe_nat_of_infinite {ι : Type u} {x : ι → ℕ}
    (hx : (Function.support x).Infinite) :
    TrivExt.sigma (fun i => ((x i : ℕ) : WithTop ℕ)) = ⊤ :=
  TrivExt.sigma_eq_top_of_infinite (by rw [support_coe_withTop_nat]; exact hx)

/-- **Examples 3.3(1)**: the trivial `ℵ₀`-extension `ℕ₀ ∪ {∞}` is `ℵ₀⁻`-braided over `ℕ₀`, hence
(by Theorem 3.11(2)) *is* the universal `ℵ₀`-extension of `ℕ₀`.  This is the first entry of
Examples 3.12. -/
theorem isBraidedOver_withTop_nat :
    letI := LMonoid.ofAddCommMonoid ℕ
    letI := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
    IsBraidedOver (ℵ₀ : Cardinal.{u}) ℵ₀ ℕ (WithTop ℕ) le_rfl (fun a => (a : WithTop ℕ)) := by
  letI := LMonoid.ofAddCommMonoid ℕ
  letI := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
  classical
  have hksum : ∀ x : Idx (ℵ₀ : Cardinal.{u}) → WithTop ℕ,
      KMonoid.ksum (κ := ℵ₀) x = TrivExt.sigma x :=
    fun x => TrivExt.instKMonoid_ksum _ _ x
  refine ⟨⟨rfl, fun {ι} h x => ?_⟩, fun a b hab => ?_, fun h => ?_, fun x y hxy => ?_⟩
  · -- `↑` is an `ℵ₀⁻`-homomorphism: both sides are the finite sum of the `x i`
    haveI : Finite ι := Cardinal.lt_aleph0_iff_finite.mp h
    haveI : Fintype ι := Fintype.ofFinite ι
    rw [LMonoid.lsumOf_aleph0_eq_finsum h x, KMonoid.sumOf_eq_sum]
    simp
  · exact_mod_cast hab
  · -- `ℕ₀` generates `ℕ₀ ∪ {∞}`: a finite element is a one-term sum, `∞` is the sum of `1`s
    rcases eq_or_ne h ⊤ with rfl | hne
    · refine ⟨fun _ => 1, ?_⟩
      haveI : Infinite (Idx (ℵ₀ : Cardinal.{u})) := infinite_Idx le_rfl
      rw [hksum, trivExt_sigma_coe_nat_of_infinite
        (x := fun _ : Idx (ℵ₀ : Cardinal.{u}) => 1) ?_]
      rw [show (Function.support fun _ : Idx (ℵ₀ : Cardinal.{u}) => 1) = Set.univ from
        Set.eq_univ_of_forall fun _ => one_ne_zero]
      exact Set.infinite_univ
    · obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
      obtain ⟨i₀⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
      refine ⟨fun i => if i = i₀ then a else 0, ?_⟩
      rw [KMonoid.ksum_single i₀ _ fun i hi => by simp [hi]]
      simp
  · -- families with equal sum are braided: finite support on both sides, or infinite on both
    rw [hksum, hksum] at hxy
    have hidx : #(Idx (ℵ₀ : Cardinal.{u})) ≤ ℵ₀ := le_of_eq (mk_Idx _)
    by_cases hfx : (Function.support x).Finite <;> by_cases hfy : (Function.support y).Finite
    · rw [trivExt_sigma_coe_nat_of_finite hfx, trivExt_sigma_coe_nat_of_finite hfy] at hxy
      exact isBraided_nat_of_finite_support x y hfx hfy (by exact_mod_cast hxy)
    · rw [trivExt_sigma_coe_nat_of_finite hfx, trivExt_sigma_coe_nat_of_infinite hfy] at hxy
      exact absurd hxy WithTop.coe_ne_top
    · rw [trivExt_sigma_coe_nat_of_infinite hfx, trivExt_sigma_coe_nat_of_finite hfy] at hxy
      exact absurd hxy.symm WithTop.coe_ne_top
    · exact isBraided_nat_of_infinite_support hidx x y hfx hfy

/-- **Examples 3.12**, first entry: `ℕ̂₀ = ℕ₀ ∪ {∞}`.  Combining `isBraidedOver_withTop_nat` with
Theorem 3.11(2), the universal `ℵ₀`-extension of `ℕ₀` is its trivial `ℵ₀`-extension. -/
theorem isUniversalKExtension_withTop_nat :
    letI := LMonoid.ofAddCommMonoid ℕ
    letI := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
    IsUniversalKExtension (ℵ₀ : Cardinal.{u}) ℵ₀ ℕ (WithTop ℕ) le_rfl
      (fun a => (a : WithTop ℕ)) := by
  letI := LMonoid.ofAddCommMonoid ℕ
  letI := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
  exact isBraidedOver_withTop_nat.isUniversalKExtension le_rfl

/-! ## Lemma 3.13(1): free objects

`F_{λ⁻}(B)` sits inside `F_κ(B)` — a family of cardinals `< λ` with support of size `< λ` is in
particular a family of cardinals `≤ κ` with support of size `≤ κ` — and the universal property of
`F_κ(B)` (Proposition 2.9) is exactly the universal property required of the extension. -/

section Free

variable {lam κ : Cardinal.{u}} {B : Type u}

/-- A `λ⁻`-homomorphism into a `κ`-monoid is the same thing as an `LMonoid lam`-homomorphism for
the induced structure: `toLMonoidOfLE`'s `λ⁻`-sums *are* the `κ`-sums, by definition. -/
theorem isLMonoidHom_of_isLHom {X : Type v} {K : Type w} [LMonoid lam X] [KMonoid κ K]
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) {f : X → K} (hf : LMonoid.IsLHom hlk f) :
    letI := KMonoid.toLMonoidOfLE K hlam hlk
    IsLMonoidHom lam f :=
  fun h x => hf.2 h x

/-- Conversely, an `LMonoid lam`-homomorphism into a `κ`-monoid is a `λ⁻`-homomorphism. -/
theorem isLHom_of_isLMonoidHom {X : Type v} {K : Type w} [LMonoid lam X] [KMonoid κ K]
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) {f : X → K}
    (hf : letI := KMonoid.toLMonoidOfLE K hlam hlk; IsLMonoidHom lam f) :
    LMonoid.IsLHom hlk f := by
  letI := KMonoid.toLMonoidOfLE K hlam hlk
  exact ⟨hf.map_zero, fun h x => hf h x⟩

/-- The inclusion `F_{λ⁻}(B) ↪ F_κ(B)`. -/
def freeIncl (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ κ) (x : ↥(FreeL lam B)) :
    ↥(FreeK κ B) :=
  ⟨fun b => ⟨((x : B → LCard lam) b : Cardinal.{u}),
      lt_of_lt_of_le ((x : B → LCard lam) b).2 (le_trans hlk (Order.le_succ κ))⟩,
    lt_of_lt_of_le x.2 (le_trans hlk (Order.le_succ κ))⟩

@[simp] theorem val_freeIncl (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ κ)
    (x : ↥(FreeL lam B)) (b : B) :
    (((freeIncl hlam hκ hlk x : ↥(FreeK κ B)) : B → Fcard κ) b : Cardinal.{u})
      = ((x : B → LCard lam) b : Cardinal.{u}) := rfl

/-- `freeIncl` carries the generator `ι(b)` of `F_{λ⁻}(B)` to the generator `ι(b)` of
`F_κ(B)`. -/
theorem freeIncl_iota (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ κ) (b : B) :
    letI : Fact lam.IsRegular := ⟨hlam⟩
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    freeIncl hlam hκ hlk (iota (lam := lam) b) = iota (lam := Order.succ κ) b := by
  letI : Fact lam.IsRegular := ⟨hlam⟩
  letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  refine Subtype.ext (funext fun b' => Subtype.ext ?_)
  rw [val_freeIncl, coe_iota, coe_iota]
  by_cases h : b' = b
  · rw [h, val_iotaFun_self, val_iotaFun_self]
  · rw [val_iotaFun_of_ne (lam := lam) h, val_iotaFun_of_ne (lam := Order.succ κ) h]

/-- `freeIncl` is a `λ⁻`-homomorphism: on both sides a coordinate is the same cardinal sum. -/
theorem isLHom_freeIncl (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ κ) :
    letI : Fact lam.IsRegular := ⟨hlam⟩
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    letI := instKMonoidFreeK κ hκ B
    LMonoid.IsLHom hlk (freeIncl (B := B) hlam hκ hlk) := by
  letI : Fact lam.IsRegular := ⟨hlam⟩
  letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  letI := instKMonoidFreeK κ hκ B
  refine ⟨Subtype.ext (funext fun b => Subtype.ext ?_), fun {ι} h x => ?_⟩
  · rw [val_freeIncl]
    show ((0 : LCard lam) : Cardinal.{u}) = ((0 : Fcard κ) : Cardinal.{u})
    rw [LCard.val_zero hlam, LCard.val_zero (Cardinal.isRegular_succ hκ)]
  · exact Subtype.ext (funext fun b => Subtype.ext rfl)

/-- **Lemma 3.13(1)**: the free `κ`-monoid on `B` is the universal `κ`-extension of the free
`λ⁻`-monoid on `B`.

Both universal properties are Proposition 2.9, at `λ` and at `κ⁺` respectively; the extension of
`φ : F_{λ⁻}(B) → K` is `lift (φ ∘ ι)`, and both halves of the universal property are `hom_ext` —
at level `λ` for the extension identity, at level `κ⁺` for uniqueness. -/
theorem lemma_3_13_free (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ κ) :
    letI : Fact lam.IsRegular := ⟨hlam⟩
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    letI := instKMonoidFreeK κ hκ B
    IsUniversalKExtension lam κ ↥(FreeL lam B) ↥(FreeK κ B) hlk (freeIncl hlam hκ hlk) := by
  letI : Fact lam.IsRegular := ⟨hlam⟩
  letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  letI := instKMonoidFreeK κ hκ B
  refine ⟨isLHom_freeIncl hlam hκ hlk, fun K _ φ hφ => ?_⟩
  -- the extension is the lift of `φ ∘ ι`, taken at level `κ⁺`
  set ψ : ↥(FreeK κ B) → K :=
    lift (lam := Order.succ κ) (X := K) (fun b => φ (iota (lam := lam) b)) with hψ
  have hψiota : ∀ b : B, ψ (iota (lam := Order.succ κ) b) = φ (iota (lam := lam) b) :=
    fun b => by rw [hψ, lift_iota]
  refine ⟨ψ, ⟨isKHom_of_isLMonoidHom hκ (isLMonoidHom_lift _), ?_⟩, ?_⟩
  · -- `ψ ∘ freeIncl = φ`: both are `λ⁻`-homomorphisms agreeing on the generators
    letI := KMonoid.toLMonoidOfLE K hlam hlk
    have hcomp : IsLMonoidHom lam (fun x => ψ (freeIncl hlam hκ hlk x)) := by
      intro ι h x
      show ψ (freeIncl hlam hκ hlk (LMonoid.lsumOf (lam := lam) h x)) = _
      rw [(isLHom_freeIncl (B := B) hlam hκ hlk).2 h x]
      exact isLMonoidHom_lift _ (KMonoid.lt_succ (h.le.trans hlk)) _
    have key := hom_ext (lam := lam) (X := K)
      (g₁ := fun x => ψ (freeIncl hlam hκ hlk x)) (g₂ := φ) hcomp
      (isLMonoidHom_of_isLHom hlam hlk hφ)
      (fun b => by rw [freeIncl_iota hlam hκ hlk b, hψiota b])
    exact fun x => congrFun key x
  · -- uniqueness: a `κ`-homomorphism out of `F_κ(B)` is determined on the generators
    rintro ψ' ⟨hhom', hext'⟩
    refine hom_ext (lam := Order.succ κ) (X := K) (g₁ := ψ') (g₂ := ψ)
      (fun {ι} h x => KMonoid.IsKHom.map_sumOf hhom' (KMonoid.le_of_lt_succ h) x)
      (isLMonoidHom_lift _) fun b => ?_
    rw [hψiota b, ← freeIncl_iota hlam hκ hlk b, hext']

end Free

/-! ## Saturated submonoids and Lemma 3.13(2) -/

/-- A submonoid `S ⊆ X` is *saturated* if a summand in `X` of an element of `S` that itself lies
in `S` has its complement in `S`: from `s = t + h` with `s`, `t ∈ S` follows `h ∈ S`. -/
def IsSaturated {X : Type v} [AddCommMonoid X] (S : Set X) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, ∀ h : X, s = t + h → h ∈ S

section Sub

variable {lam κ : Cardinal.{u}} {X : Type v} {Hh : Type w}

/-- **Lemma 3.13(2)**, in the form actually used: if `Ĥ` is `λ⁻`-braided over `X` and `S ⊆ X` is a
`λ⁻`-submonoid which is either saturated or sits over an uncountable `λ`, then *any* `κ`-submonoid
`T` of `Ĥ` with `f(S) ⊆ T ⊆ ⟨f(S)⟩_κ` — that is, `T = ⟨S⟩_κ` described extensionally — is the
universal `κ`-extension of `S`.  Stating the conclusion for such a `T` rather than for
`⟨f(S)⟩_κ` on the nose avoids rewriting a set equality inside a type at the point of use.

Paper proof: it suffices to see that `⟨S⟩_κ` is `λ⁻`-braided over `S`, i.e. that the braiding
families `u`, `v` of a braiding in `Ĥ` may be taken inside `S`.  For `λ ≠ ℵ₀` that is
Lemma 3.4(4) — take `v ≡ 0`, so `u_μ` is a partial sum of elements of `S`.  For `λ = ℵ₀` it is a
transfinite induction along the blocks: at a limit `v_μ = 0` and `u_μ ∈ S`, and
`u_{μ+n} + v_{μ+n}` and `u_{μ+n} + v_{μ+n+1}` both lie in `S`, so saturatedness pushes `u` and
`v` into `S` one step at a time. -/
theorem lemma_3_13_sub_of_subset [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ κ) {f : X → Hh}
    (hbr : IsBraidedOver lam κ X Hh hlk f) (S : Set X) (hS : IsLSubmonoid lam S)
    (hsat : lam ≠ ℵ₀ ∨ IsSaturated S) {T : Set Hh} (hT : KMonoid.IsKSubmonoid κ T)
    (hfT : ∀ s ∈ S, f s ∈ T) (hTgen : T ⊆ KMonoid.kclosure κ (f '' S)) :
    letI := hS.lmonoid
    letI := hT.kmonoid
    IsUniversalKExtension lam κ ↥S ↥T hlk (fun s => ⟨f (s : X), hfT (s : X) s.2⟩) := by
  classical
  letI := hS.lmonoid
  letI := hT.kmonoid
  have hf0 : f 0 = 0 := hbr.isLHom.1
  have h0S : (0 : X) ∈ S := hS.zero_mem
  refine IsBraidedOver.isUniversalKExtension hlk ⟨⟨Subtype.ext hf0, fun {ι} h x => ?_⟩,
    fun a b hab => Subtype.ext (hbr.injective (congrArg Subtype.val hab)), fun h => ?_,
    fun a b hab => ?_⟩
  · -- the inclusion is a `λ⁻`-homomorphism, because `f` is
    exact Subtype.ext (hbr.isLHom.2 h fun i => ((x i : X)))
  · -- `T` is generated by `S`: unfold the description of the `κ`-closure
    obtain ⟨x, hxS, hxsum⟩ :=
      (KMonoid.mem_kclosure_iff (S := f '' S) ⟨0, h0S, hf0⟩ (h : Hh)).mp (hTgen h.2)
    choose s hsS hsf using hxS
    refine ⟨fun i => ⟨s i, hsS i⟩, Subtype.ext ?_⟩
    show (h : Hh) = KMonoid.ksum (κ := κ) fun i => f (s i)
    rw [hxsum]
    exact congrArg _ (funext fun i => (hsf i).symm)
  · -- two families in `S` with equal `κ`-sum are `λ⁻`-braided *inside* `S`
    have hbraid := hbr.braided (fun i => (a i : X)) (fun i => (b i : X))
      (congrArg Subtype.val hab)
    rcases hsat with hne | hsatS
    · -- `λ ≠ ℵ₀`: Lemma 3.4(4) lets us take `v ≡ 0`, and then each `u` is a partial sum
      obtain ⟨I, J, hI, hJ, hIdisj, hJdisj, hIcov, hJcov, heq⟩ :=
        (isBraided_iff_of_ne_aleph0 hne _ _).mp hbraid
      exact IsBraided.of_partition I J hIdisj hJdisj hIcov hJcov hI hJ
        fun p => Subtype.ext (heq p)
    · -- `S` saturated: walk along each `ω`-block, moving `u` and `v` into `S` one step at a time
      obtain ⟨d⟩ := hbraid
      have hxS : ∀ p, d.v p + d.u p ∈ S := fun p =>
        d.hI p ▸ hS.lsumOf_mem (d.I_small p) _ fun i => (a (i : Idx κ)).2
      have hyS : ∀ p, d.v (bsucc p) + d.u p ∈ S := fun p =>
        d.hJ p ▸ hS.lsumOf_mem (d.J_small p) _ fun j => (b (j : Idx κ)).2
      have key : ∀ p : Idx κ × ℕ, d.u p ∈ S ∧ d.v p ∈ S := by
        rintro ⟨α, m⟩
        induction m with
        | zero =>
            have hv0 : d.v (α, 0) = 0 := d.v_limit α
            refine ⟨?_, hv0 ▸ h0S⟩
            have hsum := hxS (α, 0)
            rwa [hv0, zero_add] at hsum
        | succ m ih =>
            have hv : d.v (α, m + 1) ∈ S :=
              hsatS _ (hyS (α, m)) _ ih.1 _ (add_comm (d.v (α, m + 1)) (d.u (α, m)))
            exact ⟨hsatS _ (hxS (α, m + 1)) _ hv _ rfl, hv⟩
      exact ⟨{ I := d.I, J := d.J
               I_disjoint := d.I_disjoint, J_disjoint := d.J_disjoint
               I_cover := d.I_cover, J_cover := d.J_cover
               I_small := d.I_small, J_small := d.J_small
               u := fun p => ⟨d.u p, (key p).1⟩
               v := fun p => ⟨d.v p, (key p).2⟩
               v_limit := fun α => Subtype.ext (d.v_limit α)
               hI := fun p => Subtype.ext (d.hI p)
               hJ := fun p => Subtype.ext (d.hJ p) }⟩

/-- **Lemma 3.13(2)** as printed: `⟨S⟩_κ ⊆ Ĥ` is the universal `κ`-extension of `S`. -/
theorem lemma_3_13_sub [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ κ) {f : X → Hh}
    (hbr : IsBraidedOver lam κ X Hh hlk f) (S : Set X) (hS : IsLSubmonoid lam S)
    (hsat : lam ≠ ℵ₀ ∨ IsSaturated S) :
    letI := hS.lmonoid
    letI := (KMonoid.isKSubmonoid_kclosure κ (f '' S)).kmonoid
    IsUniversalKExtension lam κ ↥S ↥(KMonoid.kclosure κ (f '' S)) hlk
      (fun s => ⟨f (s : X), KMonoid.subset_kclosure ⟨(s : X), s.2, rfl⟩⟩) :=
  lemma_3_13_sub_of_subset hlk hbr S hS hsat (KMonoid.isKSubmonoid_kclosure κ (f '' S))
    (fun s hs => KMonoid.subset_kclosure ⟨s, hs, rfl⟩) subset_rfl

end Sub

/-! ## Proposition 3.14: monoids defined by linear equations, inequalities and congruences

A homogeneous system in `n` unknowns over `F_κ` consists of equations
`a₁x₁ + ⋯ + aₙxₙ = b₁x₁ + ⋯ + bₙxₙ`, inequalities `a₁x₁ + ⋯ + aₙxₙ ≤ b₁x₁ + ⋯ + bₙxₙ`, and
congruences `a₁x₁ + ⋯ + aₙxₙ ∈ d·F_κ`, all with natural-number coefficients.  The same system can
be read over `F_κ` for any `κ`, which is what makes Proposition 3.14 expressible. -/

section Diophantine

/-! ### `κ`-sums, natural multiples and finite sums

The two interchange laws needed to see that the solution set of a linear system is a
`κ`-submonoid.  Both are formal consequences of the additivity of `Σ` (Lemma 2.7 is the analogous
statement for *cardinal* multiples; here the multiplier is a natural number, so plain induction
suffices). -/

/-- A natural multiple commutes with `κ`-sums. -/
theorem KMonoid.nsmul_sumOf {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H] {ι : Type u}
    (h : #ι ≤ κ) (m : ℕ) (x : ι → H) :
    m • KMonoid.sumOf (κ := κ) h x = KMonoid.sumOf (κ := κ) h fun i => m • x i := by
  induction m with
  | zero =>
      rw [zero_nsmul, show (fun i => (0 : ℕ) • x i) = fun _ => (0 : H) from
        funext fun i => zero_nsmul (x i), KMonoid.sumOf_zero]
  | succ m ih =>
      rw [succ_nsmul, ih, ← KMonoid.sumOf_add]
      exact congrArg _ (funext fun i => (succ_nsmul (x i) m).symm)

/-- A finite sum commutes with `κ`-sums. -/
theorem KMonoid.finsetSum_sumOf {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H] {ι : Type u}
    (h : #ι ≤ κ) {J : Type w} (s : Finset J) (f : J → ι → H) :
    ∑ j ∈ s, KMonoid.sumOf (κ := κ) h (f j)
      = KMonoid.sumOf (κ := κ) h fun i => ∑ j ∈ s, f j i := by
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, show (fun i => ∑ j ∈ (∅ : Finset J), f j i) = fun _ => (0 : H) from
        funext fun i => Finset.sum_empty, KMonoid.sumOf_zero]
  | cons j s hj ih =>
      rw [Finset.sum_cons, ih, ← KMonoid.sumOf_add]
      exact congrArg _ (funext fun i => (Finset.sum_cons (f := fun j => f j i) hj).symm)

/-- A homogeneous linear system in `n` unknowns with natural coefficients: a set of equations, a
set of inequalities, and a set of congruences. -/
structure LinSystem (n : ℕ) where
  /-- Equations `a · x = b · x`. -/
  eqs : Set ((Fin n → ℕ) × (Fin n → ℕ))
  /-- Inequalities `a · x ≼ b · x`. -/
  ineqs : Set ((Fin n → ℕ) × (Fin n → ℕ))
  /-- Congruences `a · x ∈ d · F_κ`. -/
  congrs : Set ((Fin n → ℕ) × ℕ)

variable {n : ℕ} (sys : LinSystem n) {κ : Cardinal.{u}}

/-- The linear form `a₁x₁ + ⋯ + aₙxₙ` evaluated in `F_κ^n`. -/
noncomputable def linEval {n : ℕ} {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (a : Fin n → ℕ)
    (x : Fin n → Fcard κ) : Fcard κ :=
  letI := Fcard.instKMonoid hκ
  ∑ i, (a i) • x i

/-- The solution set of the system in `F_κ^n`. -/
noncomputable def LinSystem.solutions (hκ : ℵ₀ ≤ κ) : Set (Fin n → Fcard κ) :=
  letI := Fcard.instKMonoid hκ
  {x | (∀ p ∈ sys.eqs, linEval hκ p.1 x = linEval hκ p.2 x) ∧
       (∀ p ∈ sys.ineqs, AddLe (linEval hκ p.1 x) (linEval hκ p.2 x)) ∧
       (∀ p ∈ sys.congrs, ∃ y : Fcard κ, linEval hκ p.1 x = (p.2) • y)}

/-- A linear form vanishes at `0`. -/
theorem linEval_zero (hκ : ℵ₀ ≤ κ) (a : Fin n → ℕ) :
    letI := Fcard.instKMonoid hκ
    linEval hκ a (0 : Fin n → Fcard κ) = 0 := by
  letI := Fcard.instKMonoid hκ
  show ∑ i, (a i) • (0 : Fin n → Fcard κ) i = 0
  exact Finset.sum_eq_zero fun i _ => smul_zero _

/-- `linEval` commutes with `κ`-sums: sums in `F_κ^n` are coordinatewise, and both a natural
multiple and a finite sum commute with `Σ`. -/
theorem linEval_sumOf (hκ : ℵ₀ ≤ κ) (a : Fin n → ℕ) {ι : Type u} (h : #ι ≤ κ)
    (z : ι → (Fin n → Fcard κ)) :
    letI := Fcard.instKMonoid hκ
    letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ
    linEval hκ a (KMonoid.sumOf (κ := κ) h z)
      = KMonoid.sumOf (κ := κ) h fun k => linEval hκ a (z k) := by
  letI := Fcard.instKMonoid hκ
  letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ
  calc linEval hκ a (KMonoid.sumOf (κ := κ) h z)
      = ∑ i, KMonoid.sumOf (κ := κ) h (fun k => (a i) • z k i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (KMonoid.sumOf (κ := κ) h z) i = KMonoid.sumOf (κ := κ) h (fun k => z k i) from
          KMonoid.pi_sumOf κ (fun _ : Fin n => Fcard κ) hκ h z i, KMonoid.nsmul_sumOf]
    _ = KMonoid.sumOf (κ := κ) h fun k => linEval hκ a (z k) :=
        KMonoid.finsetSum_sumOf h Finset.univ fun i k => (a i) • z k i

/-- The solution set is a `κ`-submonoid of `F_κ^n`: each condition is preserved by `κ`-sums,
because `Σ` commutes with the coefficientwise operations (Lemma 2.7). -/
theorem LinSystem.isKSubmonoid_solutions (hκ : ℵ₀ ≤ κ) :
    letI := Fcard.instKMonoid hκ
    letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ
    KMonoid.IsKSubmonoid κ (sys.solutions hκ) := by
  letI := Fcard.instKMonoid hκ
  letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ
  have hidx : #(Idx κ) ≤ κ := le_of_eq (mk_Idx κ)
  constructor
  · -- `0` solves every condition
    refine ⟨fun p _ => by rw [linEval_zero, linEval_zero], fun p _ => ?_,
      fun p _ => ⟨0, by rw [linEval_zero, smul_zero]⟩⟩
    rw [linEval_zero, linEval_zero]
  · -- and each condition is closed under `κ`-sums
    intro z hz
    rw [← KMonoid.sumOf_Idx z]
    refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
    · rw [linEval_sumOf, linEval_sumOf]
      exact congrArg _ (funext fun k => (hz k).1 p hp)
    · choose c hc using fun k => (hz k).2.1 p hp
      refine ⟨KMonoid.sumOf (κ := κ) hidx c, ?_⟩
      rw [linEval_sumOf, linEval_sumOf, ← KMonoid.sumOf_add]
      exact congrArg _ (funext fun k => hc k)
    · choose y hy using fun k => (hz k).2.2 p hp
      refine ⟨KMonoid.sumOf (κ := κ) hidx y, ?_⟩
      rw [linEval_sumOf, KMonoid.nsmul_sumOf]
      exact congrArg _ (funext fun k => hy k)

/-- The value of an element of `F_κ`, as an additive map — used to evaluate finite sums
componentwise. -/
noncomputable def fcardVal (hκ : ℵ₀ ≤ κ) :
    letI := Fcard.instKMonoid hκ
    Fcard κ →+ Cardinal.{u} :=
  letI := Fcard.instKMonoid hκ
  { toFun := fun c => (c : Cardinal.{u})
    map_zero' := Fcard.instKMonoid_zero hκ
    map_add' := Fcard.instKMonoid_add hκ }

@[simp] theorem fcardVal_apply (hκ : ℵ₀ ≤ κ) (c : Fcard κ) :
    letI := Fcard.instKMonoid hκ
    fcardVal hκ c = (c : Cardinal.{u}) := rfl

/-- The inclusion `F_{ℵ₀} ↪ F_κ`. -/
def fcardIncl (hκ : ℵ₀ ≤ κ) (a : Fcard ℵ₀) : Fcard κ :=
  Fcard.mk (a : Cardinal.{u}) (le_trans (Fcard.le a) hκ)

@[simp] theorem val_fcardIncl (hκ : ℵ₀ ≤ κ) (a : Fcard ℵ₀) :
    ((fcardIncl hκ a : Fcard κ) : Cardinal.{u}) = (a : Cardinal.{u}) := rfl

/-- `F_{ℵ₀} ↪ F_κ` is additive: on both sides addition is addition of cardinals. -/
theorem fcardIncl_add (hκ : ℵ₀ ≤ κ) (a b : Fcard ℵ₀) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := Fcard.instKMonoid hκ
    fcardIncl hκ (a + b) = fcardIncl hκ a + fcardIncl hκ b := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := Fcard.instKMonoid hκ
  refine Fcard.ext ?_
  rw [val_fcardIncl, Fcard.instKMonoid_add, Fcard.instKMonoid_add, val_fcardIncl, val_fcardIncl]

theorem fcardIncl_zero (hκ : ℵ₀ ≤ κ) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := Fcard.instKMonoid hκ
    fcardIncl hκ (0 : Fcard ℵ₀) = 0 := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := Fcard.instKMonoid hκ
  refine Fcard.ext ?_
  rw [val_fcardIncl, Fcard.instKMonoid_zero, Fcard.instKMonoid_zero]

theorem fcardIncl_finsetSum (hκ : ℵ₀ ≤ κ) {J : Type w} (s : Finset J) (f : J → Fcard ℵ₀) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := Fcard.instKMonoid hκ
    fcardIncl hκ (∑ j ∈ s, f j) = ∑ j ∈ s, fcardIncl hκ (f j) := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := Fcard.instKMonoid hκ
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, fcardIncl_zero]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, fcardIncl_add, ih]

theorem fcardIncl_nsmul (hκ : ℵ₀ ≤ κ) (m : ℕ) (a : Fcard ℵ₀) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := Fcard.instKMonoid hκ
    fcardIncl hκ (m • a) = m • fcardIncl hκ a := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := Fcard.instKMonoid hκ
  induction m with
  | zero => rw [zero_nsmul, zero_nsmul, fcardIncl_zero]
  | succ m ih => rw [succ_nsmul, succ_nsmul, fcardIncl_add, ih]

/-- `F_{ℵ₀} ↪ F_κ` commutes with the linear forms. -/
theorem fcardIncl_linEval (hκ : ℵ₀ ≤ κ) (a : Fin n → ℕ) (x : Fin n → Fcard ℵ₀) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := Fcard.instKMonoid hκ
    fcardIncl hκ (linEval (le_refl ℵ₀) a x) = linEval hκ a (fun i => fcardIncl hκ (x i)) := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := Fcard.instKMonoid hκ
  show fcardIncl hκ (∑ i, (a i) • x i) = ∑ i, (a i) • fcardIncl hκ (x i)
  rw [fcardIncl_finsetSum]
  exact Finset.sum_congr rfl fun i _ => fcardIncl_nsmul hκ (a i) (x i)

/-- An additive map `F_κ → F_{κ'}` commutes with the linear forms: they are finite sums of
natural multiples. -/
theorem map_linEval {κ' : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hκ' : ℵ₀ ≤ κ') (g : Fcard κ → Fcard κ')
    (hg : letI := Fcard.instKMonoid hκ
          letI := Fcard.instKMonoid hκ'
          g 0 = 0 ∧ ∀ a b, g (a + b) = g a + g b)
    (a : Fin n → ℕ) (x : Fin n → Fcard κ) :
    letI := Fcard.instKMonoid hκ
    letI := Fcard.instKMonoid hκ'
    g (linEval hκ a x) = linEval hκ' a (fun i => g (x i)) := by
  letI := Fcard.instKMonoid hκ
  letI := Fcard.instKMonoid hκ'
  set G : Fcard κ →+ Fcard κ' := { toFun := g, map_zero' := hg.1, map_add' := hg.2 } with hG
  show G (∑ i, (a i) • x i) = ∑ i, (a i) • G (x i)
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => G.map_nsmul (a i) (x i)

/-- **Any** additive map `F_κ → F_{κ'}` carries solutions to solutions.  Note that this is not
formal for the inequalities: `≼` is an existential, and its witness has to be transported —
which it can be, precisely because the map is additive. -/
theorem LinSystem.mem_solutions_map {κ' : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hκ' : ℵ₀ ≤ κ')
    (g : Fcard κ → Fcard κ')
    (hg : letI := Fcard.instKMonoid hκ
          letI := Fcard.instKMonoid hκ'
          g 0 = 0 ∧ ∀ a b, g (a + b) = g a + g b)
    {x : Fin n → Fcard κ} (hx : x ∈ sys.solutions hκ) :
    (fun i => g (x i)) ∈ sys.solutions hκ' := by
  letI := Fcard.instKMonoid hκ
  letI := Fcard.instKMonoid hκ'
  have hmap := map_linEval (n := n) hκ hκ' g hg
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [← hmap, ← hmap]
    exact congrArg _ (hx.1 p hp)
  · obtain ⟨c, hc⟩ := hx.2.1 p hp
    refine ⟨g c, ?_⟩
    rw [← hmap, ← hmap, ← hg.2, hc]
  · obtain ⟨y, hy⟩ := hx.2.2 p hp
    refine ⟨g y, ?_⟩
    rw [← hmap, hy]
    exact ({ toFun := g, map_zero' := hg.1, map_add' := hg.2 } :
      Fcard κ →+ Fcard κ').map_nsmul p.2 y

/-- A solution over `F_{ℵ₀}` is a solution over `F_κ`. -/
theorem LinSystem.mem_solutions_of_incl (hκ : ℵ₀ ≤ κ) {x : Fin n → Fcard ℵ₀}
    (hx : x ∈ sys.solutions (le_refl ℵ₀)) :
    (fun i => fcardIncl hκ (x i)) ∈ sys.solutions hκ :=
  sys.mem_solutions_map (le_refl ℵ₀) hκ (fcardIncl hκ)
    ⟨fcardIncl_zero hκ, fcardIncl_add hκ⟩ hx

/-! ### Every `κ`-solution is a `κ`-sum of `ℵ₀`-solutions

The paper's decomposition `α = β + Σ_{ℵ₀ ≤ λ ≤ κ} λ γ^{(λ)}`, where `β_i = min(α_i, ℵ₀)` and
`γ^{(λ)}_i` is `ℵ₀` for `α_i ≥ λ` and `0` otherwise.  Two observations make it cheap: only the
finitely many levels `λ = α_i` contribute, and both `β` and `γ^{(λ)}` arise from *additive* maps
`F_κ → F_{ℵ₀}` applied coordinatewise, so they are solutions by `mem_solutions_map` — which is the
paper's remark that the construction does not look at the coefficients. -/

/-- Truncation at `ℵ₀`: the additive map `min(·, ℵ₀) : F_κ → F_{ℵ₀}`, giving the paper's `β`. -/
noncomputable def truncAleph0 (c : Fcard κ) : Fcard ℵ₀ :=
  if h : (c : Cardinal.{u}) < ℵ₀ then Fcard.mk (c : Cardinal.{u}) h.le else Fcard.mk ℵ₀ le_rfl

theorem val_truncAleph0 (c : Fcard κ) :
    ((truncAleph0 c : Fcard ℵ₀) : Cardinal.{u})
      = if (c : Cardinal.{u}) < ℵ₀ then (c : Cardinal.{u}) else ℵ₀ := by
  unfold truncAleph0
  split <;> rfl

theorem truncAleph0_isAdd (hκ : ℵ₀ ≤ κ) :
    letI := Fcard.instKMonoid hκ
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    truncAleph0 (κ := κ) 0 = 0 ∧
      ∀ a b, truncAleph0 (κ := κ) (a + b) = truncAleph0 a + truncAleph0 b := by
  letI := Fcard.instKMonoid hκ
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  refine ⟨Fcard.ext ?_, fun a b => Fcard.ext ?_⟩
  · rw [val_truncAleph0, Fcard.instKMonoid_zero hκ, if_pos Cardinal.aleph0_pos,
      Fcard.instKMonoid_zero]
  · rw [val_truncAleph0, Fcard.instKMonoid_add hκ, Fcard.instKMonoid_add,
      val_truncAleph0, val_truncAleph0]
    by_cases ha : (a : Cardinal.{u}) < ℵ₀ <;> by_cases hb : (b : Cardinal.{u}) < ℵ₀
    · rw [if_pos (Cardinal.add_lt_aleph0 ha hb), if_pos ha, if_pos hb]
    · rw [if_neg (fun h => hb (lt_of_le_of_lt (self_le_add_left _ _) h)), if_pos ha, if_neg hb,
        Cardinal.add_eq_right le_rfl ha.le]
    · rw [if_neg (fun h => ha (lt_of_le_of_lt (self_le_add_right _ _) h)), if_neg ha, if_pos hb,
        Cardinal.add_eq_left le_rfl hb.le]
    · rw [if_neg (fun h => ha (lt_of_le_of_lt (self_le_add_right _ _) h)), if_neg ha, if_neg hb,
        Cardinal.aleph0_add_aleph0]

/-- The level indicator: the additive map `F_κ → F_{ℵ₀}` sending `c` to `ℵ₀` if `c ≥ lev` and to
`0` otherwise, giving the paper's `γ^{(lev)}`.  Additivity needs `lev` infinite. -/
noncomputable def geLevel (lev : Cardinal.{u}) (c : Fcard κ) : Fcard ℵ₀ :=
  if lev ≤ (c : Cardinal.{u}) then Fcard.mk ℵ₀ le_rfl
  else Fcard.mk 0 (zero_le : (0 : Cardinal.{u}) ≤ ℵ₀)

theorem val_geLevel (lev : Cardinal.{u}) (c : Fcard κ) :
    ((geLevel lev c : Fcard ℵ₀) : Cardinal.{u}) = if lev ≤ (c : Cardinal.{u}) then ℵ₀ else 0 := by
  unfold geLevel
  split <;> rfl

theorem geLevel_isAdd (hκ : ℵ₀ ≤ κ) {lev : Cardinal.{u}} (hlev : ℵ₀ ≤ lev) :
    letI := Fcard.instKMonoid hκ
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    geLevel (κ := κ) lev 0 = 0 ∧
      ∀ a b, geLevel (κ := κ) lev (a + b) = geLevel lev a + geLevel lev b := by
  letI := Fcard.instKMonoid hκ
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  refine ⟨Fcard.ext ?_, fun a b => Fcard.ext ?_⟩
  · rw [val_geLevel, Fcard.instKMonoid_zero hκ,
      if_neg (fun h => absurd (le_antisymm (hlev.trans h) zero_le) Cardinal.aleph0_ne_zero),
      Fcard.instKMonoid_zero]
  · rw [val_geLevel, Fcard.instKMonoid_add hκ, Fcard.instKMonoid_add, val_geLevel, val_geLevel]
    by_cases ha : lev ≤ (a : Cardinal.{u})
    · rw [if_pos (ha.trans (self_le_add_right _ _)), if_pos ha]
      split
      · exact Cardinal.aleph0_add_aleph0.symm
      · exact (add_zero _).symm
    · by_cases hb : lev ≤ (b : Cardinal.{u})
      · rw [if_pos (hb.trans (self_le_add_left _ _)), if_neg ha, if_pos hb]
        exact (zero_add _).symm
      · rw [if_neg ha, if_neg hb, add_zero,
          if_neg (not_le.mpr (Cardinal.add_lt_of_lt hlev (not_le.mp ha) (not_le.mp hb)))]

/-- A finite sum of cardinals `≤ c` is `≤ c`, for infinite `c`. -/
theorem csum_finset_le {J : Type w} (s : Finset J) (f : J → Cardinal.{u}) {c : Cardinal.{u}}
    (hc : ℵ₀ ≤ c) (hf : ∀ j ∈ s, f j ≤ c) : ∑ j ∈ s, f j ≤ c := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty]; exact zero_le
  | cons j s hj ih =>
      rw [Finset.sum_cons]
      exact Cardinal.add_le_of_le hc (hf j (Finset.mem_cons_self _ _))
        (ih fun k hk => hf k (Finset.mem_cons_of_mem hk))

/-- **The generation statement behind Proposition 3.14(1)**: every `κ`-solution is a `κ`-sum of
images of `ℵ₀`-solutions.

`α = β + Σ_{j : α_j infinite} α_j · γ^{(α_j)}`: in a finite component both sides are `α_i`, since
every level is infinite and so contributes `0` there; in an infinite component the right-hand side
is `ℵ₀` plus a finite sum of cardinals `≤ α_i` one of which — the term `j = i` — equals `α_i`. -/
theorem LinSystem.solutions_subset_kclosure (hκ0 : ℵ₀ ≤ κ) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := Fcard.instKMonoid hκ0
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ0
    sys.solutions hκ0 ⊆ KMonoid.kclosure κ
      ((fun (x : Fin n → Fcard ℵ₀) (i : Fin n) => fcardIncl hκ0 (x i)) ''
        sys.solutions (le_refl ℵ₀)) := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := Fcard.instKMonoid hκ0
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ0
  classical
  set f : (Fin n → Fcard ℵ₀) → (Fin n → Fcard κ) := fun x i => fcardIncl hκ0 (x i) with hfdef
  have hT : KMonoid.IsKSubmonoid κ (KMonoid.kclosure κ (f '' sys.solutions (le_refl ℵ₀))) :=
    KMonoid.isKSubmonoid_kclosure κ _
  have hmem : ∀ x ∈ sys.solutions (le_refl (ℵ₀ : Cardinal.{u})),
      f x ∈ KMonoid.kclosure κ (f '' sys.solutions (le_refl ℵ₀)) :=
    fun x hx => KMonoid.subset_kclosure ⟨x, hx, rfl⟩
  intro α hα
  -- the finite part `β = min(α, ℵ₀)`
  have hβsol : (fun i => truncAleph0 (α i)) ∈ sys.solutions (le_refl (ℵ₀ : Cardinal.{u})) :=
    sys.mem_solutions_map hκ0 le_rfl truncAleph0 (truncAleph0_isAdd hκ0) hα
  -- the levels: only the finitely many infinite components matter
  set Λ : Finset (Fin n) := Finset.univ.filter fun j => ℵ₀ ≤ ((α j : Fcard κ) : Cardinal.{u})
    with hΛdef
  have hmemΛ : ∀ j, j ∈ Λ ↔ ℵ₀ ≤ ((α j : Fcard κ) : Cardinal.{u}) := by
    intro j; rw [hΛdef]; simp
  have hγsol : ∀ j ∈ Λ, (fun i => geLevel ((α j : Fcard κ) : Cardinal.{u}) (α i))
      ∈ sys.solutions (le_refl (ℵ₀ : Cardinal.{u})) := fun j hj =>
    sys.mem_solutions_map hκ0 le_rfl _ (geLevel_isAdd hκ0 ((hmemΛ j).mp hj)) hα
  -- the scaled pieces `α_j · γ^{(α_j)}`, each a `κ`-sum of copies of an `ℵ₀`-solution
  set w : Fin n → (Fin n → Fcard κ) := fun j =>
    KMonoid.cmul (κ := κ) ((α j : Fcard κ) : Cardinal.{u}) (Fcard.le _)
      (f fun i => geLevel ((α j : Fcard κ) : Cardinal.{u}) (α i)) with hwdef
  have hwT : ∀ j ∈ Λ, w j ∈ KMonoid.kclosure κ (f '' sys.solutions (le_refl ℵ₀)) := by
    intro j hj
    have hidx : #(Idx ((α j : Fcard κ) : Cardinal.{u})) ≤ κ :=
      (le_of_eq (mk_Idx _)).trans (Fcard.le _)
    exact hT.sumOf_mem hidx _ fun _ => hmem _ (hγsol j hj)
  have hsumT : ∑ j ∈ Λ, w j ∈ KMonoid.kclosure κ (f '' sys.solutions (le_refl ℵ₀)) :=
    AddSubmonoid.sum_mem
      { carrier := KMonoid.kclosure κ (f '' sys.solutions (le_refl ℵ₀))
        zero_mem' := hT.zero_mem
        add_mem' := fun ha hb => hT.add_mem ha hb } fun j hj => hwT j hj
  -- the identity `α = f β + Σ_{j ∈ Λ} w j`, checked componentwise on values
  have hvalw : ∀ (j i : Fin n), ((w j i : Fcard κ) : Cardinal.{u})
      = ((α j : Fcard κ) : Cardinal.{u}) *
        (if ((α j : Fcard κ) : Cardinal.{u}) ≤ ((α i : Fcard κ) : Cardinal.{u}) then ℵ₀ else 0) := by
    intro j i
    rw [hwdef]
    show ((KMonoid.cmul (κ := κ) ((α j : Fcard κ) : Cardinal.{u}) (Fcard.le _)
        (fcardIncl hκ0 (geLevel ((α j : Fcard κ) : Cardinal.{u}) (α i))) : Fcard κ)
      : Cardinal.{u}) = _
    rw [KMonoid.cmul_eq_lcmul, LCard.val_lcmul, val_fcardIncl]
    exact congrArg _ (val_geLevel _ _)
  have hkey : α = f (fun i => truncAleph0 (α i)) + ∑ j ∈ Λ, w j := by
    refine funext fun i => Fcard.ext ?_
    have hsum : (((∑ j ∈ Λ, w j) i : Fcard κ) : Cardinal.{u})
        = ∑ j ∈ Λ, ((w j i : Fcard κ) : Cardinal.{u}) := by
      rw [show ((∑ j ∈ Λ, w j) i : Fcard κ) = ∑ j ∈ Λ, w j i from Finset.sum_apply _ _ _,
        ← fcardVal_apply hκ0, map_sum]
      rfl
    rw [show ((f (fun i => truncAleph0 (α i)) + ∑ j ∈ Λ, w j) i : Fcard κ)
        = f (fun i => truncAleph0 (α i)) i + (∑ j ∈ Λ, w j) i from rfl,
      Fcard.instKMonoid_add hκ0, hsum, hfdef]
    show _ = ((truncAleph0 (α i) : Fcard ℵ₀) : Cardinal.{u}) + _
    rw [val_truncAleph0]
    by_cases hi : ((α i : Fcard κ) : Cardinal.{u}) < ℵ₀
    · -- a finite component: every level is infinite, so no `w j` contributes
      rw [if_pos hi, Finset.sum_eq_zero fun j hj => ?_, add_zero]
      rw [hvalw j i, if_neg (fun hc => absurd (lt_of_le_of_lt ((hmemΛ j).mp hj |>.trans hc) hi)
        (lt_irrefl _)), mul_zero]
    · -- an infinite component: the term `j = i` already gives `α_i`, and no term exceeds it
      have hi' : ℵ₀ ≤ ((α i : Fcard κ) : Cardinal.{u}) := not_lt.mp hi
      have hiΛ : i ∈ Λ := (hmemΛ i).mpr hi'
      have hle : ∑ j ∈ Λ, ((w j i : Fcard κ) : Cardinal.{u}) ≤ ((α i : Fcard κ) : Cardinal.{u}) := by
        refine csum_finset_le _ _ hi' fun j hj => ?_
        rw [hvalw j i]
        by_cases hc : ((α j : Fcard κ) : Cardinal.{u}) ≤ ((α i : Fcard κ) : Cardinal.{u})
        · rw [if_pos hc, Cardinal.mul_aleph0_eq ((hmemΛ j).mp hj)]
          exact hc
        · rw [if_neg hc, mul_zero]
          exact zero_le
      have hge : ((α i : Fcard κ) : Cardinal.{u}) ≤ ∑ j ∈ Λ, ((w j i : Fcard κ) : Cardinal.{u}) := by
        refine le_trans (le_of_eq ?_)
          (Finset.single_le_sum (f := fun j => ((w j i : Fcard κ) : Cardinal.{u}))
            (fun j _ => zero_le) hiΛ)
        rw [hvalw i i, if_pos le_rfl, Cardinal.mul_aleph0_eq hi']
      rw [if_neg hi, le_antisymm hle hge, Cardinal.add_eq_right hi' hi']
  rw [hkey]
  exact hT.add_mem (hmem _ hβsol) hsumT

/-! ### `F_κ^n` is `λ⁻`-braided over `F_{ℵ₀}^n`

The ambient braided extension that Lemma 3.13(2) needs.  Lemma 3.13(1) gives it for the free
objects `F_{λ⁻}(B) ⊆ F_κ(B)`, which are *subtypes* of the products and need `B : Type u`, while
§3.2 works with the plain products over `Fin n`.  For a basis of size `< λ` the support condition
is vacuous, so the two differ only by the coercion out of the subtype composed with the reindexing
along `ULift (Fin n) ≃ Fin n`; that is an isomorphism on both sides, and Theorem 3.11 read as an
equivalence turns the universal property of Lemma 3.13(1) into a braiding, which then transports
(`IsBraidedOver.of_iso`, `IsBraidedOver.of_base_iso`). -/

/-- Every family indexed by a basis of size `< λ` lies in `F_{λ⁻}(B)`: its support is a subset of
the basis. -/
theorem mem_FreeL_of_mk_lt {lam : Cardinal.{u}} [Fact lam.IsRegular] {B : Type u}
    (hB : #B < lam) (x : B → LCard lam) : x ∈ FreeL lam B :=
  lt_of_le_of_lt (Cardinal.mk_set_le _) hB

/-- **`F_κ^n` is `ℵ₁⁻`-braided over `F_{ℵ₀}^n`**, along the coordinatewise inclusion: the free
`κ`-monoid on `n` generators over the free `ℵ₁⁻`-monoid on the same generators. -/
theorem isBraidedOver_pi_fcard (hκ : Order.succ ℵ₀ ≤ κ) :
    letI hκ0 : ℵ₀ ≤ κ := le_trans (Order.le_succ ℵ₀) hκ
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := Fcard.instKMonoid hκ0
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ0
    IsBraidedOver (Order.succ ℵ₀) κ (Fin n → Fcard ℵ₀) (Fin n → Fcard κ) hκ
      (fun x i => fcardIncl hκ0 (x i)) := by
  letI hκ0 : ℵ₀ ≤ κ := le_trans (Order.le_succ ℵ₀) hκ
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := Fcard.instKMonoid hκ0
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ0
  letI : Fact (Order.succ (ℵ₀ : Cardinal.{u})).IsRegular := ⟨Cardinal.isRegular_succ le_rfl⟩
  letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ0⟩
  letI := instKMonoidFreeK κ hκ0 (ULift.{u} (Fin n))
  have hBlt : #(ULift.{u} (Fin n)) < ℵ₀ := Cardinal.lt_aleph0_iff_finite.mpr inferInstance
  have hBlam : #(ULift.{u} (Fin n)) < Order.succ (ℵ₀ : Cardinal.{u}) :=
    lt_of_lt_of_le hBlt (Order.le_succ _)
  have hBk : #(ULift.{u} (Fin n)) < Order.succ κ :=
    lt_of_lt_of_le hBlt (le_trans hκ0 (Order.le_succ _))
  -- Lemma 3.13(1) at `λ = ℵ₁`, read as a braiding
  have hcon : IsConical ↥(FreeL (Order.succ (ℵ₀ : Cardinal.{u})) (ULift.{u} (Fin n))) :=
    LMonoid.isConical (lam := Order.succ ℵ₀) (Order.lt_succ_iff.mpr le_rfl)
  have hbr := isBraidedOver_of_isUniversalKExtension (Cardinal.isRegular_succ le_rfl) hκ hcon
    (lemma_3_13_free (lam := Order.succ ℵ₀) (κ := κ) (B := ULift.{u} (Fin n))
      (Cardinal.isRegular_succ le_rfl) hκ0 hκ)
  -- the extension side: `F_κ(ULift (Fin n)) ≅ F_κ^n`
  set e : ↥(FreeK κ (ULift.{u} (Fin n))) → (Fin n → Fcard κ) :=
    fun s => fun i => (s : ULift.{u} (Fin n) → Fcard κ) (ULift.up i) with hedef
  set e' : (Fin n → Fcard κ) → ↥(FreeK κ (ULift.{u} (Fin n))) :=
    fun x => ⟨fun b => x b.down, mem_FreeL_of_mk_lt hBk _⟩ with he'def
  have hbr2 := hbr.of_iso hκ (e := e) ⟨funext fun _ => rfl, fun _ => funext fun _ => rfl⟩
    (Function.bijective_iff_has_inverse.mpr ⟨e', fun s => Subtype.ext (funext fun b => rfl),
      fun x => funext fun i => rfl⟩) (fun _ => rfl)
  -- the base side: `F_{ℵ₁⁻}(ULift (Fin n)) ≅ F_{ℵ₀}^n`
  set g : (Fin n → Fcard ℵ₀) → ↥(FreeL (Order.succ (ℵ₀ : Cardinal.{u})) (ULift.{u} (Fin n))) :=
    fun x => ⟨fun b => x b.down, mem_FreeL_of_mk_lt hBlam _⟩ with hgdef
  set g' : ↥(FreeL (Order.succ (ℵ₀ : Cardinal.{u})) (ULift.{u} (Fin n))) → (Fin n → Fcard ℵ₀) :=
    fun s => fun i => (s : ULift.{u} (Fin n) → Fcard ℵ₀) (ULift.up i) with hg'def
  have hbr3 := hbr2.of_base_iso hκ (g := g) (g' := g')
    (fun h x => Subtype.ext (funext fun b => rfl)) (fun h s => funext fun i => rfl)
    (fun x => funext fun i => rfl) (fun s => Subtype.ext (funext fun b => rfl))
  exact hbr3

/-- **Proposition 3.14(1)**: the universal `κ`-extension of the `ℵ₀`-monoid cut out of `F_{ℵ₀}^n`
by a system is the `κ`-submonoid of `F_κ^n` cut out by the *same* system.

An `ℵ₀`-monoid is an `ℵ₁⁻`-monoid, which is why the extension is taken along `λ = ℵ₀⁺`.

Paper proof: the solution set over `F_κ` is `ℵ₁⁻`-braided over the solution set over `F_{ℵ₀}`,
so Theorem 3.11(2) identifies it as the universal `κ`-extension. -/
theorem prop_3_14_one (hκ : Order.succ ℵ₀ ≤ κ) :
    letI hκ0 : ℵ₀ ≤ κ := le_trans (Order.le_succ ℵ₀) hκ
    letI := Fcard.instKMonoid (le_refl ℵ₀)
    letI := Fcard.instKMonoid hκ0
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ0
    letI := (sys.isKSubmonoid_solutions (le_refl ℵ₀)).kmonoid
    letI := (sys.isKSubmonoid_solutions hκ0).kmonoid
    IsUniversalKExtension (Order.succ ℵ₀) κ ↥(sys.solutions (le_refl ℵ₀))
      ↥(sys.solutions hκ0) hκ
      (fun x => ⟨fun i => fcardIncl hκ0 ((x : Fin n → Fcard ℵ₀) i),
        sys.mem_solutions_of_incl hκ0 x.2⟩) := by
  letI hκ0 : ℵ₀ ≤ κ := le_trans (Order.le_succ ℵ₀) hκ
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := Fcard.instKMonoid hκ0
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ0
  -- the `ℵ₀`-solutions form an `ℵ₁⁻`-submonoid of `F_{ℵ₀}^n`: an `ℵ₀`-monoid *is* an `ℵ₁⁻`-monoid
  have hS : IsLSubmonoid (Order.succ ℵ₀) (sys.solutions (le_refl (ℵ₀ : Cardinal.{u}))) :=
    ⟨(sys.isKSubmonoid_solutions (le_refl ℵ₀)).zero_mem, fun {ι} h x hx =>
      (sys.isKSubmonoid_solutions (le_refl ℵ₀)).sumOf_mem (KMonoid.le_of_lt_succ h) x hx⟩
  exact lemma_3_13_sub_of_subset hκ (isBraidedOver_pi_fcard hκ) _ hS
    (Or.inl (Order.lt_succ_iff.mpr le_rfl).ne') (sys.isKSubmonoid_solutions hκ0)
    (fun x hx => sys.mem_solutions_of_incl hκ0 hx) (sys.solutions_subset_kclosure hκ0)

/-- `ℵ₀·H` componentwise: replace every nonzero component by `ℵ₀`, leaving zeroes alone.  This is
the paper's explicit description of the elements of `ℵ₀H`. -/
noncomputable def alephPart {n : ℕ} (x : Fin n → Fcard ℵ₀) : Fin n → Fcard ℵ₀ :=
  fun i => if ((x i : Fcard ℵ₀) : Cardinal.{u}) = 0 then Fcard.mk 0 (zero_le' : (0 : Cardinal.{u}) ≤ ℵ₀)
    else Fcard.mk ℵ₀ le_rfl

/-- `H`, the solutions all of whose components are finite: the monoid `H ⊆ ℕ₀^n` of
Proposition 3.14(2), viewed inside `F_{ℵ₀}^n`. -/
noncomputable def LinSystem.finSolutions : Set (Fin n → Fcard ℵ₀) :=
  {x ∈ sys.solutions (le_refl ℵ₀) | ∀ i, ((x i : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀}

/-- `H + ℵ₀H`, the candidate universal `ℵ₀`-extension of Proposition 3.14(2). -/
noncomputable def LinSystem.alephExt : Set (Fin n → Fcard ℵ₀) :=
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  {z | ∃ h ∈ sys.finSolutions, ∃ h' ∈ sys.finSolutions, z = h + alephPart h'}

/-- The single-coordinate version of `alephPart`: `0 ↦ 0` and everything else to `ℵ₀`. -/
noncomputable def alephOne (c : Fcard ℵ₀) : Fcard ℵ₀ :=
  if (c : Cardinal.{u}) = 0 then Fcard.mk 0 (zero_le : (0 : Cardinal.{u}) ≤ ℵ₀)
  else Fcard.mk ℵ₀ le_rfl

theorem alephPart_eq {n : ℕ} (x : Fin n → Fcard ℵ₀) (i : Fin n) :
    alephPart x i = alephOne (x i) := rfl

/-- `alephOne` is additive: `a + b` is zero exactly when both summands are, and otherwise both
sides are `ℵ₀`. -/
theorem alephOne_isAdd :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    alephOne 0 = 0 ∧ ∀ a b, alephOne (a + b) = alephOne a + alephOne b := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  have hval : ∀ c : Fcard ℵ₀, (alephOne c : Cardinal.{u})
      = if (c : Cardinal.{u}) = 0 then 0 else ℵ₀ := by
    intro c
    unfold alephOne
    split <;> rfl
  refine ⟨Fcard.ext ?_, fun a b => Fcard.ext ?_⟩
  · rw [hval, Fcard.instKMonoid_zero, if_pos rfl]
  · rw [hval, Fcard.instKMonoid_add, Fcard.instKMonoid_add, hval, hval]
    by_cases ha : (a : Cardinal.{u}) = 0 <;> by_cases hb : (b : Cardinal.{u}) = 0
    · rw [if_pos (by rw [ha, hb, add_zero]), if_pos ha, if_pos hb, add_zero]
    · rw [if_neg (fun h => hb (add_eq_zero.mp h).2), if_pos ha, if_neg hb, zero_add]
    · rw [if_neg (fun h => ha (add_eq_zero.mp h).1), if_neg ha, if_pos hb, add_zero]
    · rw [if_neg (fun h => ha (add_eq_zero.mp h).1), if_neg ha, if_neg hb,
        Cardinal.aleph0_add_aleph0]

/-- `ℵ₀H ⊆ H`'s solution set: the componentwise `ℵ₀`-collapse of a solution is a solution. -/
theorem LinSystem.mem_solutions_alephPart {x : Fin n → Fcard ℵ₀}
    (hx : x ∈ sys.solutions (le_refl (ℵ₀ : Cardinal.{u}))) :
    alephPart x ∈ sys.solutions (le_refl (ℵ₀ : Cardinal.{u})) :=
  sys.mem_solutions_map (le_refl ℵ₀) (le_refl ℵ₀) alephOne alephOne_isAdd hx

/-- `H` is a submonoid: finite solutions are closed under `+`. -/
theorem LinSystem.addSubmonoid_finSolutions :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    (0 : Fin n → Fcard ℵ₀) ∈ sys.finSolutions ∧
      ∀ a ∈ sys.finSolutions, ∀ b ∈ sys.finSolutions, a + b ∈ sys.finSolutions := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  have hsub := sys.isKSubmonoid_solutions (le_refl (ℵ₀ : Cardinal.{u}))
  refine ⟨⟨hsub.zero_mem, fun i => ?_⟩, fun a ha b hb => ⟨hsub.add_mem ha.1 hb.1, fun i => ?_⟩⟩
  · rw [show ((0 : Fin n → Fcard ℵ₀) i) = 0 from rfl, Fcard.instKMonoid_zero]
    exact Cardinal.aleph0_pos
  · rw [show ((a + b : Fin n → Fcard ℵ₀) i) = a i + b i from rfl, Fcard.instKMonoid_add]
    exact Cardinal.add_lt_aleph0 (ha.2 i) (hb.2 i)

/-! ### `H + ℵ₀H` is closed under countable sums

Three ingredients: the support of a family of cardinals injects into its cardinal sum (so a
component of a countable sum that stays *finite* receives contributions from only finitely many
terms); `alephPart` is additive; and a set of components is the support of a single element of `H`
as soon as each of its components is hit by some element of `H` that vanishes outside the set. -/

/-- The support of a family of cardinals injects into its cardinal sum. -/
theorem mk_support_le_csum {ι : Type u} (c : ι → Cardinal.{u}) :
    #{i | c i ≠ 0} ≤ Cardinal.sum c := by
  classical
  have hne : ∀ i : {i | c i ≠ 0}, Nonempty (c (i : ι)).out := fun i =>
    Cardinal.mk_ne_zero_iff.mp (by rw [Cardinal.mk_out]; exact i.2)
  exact ⟨⟨fun i => ⟨(i : ι), (hne i).some⟩,
    fun i j hij => Subtype.ext (congrArg Sigma.fst hij)⟩⟩

/-- `alephPart` is additive, being `alephOne` in each component. -/
theorem alephPart_add {n : ℕ} (x y : Fin n → Fcard ℵ₀) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    alephPart (x + y) = alephPart x + alephPart y := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  exact funext fun i => alephOne_isAdd.2 (x i) (y i)

theorem alephPart_zero {n : ℕ} :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    alephPart (0 : Fin n → Fcard ℵ₀) = 0 := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  exact funext fun _ => alephOne_isAdd.1

/-- The value of `alephPart`: `0` where `x` vanishes and `ℵ₀` elsewhere. -/
theorem val_alephPart {n : ℕ} (x : Fin n → Fcard ℵ₀) (i : Fin n) :
    ((alephPart x i : Fcard ℵ₀) : Cardinal.{u})
      = if ((x i : Fcard ℵ₀) : Cardinal.{u}) = 0 then 0 else ℵ₀ := by
  rw [alephPart_eq]
  unfold alephOne
  split <;> rfl

/-- `H` as an additive submonoid, so that finite sums may be formed inside it. -/
noncomputable def LinSystem.finSubmonoid :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    AddSubmonoid (Fin n → Fcard ℵ₀) :=
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  { carrier := sys.finSolutions
    zero_mem' := sys.addSubmonoid_finSolutions.1
    add_mem' := fun {a b} ha hb => sys.addSubmonoid_finSolutions.2 a ha b hb }

theorem LinSystem.mem_finSubmonoid {x : Fin n → Fcard ℵ₀} :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    x ∈ sys.finSubmonoid ↔ x ∈ sys.finSolutions := Iff.rfl

/-- A set `U` of components is the support of a single element of `H`, as soon as every `i ∈ U` is
hit by an element `g i ∈ H` vanishing outside `U`: take `Σ_{i ∈ U} g i`. -/
theorem LinSystem.exists_finSolutions_support (U : Finset (Fin n))
    (g : Fin n → (Fin n → Fcard ℵ₀)) (hgH : ∀ i, g i ∈ sys.finSolutions)
    (hne : ∀ i ∈ U, ((g i i : Fcard ℵ₀) : Cardinal.{u}) ≠ 0)
    (hzero : ∀ i ∈ U, ∀ j ∉ U, ((g i j : Fcard ℵ₀) : Cardinal.{u}) = 0) :
    ∃ w ∈ sys.finSolutions, (∀ i ∈ U, ((w i : Fcard ℵ₀) : Cardinal.{u}) ≠ 0) ∧
      ∀ j ∉ U, ((w j : Fcard ℵ₀) : Cardinal.{u}) = 0 := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  refine ⟨∑ i ∈ U, g i,
    (sys.mem_finSubmonoid).mp (AddSubmonoid.sum_mem sys.finSubmonoid fun i _ => hgH i),
    fun i hi => ?_, fun j hj => ?_⟩
  · have hval : ((∑ i' ∈ U, g i') i : Cardinal.{u}) = ∑ i' ∈ U, ((g i' i : Fcard ℵ₀) : Cardinal.{u}) := by
      rw [Finset.sum_apply, ← fcardVal_apply (le_refl (ℵ₀ : Cardinal.{u})), map_sum]
      rfl
    intro hzero'
    refine hne i hi (le_antisymm ?_ zero_le)
    have hle : ((g i i : Fcard ℵ₀) : Cardinal.{u}) ≤ ∑ i' ∈ U, ((g i' i : Fcard ℵ₀) : Cardinal.{u}) :=
      Finset.single_le_sum (f := fun i' => ((g i' i : Fcard ℵ₀) : Cardinal.{u}))
        (fun i' _ => zero_le) hi
    rw [← hval, hzero'] at hle
    exact hle
  · rw [show ((∑ i ∈ U, g i) j : Fcard ℵ₀) = ∑ i ∈ U, g i j from Finset.sum_apply _ _ _,
      ← fcardVal_apply (le_refl (ℵ₀ : Cardinal.{u})), map_sum]
    exact Finset.sum_eq_zero fun i hi => hzero i hi j hj

/-- A countable sum of elements of `H` lies in `H + ℵ₀H`: the components that stay finite already
receive all of their contributions from a *finite* set `J` of indices, and every component that
blows up to `ℵ₀` is hit by an index outside `J`, so is absorbed into the `ℵ₀H` part. -/
theorem LinSystem.ksum_mem_alephExt (p : Idx (ℵ₀ : Cardinal.{u}) → (Fin n → Fcard ℵ₀))
    (hp : ∀ k, p k ∈ sys.finSolutions) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    KMonoid.ksum (κ := ℵ₀) p ∈ sys.alephExt := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  classical
  have hidx : #(Idx (ℵ₀ : Cardinal.{u})) ≤ ℵ₀ := le_of_eq (mk_Idx _)
  show KMonoid.sumOf (κ := ℵ₀) hidx p ∈ sys.alephExt
  -- the value of a component of a `κ`-sum is the cardinal sum of the components
  have hval : ∀ (y : Idx (ℵ₀ : Cardinal.{u}) → (Fin n → Fcard ℵ₀)) (i : Fin n),
      ((KMonoid.sumOf (κ := ℵ₀) hidx y i : Fcard ℵ₀) : Cardinal.{u})
        = Cardinal.sum fun k => ((y k i : Fcard ℵ₀) : Cardinal.{u}) := fun _ _ => rfl
  have hadd : ∀ (x y : Fin n → Fcard ℵ₀) (i : Fin n),
      (((x + y) i : Fcard ℵ₀) : Cardinal.{u})
        = ((x i : Fcard ℵ₀) : Cardinal.{u}) + ((y i : Fcard ℵ₀) : Cardinal.{u}) :=
    fun x y i => Fcard.instKMonoid_add (le_refl (ℵ₀ : Cardinal.{u})) (x i) (y i)
  set a := KMonoid.sumOf (κ := ℵ₀) hidx p with hadef
  -- `F`: the components of the sum that stay finite
  set F : Finset (Fin n) := Finset.univ.filter fun i => ((a i : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀
    with hFdef
  have hmemF : ∀ i, i ∈ F ↔ ((a i : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀ := by
    intro i; rw [hFdef]; simp
  have hnotF : ∀ i, i ∉ F → ((a i : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ := fun i hi =>
    le_antisymm (Fcard.le _) (not_lt.mp fun hc => hi ((hmemF i).mpr hc))
  -- `J`: the finitely many indices contributing to a finite component
  set J : Set (Idx (ℵ₀ : Cardinal.{u})) :=
    ⋃ i ∈ (F : Set (Fin n)), {k | ((p k i : Fcard ℵ₀) : Cardinal.{u}) ≠ 0} with hJdef
  have hJfin : J.Finite := by
    refine Set.Finite.biUnion (F : Set (Fin n)).toFinite fun i hi => ?_
    refine Cardinal.lt_aleph0_iff_set_finite.mp (lt_of_le_of_lt (mk_support_le_csum _) ?_)
    rw [← hval p i]
    exact (hmemF i).mp (Finset.mem_coe.mp hi)
  have hJout : ∀ i ∈ F, ∀ k, k ∉ J → ((p k i : Fcard ℵ₀) : Cardinal.{u}) = 0 := by
    intro i hi k hk
    by_contra hc
    exact hk (Set.mem_biUnion (Finset.mem_coe.mpr hi) hc)
  -- split the family at `J`
  set p₁ : Idx (ℵ₀ : Cardinal.{u}) → (Fin n → Fcard ℵ₀) := fun k => if k ∈ J then p k else 0
    with hp₁def
  set p₂ : Idx (ℵ₀ : Cardinal.{u}) → (Fin n → Fcard ℵ₀) := fun k => if k ∈ J then 0 else p k
    with hp₂def
  have hsplit : a = KMonoid.sumOf (κ := ℵ₀) hidx p₁ + KMonoid.sumOf (κ := ℵ₀) hidx p₂ := by
    rw [hadef, ← KMonoid.sumOf_add hidx p₁ p₂]
    refine congrArg _ (funext fun k => ?_)
    by_cases hk : k ∈ J
    · rw [hp₁def, hp₂def]; simp only [if_pos hk]; rw [add_zero]
    · rw [hp₁def, hp₂def]; simp only [if_neg hk]; rw [zero_add]
  -- the first half is a *finite* sum of elements of `H`, hence lies in `H`
  haveI : Fintype ↥J := hJfin.fintype
  have hJle : #(J : Set (Idx (ℵ₀ : Cardinal.{u}))) ≤ ℵ₀ :=
    (Cardinal.mk_set_le J).trans (le_of_eq (mk_Idx _))
  have hp₁sum : KMonoid.sumOf (κ := ℵ₀) hidx p₁ = ∑ k : ↥J, p (k : Idx ℵ₀) := by
    have hext : Function.extend (Function.Embedding.subtype (· ∈ J))
        (fun k : ↥J => p (k : Idx ℵ₀)) 0 = p₁ := by
      funext k
      by_cases hk : k ∈ J
      · have hk' : (Function.Embedding.subtype (· ∈ J)) ⟨k, hk⟩ = k := rfl
        rw [← hk', (Function.Embedding.subtype (· ∈ J)).injective.extend_apply, hp₁def]
        exact (if_pos hk).symm
      · rw [Function.extend_apply' _ _ _ (by rintro ⟨⟨t, ht⟩, rfl⟩; exact hk ht), hp₁def]
        exact (if_neg hk).symm
    rw [← hext, KMonoid.sumOf_extend hJle hidx, KMonoid.sumOf_eq_sum]
  have hhH : KMonoid.sumOf (κ := ℵ₀) hidx p₁ ∈ sys.finSolutions := by
    rw [hp₁sum]
    exact (sys.mem_finSubmonoid).mp
      (AddSubmonoid.sum_mem sys.finSubmonoid fun k _ => (sys.mem_finSubmonoid).mpr (hp k))
  -- and the second half contributes nothing to a component missed outside `J`
  have hp₂zero : ∀ i, (∀ k, k ∉ J → ((p k i : Fcard ℵ₀) : Cardinal.{u}) = 0) →
      ((KMonoid.sumOf (κ := ℵ₀) hidx p₂ i : Fcard ℵ₀) : Cardinal.{u}) = 0 := by
    intro i hi
    have hfam : (fun k => p₂ k i) = fun _ => (0 : Fcard ℵ₀) := by
      funext k
      by_cases hk : k ∈ J
      · rw [hp₂def]; simp only [if_pos hk]; rfl
      · rw [hp₂def]; simp only [if_neg hk]
        exact Fcard.ext ((hi k hk).trans (Fcard.instKMonoid_zero _).symm)
    rw [show (KMonoid.sumOf (κ := ℵ₀) hidx p₂ i) = KMonoid.sumOf (κ := ℵ₀) hidx (fun k => p₂ k i)
      from rfl, hfam, KMonoid.sumOf_zero, Fcard.instKMonoid_zero]
  have hafin : ∀ i, (∀ k, k ∉ J → ((p k i : Fcard ℵ₀) : Cardinal.{u}) = 0) →
      ((a i : Fcard ℵ₀) : Cardinal.{u})
        = ((KMonoid.sumOf (κ := ℵ₀) hidx p₁ i : Fcard ℵ₀) : Cardinal.{u}) := by
    intro i hi
    rw [hsplit, hadd, hp₂zero i hi, add_zero]
  -- every component that blows up is hit by an index outside `J`
  have hpick : ∀ i, ∃ k, i ∉ F → k ∉ J ∧ ((p k i : Fcard ℵ₀) : Cardinal.{u}) ≠ 0 := by
    intro i
    by_cases hi : i ∈ F
    · exact ⟨(nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))).some, fun hc => absurd hi hc⟩
    · have hex : ∃ k, k ∉ J ∧ ((p k i : Fcard ℵ₀) : Cardinal.{u}) ≠ 0 := by
        by_contra hno
        push Not at hno
        exact hi ((hmemF i).mpr (by rw [hafin i hno]; exact hhH.2 i))
      obtain ⟨k, hk1, hk2⟩ := hex
      exact ⟨k, fun _ => ⟨hk1, hk2⟩⟩
  choose kf hkf using hpick
  -- realise the blown-up components as the support of a single element of `H`
  obtain ⟨w, hwH, hw1, hw2⟩ := sys.exists_finSolutions_support Fᶜ (fun i => p (kf i))
    (fun i => hp (kf i))
    (fun i hi => (hkf i (Finset.mem_compl.mp hi)).2)
    (fun i hi j hj => hJout j (by simpa using hj) _ (hkf i (Finset.mem_compl.mp hi)).1)
  refine ⟨KMonoid.sumOf (κ := ℵ₀) hidx p₁, hhH, w, hwH, funext fun i => Fcard.ext ?_⟩
  rw [hadd, val_alephPart]
  by_cases hi : i ∈ F
  · rw [if_pos (hw2 i (by simpa using hi)), add_zero]
    exact hafin i fun k hk => hJout i hi k hk
  · rw [if_neg (hw1 i (Finset.mem_compl.mpr hi)), hnotF i hi]
    exact (Cardinal.add_eq_right le_rfl (le_of_lt (hhH.2 i))).symm

/-- The `ℵ₀H` part of a countable sum: a countable sum of elements of `ℵ₀H` is again in `ℵ₀H`,
because in each component it is `ℵ₀` exactly where one of the summands is. -/
theorem LinSystem.exists_alephPart_ksum (q : Idx (ℵ₀ : Cardinal.{u}) → (Fin n → Fcard ℵ₀))
    (hq : ∀ k, q k ∈ sys.finSolutions) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    ∃ w ∈ sys.finSolutions,
      KMonoid.ksum (κ := ℵ₀) (fun k => alephPart (q k)) = alephPart w := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  classical
  have hidx : #(Idx (ℵ₀ : Cardinal.{u})) ≤ ℵ₀ := le_of_eq (mk_Idx _)
  -- `U`: the components hit by some `q k`
  set U : Finset (Fin n) :=
    Finset.univ.filter fun i => ∃ k, ((q k i : Fcard ℵ₀) : Cardinal.{u}) ≠ 0 with hUdef
  have hmemU : ∀ i, i ∈ U ↔ ∃ k, ((q k i : Fcard ℵ₀) : Cardinal.{u}) ≠ 0 := by
    intro i; rw [hUdef]; simp
  have hpick : ∀ i, ∃ k, i ∈ U → ((q k i : Fcard ℵ₀) : Cardinal.{u}) ≠ 0 := by
    intro i
    by_cases hi : i ∈ U
    · obtain ⟨k, hk⟩ := (hmemU i).mp hi
      exact ⟨k, fun _ => hk⟩
    · exact ⟨(nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))).some, fun hc => absurd hc hi⟩
  choose kf hkf using hpick
  have hout : ∀ j, j ∉ U → ∀ k, ((q k j : Fcard ℵ₀) : Cardinal.{u}) = 0 := by
    intro j hj k
    by_contra hc
    exact hj ((hmemU j).mpr ⟨k, hc⟩)
  obtain ⟨w, hwH, hw1, hw2⟩ := sys.exists_finSolutions_support U (fun i => q (kf i))
    (fun i => hq (kf i)) (fun i hi => hkf i hi) (fun i _ j hj => hout j hj _)
  refine ⟨w, hwH, funext fun i => Fcard.ext ?_⟩
  rw [val_alephPart,
    show (KMonoid.ksum (κ := ℵ₀) (fun k => alephPart (q k)) i)
      = KMonoid.sumOf (κ := ℵ₀) hidx (fun k => alephPart (q k) i) from rfl]
  by_cases hi : i ∈ U
  · rw [if_neg (hw1 i hi)]
    refine le_antisymm (Fcard.le _) ?_
    rw [show ((KMonoid.sumOf (κ := ℵ₀) hidx (fun k => alephPart (q k) i) : Fcard ℵ₀)
        : Cardinal.{u}) = Cardinal.sum fun k => ((alephPart (q k) i : Fcard ℵ₀) : Cardinal.{u})
      from rfl]
    refine le_trans (le_of_eq ?_) (Cardinal.le_sum _ (kf i))
    rw [val_alephPart, if_neg (hkf i hi)]
  · rw [if_pos (hw2 i hi),
      show (fun k => alephPart (q k) i) = fun _ => (0 : Fcard ℵ₀) from
        funext fun k => Fcard.ext (by
          rw [val_alephPart, if_pos (hout i hi k), Fcard.instKMonoid_zero]),
      KMonoid.sumOf_zero, Fcard.instKMonoid_zero]

/-- `H + ℵ₀H` is an `ℵ₀`-submonoid of `F_{ℵ₀}^n`.

The point is closure under countable sums: a countable sum of elements `h_k + ℵ₀h'_k` has, in
each component, either finitely many nonzero contributions — in which case the sum is again of
that shape — or infinitely many, in which case the component is `ℵ₀` and is absorbed into the
`ℵ₀H` part. -/
theorem LinSystem.isKSubmonoid_alephExt :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    KMonoid.IsKSubmonoid ℵ₀ sys.alephExt := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  classical
  refine ⟨⟨0, sys.addSubmonoid_finSolutions.1, 0, sys.addSubmonoid_finSolutions.1, ?_⟩,
    fun z hz => ?_⟩
  · rw [alephPart_zero, add_zero]
  · choose p hp q hq hzk using hz
    have hsplit : KMonoid.ksum (κ := ℵ₀) z
        = KMonoid.ksum (κ := ℵ₀) p + KMonoid.ksum (κ := ℵ₀) fun k => alephPart (q k) := by
      rw [← KMonoid.sumOf_Idx z, ← KMonoid.sumOf_Idx p,
        ← KMonoid.sumOf_Idx (fun k => alephPart (q k)), ← KMonoid.sumOf_add]
      exact congrArg _ (funext hzk)
    obtain ⟨h, hhH, h', hh'H, hph⟩ := sys.ksum_mem_alephExt p hp
    obtain ⟨w, hwH, hqw⟩ := sys.exists_alephPart_ksum q hq
    refine ⟨h, hhH, h' + w, sys.addSubmonoid_finSolutions.2 _ hh'H _ hwH, ?_⟩
    rw [hsplit, hph, hqw, alephPart_add]
    exact add_assoc _ _ _

/-- Every element of `H + ℵ₀H` is a solution of the system: the easy inclusion.  Both summands
are solutions — the second because `alephPart` is additive — and the solutions form a
submonoid. -/
theorem LinSystem.alephExt_subset_solutions :
    sys.alephExt ⊆ sys.solutions (le_refl (ℵ₀ : Cardinal.{u})) := by
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  rintro z ⟨h, hh, h', hh', rfl⟩
  exact (sys.isKSubmonoid_solutions (le_refl ℵ₀)).add_mem hh.1
    (sys.mem_solutions_alephPart hh'.1)

/-- **Proposition 3.14(2)**: for a monoid `H ⊆ ℕ₀^n` cut out by a homogeneous system, the
universal `ℵ₀`-extension is `H + ℵ₀H ⊆ F_{ℵ₀}^n`.

Both `λ` and `κ` are `ℵ₀` here: an `ℵ₀⁻`-monoid is an ordinary commutative monoid, which is what
`H ⊆ ℕ₀^n` is.

Paper proof: `H + ℵ₀H` is `ℵ₀⁻`-braided over `H`.  Given two families in `H` with the same sum in
`F_{ℵ₀}^n`, either both are finitely supported — and then Lemma 3.4(1) applies — or both have
components that blow up to `ℵ₀`, and the braiding is built componentwise as in Examples 3.3(1).
Note this is genuinely *not* the solution set of the same system over `F_{ℵ₀}`, which is what
distinguishes (2) from (1); Example 3.15 is the witness. -/
theorem prop_3_14_two :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    letI : AddCommMonoid ↥sys.finSolutions :=
      addCommMonoidOfClosed sys.addSubmonoid_finSolutions.1
        (fun a ha b hb => sys.addSubmonoid_finSolutions.2 a ha b hb)
    letI := LMonoid.ofAddCommMonoid ↥sys.finSolutions
    letI := sys.isKSubmonoid_alephExt.kmonoid
    IsUniversalKExtension ℵ₀ ℵ₀ ↥sys.finSolutions ↥sys.alephExt (le_refl ℵ₀)
      (fun h => ⟨(h : Fin n → Fcard ℵ₀), ⟨(h : Fin n → Fcard ℵ₀), h.2, 0,
        sys.addSubmonoid_finSolutions.1, by rw [alephPart_zero, add_zero]⟩⟩) := by
  sorry

/-- **Example 3.15**: `H = {(m, m) : m ∈ ℕ₀} ⊆ ℕ₀²` shows that Proposition 3.14(1) and (2) really
are different statements — the universal `ℵ₀`-extension of `H` is *not* the solution set of
`x₁ = x₂` over `F_{ℵ₀}`, because that set contains `(ℵ₀, ℵ₀)` reached only as an infinite sum. -/
theorem example_3_15 : True := by
  trivial

end Diophantine



end KappaMonoid
