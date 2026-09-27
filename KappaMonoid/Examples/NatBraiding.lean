/-
**Examples 3.3(1)**: braiding in `ℕ₀`, and the packaging of `ℕ₀ ∪ {∞}` as the universal
`ℵ₀`-extension of `ℕ₀`.
-/
import KappaMonoid.Braiding.Saturated
import KappaMonoid.Core.OrderUnit
import KappaMonoid.Examples.ENNReal
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.BigOperators.Fin

universe u v w t

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
  let := LMonoid.ofAddCommMonoid ℕ
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
        (fun _i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi)) s.1 s.2.2).choose
      let u := (∑ i ∈ Finset.Ico s.1 bI', x i) - s.2.2
      let bJ' := (exists_ico_dominates hy y
        (fun _i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi)) s.2.1 u).choose
      (bI', bJ', (∑ i ∈ Finset.Ico s.2.1 bJ', y i) - u)

theorem natBraidState_succ (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) :
    natBraidState x y hx hy (k + 1) =
      let s := natBraidState x y hx hy k
      let bI' := (exists_ico_dominates hx x
        (fun _i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi)) s.1 s.2.2).choose
      let u := (∑ i ∈ Finset.Ico s.1 bI', x i) - s.2.2
      let bJ' := (exists_ico_dominates hy y
        (fun _i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi)) s.2.1 u).choose
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
  (exists_ico_dominates hx x (fun _i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi))
    (natBraidBI x y hx hy k) (natBraidV x y hx hy k)).choose_spec

/-- The defining property of `bJ (k+1)`: it dominates the deficit `u k` along `support y`. -/
theorem natBraidBJ_succ_spec (x y : ℕ → ℕ) (hx : (Function.support x).Infinite)
    (hy : (Function.support y).Infinite) (k : ℕ) :
    natBraidBJ x y hx hy k < natBraidBJ x y hx hy (k + 1) ∧
      natBraidU x y hx hy k ≤
        ∑ i ∈ Finset.Ico (natBraidBJ x y hx hy k) (natBraidBJ x y hx hy (k + 1)), y i :=
  (exists_ico_dominates hy y (fun _i hi => Nat.one_le_iff_ne_zero.mpr (Function.mem_support.mp hi))
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

Transport a bijection `φ : ℕ ≃ ι` — one exists because `ι` is infinite of cardinality `≤ ℵ₀` —
run the `ℕ`-arithmetic construction above on `x ∘ φ`, `y ∘ φ`, and hand the resulting block
boundaries, carries and deficits to `IsBraided.of_nat_blocks`, which assembles the `BraidingData`
over `ι`.  (A *bijection with* `ℕ` is what is needed, not `IsBraided.comp_equiv`, whose two index
types live in the same universe: here one side is the genuinely `Type 0`-valued `ℕ`.) -/
theorem isBraided_nat_of_infinite_support {ι : Type u} (hι : #ι ≤ ℵ₀) (x y : ι → ℕ)
    (hx : (Function.support x).Infinite) (hy : (Function.support y).Infinite) :
    letI := LMonoid.ofAddCommMonoid ℕ
    IsBraided ℵ₀ x y := by
  let := LMonoid.ofAddCommMonoid ℕ
  classical
  have hιInf : Infinite ι := by
    rcases finite_or_infinite ι with hfin | hinf
    · have := hfin
      exact absurd (Set.toFinite (Function.support x)) hx
    · exact hinf
  obtain ⟨φ⟩ := Cardinal.nonempty_equiv_nat_of_le_aleph0 hι hιInf
  have hsupp : ∀ z : ι → ℕ, (Function.support z).Infinite →
      (Function.support (z ∘ φ)).Infinite := by
    intro z hz hfin
    rw [Function.support_comp_eq_preimage] at hfin
    apply hz
    rw [← Set.image_preimage_eq (Function.support z) φ.surjective]
    exact hfin.image _
  have hx3 : (Function.support (x ∘ φ)).Infinite := hsupp x hx
  have hy3 : (Function.support (y ∘ φ)).Infinite := hsupp y hy
  exact IsBraided.of_nat_blocks φ (natBraidBI _ _ hx3 hy3) (natBraidBJ _ _ hx3 hy3)
    (strictMono_nat_of_lt_succ (natBraidBI_lt_succ _ _ hx3 hy3))
    (strictMono_nat_of_lt_succ (natBraidBJ_lt_succ _ _ hx3 hy3))
    (natBraidBI_zero _ _ hx3 hy3) (natBraidBJ_zero _ _ hx3 hy3)
    (natBraidU _ _ hx3 hy3) (natBraidV _ _ hx3 hy3) (natBraidV_zero _ _ hx3 hy3)
    (natBraidBI_sum_eq _ _ hx3 hy3) (natBraidBJ_sum_eq _ _ hx3 hy3)

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

/-- The inclusion `ℕ₀ → ℕ₀ ∪ {∞}` is an `ℵ₀⁻`-homomorphism: both sides of a finite sum are the
finite sum of the entries. -/
theorem isLHom_coe_withTop_nat :
    letI := LMonoid.ofAddCommMonoid ℕ
    letI := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
    LMonoid.IsLHom (Order.le_succ (ℵ₀ : Cardinal.{u})) (fun a : ℕ => ((a : ℕ) : WithTop ℕ)) := by
  let := LMonoid.ofAddCommMonoid ℕ
  let := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
  refine ⟨rfl, fun {ι} h x => ?_⟩
  have : Finite ι := Cardinal.lt_aleph0_iff_finite.mp h
  have : Fintype ι := Fintype.ofFinite ι
  rw [LMonoid.lsumOf_aleph0_eq_finsum h x, KMonoid.sumOf_eq_sum (h := CardLE.mk' h.le)]
  simp

/-- **Examples 3.3(1)**, the characterization: two families in `ℕ₀` indexed by `ℵ₀` are
`ℵ₀⁻`-braided *if and only if* they both have finite support and the same sum, or both have
infinite support.

The two implications going in are `isBraided_nat_of_finite_support` and
`isBraided_nat_of_infinite_support`.  Coming out: reducedness of `ℕ₀` makes the support of one
family small exactly when the other's is (`IsBraided.mk_support_lt`), and a braiding is carried by
the `ℵ₀⁻`-homomorphism `ℕ₀ → ℕ₀ ∪ {∞}` to two families with equal `ℵ₀`-sums, which for finite
support is the equality of the finite sums. -/
theorem isBraided_nat_iff (x y : Idx (ℵ₀ : Cardinal.{u}) → ℕ) :
    letI := LMonoid.ofAddCommMonoid ℕ
    IsBraided (ℵ₀ : Cardinal.{u}) x y ↔
      (((Function.support x).Finite ∧ (Function.support y).Finite ∧ ∑ᶠ i, x i = ∑ᶠ i, y i) ∨
        ((Function.support x).Infinite ∧ (Function.support y).Infinite)) := by
  classical
  let := LMonoid.ofAddCommMonoid ℕ
  let := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
  have hcon : IsConical ℕ := fun a b h => by omega
  have hidx : #(Idx (ℵ₀ : Cardinal.{u})) ≤ (ℵ₀ : Cardinal.{u}) := le_of_eq (mk_Idx _)
  constructor
  · intro h
    have hfin : (Function.support x).Finite ↔ (Function.support y).Finite := by
      constructor
      · intro hx
        exact Cardinal.lt_aleph0_iff_set_finite.mp
          (h.mk_support_lt hcon (Cardinal.lt_aleph0_iff_set_finite.mpr hx))
      · intro hy
        exact Cardinal.lt_aleph0_iff_set_finite.mp
          ((IsBraided.symm h).mk_support_lt hcon (Cardinal.lt_aleph0_iff_set_finite.mpr hy))
    by_cases hx : (Function.support x).Finite
    · refine Or.inl ⟨hx, hfin.mp hx, ?_⟩
      have hsum := sumOf_map_eq_of_isBraided (Order.le_succ (ℵ₀ : Cardinal.{u}))
        isLHom_coe_withTop_nat hidx h
      rw [KMonoid.sumOf_Idx, KMonoid.sumOf_Idx, TrivExt.instKMonoid_ksum hcon le_rfl,
        TrivExt.instKMonoid_ksum hcon le_rfl] at hsum
      show (∑ᶠ i, x i) = ∑ᶠ i, y i
      have hx2 : TrivExt.sigma ((fun a : ℕ => ((a : ℕ) : WithTop ℕ)) ∘ x) = ((∑ᶠ i, x i : ℕ) : WithTop ℕ) :=
        trivExt_sigma_coe_nat_of_finite hx
      have hy2 : TrivExt.sigma ((fun a : ℕ => ((a : ℕ) : WithTop ℕ)) ∘ y) = ((∑ᶠ i, y i : ℕ) : WithTop ℕ) :=
        trivExt_sigma_coe_nat_of_finite (hfin.mp hx)
      rw [hx2, hy2] at hsum
      exact_mod_cast hsum
    · exact Or.inr ⟨hx, fun hy => hx (hfin.mpr hy)⟩
  · rintro (⟨hx, hy, hsum⟩ | ⟨hx, hy⟩)
    · exact isBraided_nat_of_finite_support x y hx hy hsum
    · exact isBraided_nat_of_infinite_support hidx x y hx hy

/-- **Examples 3.3(1)**: the trivial `ℵ₀`-extension `ℕ₀ ∪ {∞}` is `ℵ₀⁻`-braided over `ℕ₀`, hence
(by Theorem 3.12(2)) *is* the universal `ℵ₀`-extension of `ℕ₀`.  This is the first entry of
Examples 3.13. -/
theorem isBraidedOver_withTop_nat :
    letI := LMonoid.ofAddCommMonoid ℕ
    letI := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
    IsBraidedOver (ℵ₀ : Cardinal.{u}) ℵ₀ ℕ (WithTop ℕ) (Order.le_succ ℵ₀) (fun a => (a : WithTop ℕ)) := by
  let := LMonoid.ofAddCommMonoid ℕ
  let := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
  classical
  have hksum : ∀ x : Idx (ℵ₀ : Cardinal.{u}) → WithTop ℕ,
      KMonoid.ksum (κ := ℵ₀) x = TrivExt.sigma x :=
    fun x => TrivExt.instKMonoid_ksum _ _ x
  refine ⟨⟨rfl, fun {ι} h x => ?_⟩, fun a b hab => ?_, fun h => ?_, fun x y hxy => ?_⟩
  · -- `↑` is an `ℵ₀⁻`-homomorphism: both sides are the finite sum of the `x i`
    have : Finite ι := Cardinal.lt_aleph0_iff_finite.mp h
    have : Fintype ι := Fintype.ofFinite ι
    rw [LMonoid.lsumOf_aleph0_eq_finsum h x, KMonoid.sumOf_eq_sum (h := CardLE.mk' h.le)]
    simp
  · exact_mod_cast hab
  · -- `ℕ₀` generates `ℕ₀ ∪ {∞}`: a finite element is a one-term sum, `∞` is the sum of `1`s
    rcases eq_or_ne h ⊤ with rfl | hne
    · refine ⟨fun _ => 1, ?_⟩
      have : Infinite (Idx (ℵ₀ : Cardinal.{u})) := infinite_Idx le_rfl
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

/-- **Examples 3.13**, first entry: `ℕ̂₀ = ℕ₀ ∪ {∞}`.  Combining `isBraidedOver_withTop_nat` with
Theorem 3.12(2), the universal `ℵ₀`-extension of `ℕ₀` is its trivial `ℵ₀`-extension. -/
theorem isUniversalKExtension_withTop_nat :
    letI := LMonoid.ofAddCommMonoid ℕ
    letI := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
    IsUniversalKExtension.{u, 0, 0, t} (ℵ₀ : Cardinal.{u}) ℵ₀ ℕ (WithTop ℕ) (Order.le_succ ℵ₀)
      (fun a => (a : WithTop ℕ)) := by
  let := LMonoid.ofAddCommMonoid ℕ
  let := TrivExt.instKMonoid (M := ℕ) (κ := (ℵ₀ : Cardinal.{u})) (fun a b h => by omega) le_rfl
  exact isBraidedOver_withTop_nat.isUniversalKExtension (Order.le_succ ℵ₀)

end KappaMonoid
