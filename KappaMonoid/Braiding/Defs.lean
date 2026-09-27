/-
**Definition 3.1(1)**: `BraidingData`, `IsBraided`, regrouping a partition along a partition
of the index set, and the basic properties of the braiding relation - **Lemma 3.6**.
-/
import KappaMonoid.Braiding.Prelim
import KappaMonoid.ForMathlib.NatBlocks

universe u v w

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid


/-! ## Definition 3.1(1): braided families -/

/-- The data witnessing that two `κ`-indexed families `x` and `y` over a `λ⁻`-monoid `X` are
`λ⁻`-*braided*: indexed partitions `I`, `J` of the index set into pieces of size `< λ`,
together with braiding families `u`, `v` such that `v` vanishes at limit elements and

  `Σ_{i ∈ I p} x i = v p + u p`,   `Σ_{j ∈ J p} y j = v (p+1) + u p`. -/
structure BraidingData (lam : Cardinal.{u}) {X : Type v} [LMonoid lam X] {ι : Type u}
    (x y : ι → X) where
  I : ι × ℕ → Set ι
  J : ι × ℕ → Set ι
  I_disjoint : ∀ p q, p ≠ q → Disjoint (I p) (I q)
  J_disjoint : ∀ p q, p ≠ q → Disjoint (J p) (J q)
  I_cover : (⋃ p, I p) = Set.univ
  J_cover : (⋃ p, J p) = Set.univ
  /-- The pieces have fewer than `λ` elements. -/
  [I_small : ∀ p, CardLT (I p) lam]
  [J_small : ∀ p, CardLT (J p) lam]
  u : ι × ℕ → X
  v : ι × ℕ → X
  /-- `v` vanishes at the limit elements of the well-order. -/
  v_limit : ∀ a : ι, v (a, 0) = 0
  hI : ∀ p, ∑[lam] i ∈ I p, x i = v p + u p
  hJ : ∀ p, ∑[lam] j ∈ J p, y j = v (bsucc p) + u p

attribute [instance] BraidingData.I_small BraidingData.J_small

/-- The bound `#(I p) < λ` on a piece, from the instance field. -/
@[lam_small_rule] theorem BraidingData.I_lt {X : Type v} [LMonoid lam X] {ι : Type u}
    {x y : ι → X} (d : BraidingData lam x y) (p : ι × ℕ) : #(d.I p) < lam := (d.I_small p).lt

/-- The bound `#(J p) < λ` on a piece, from the instance field. -/
@[lam_small_rule] theorem BraidingData.J_lt {X : Type v} [LMonoid lam X] {ι : Type u}
    {x y : ι → X} (d : BraidingData lam x y) (p : ι × ℕ) : #(d.J p) < lam := (d.J_small p).lt

/-- Definition 3.1(1): `x` and `y` are `λ⁻`-braided. -/
def IsBraided (lam : Cardinal.{u}) {X : Type v} [LMonoid lam X] {ι : Type u} (x y : ι → X) :
    Prop :=
  Nonempty (BraidingData lam x y)

/-- Building `BraidingData ℵ₀` from finite partitions and `finsum` equations. -/
def BraidingData.mk_finsum {X : Type v} [LMonoid ℵ₀ X] {ι : Type u} {x y : ι → X}
    (I J : ι × ℕ → Set ι)
    (hIfin : ∀ p, (I p).Finite) (hJfin : ∀ p, (J p).Finite)
    (hIdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q))
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hIcov : (⋃ p, I p) = Set.univ) (hJcov : (⋃ p, J p) = Set.univ)
    (u v : ι × ℕ → X) (hv : ∀ a : ι, v (a, 0) = 0)
    (hI : ∀ p, ∑ᶠ i ∈ I p, x i = v p + u p)
    (hJ : ∀ p, ∑ᶠ j ∈ J p, y j = v (bsucc p) + u p) :
    BraidingData ℵ₀ x y where
  I := I
  J := J
  I_disjoint := hIdisj
  J_disjoint := hJdisj
  I_cover := hIcov
  J_cover := hJcov
  I_small := fun p => ⟨lt_aleph0_iff_set_finite.mpr (hIfin p)⟩
  J_small := fun p => ⟨lt_aleph0_iff_set_finite.mpr (hJfin p)⟩
  u := u
  v := v
  v_limit := hv
  hI := fun p => (LMonoid.lsumOf_eq_finsum _ x).trans (hI p)
  hJ := fun p => (LMonoid.lsumOf_eq_finsum _ y).trans (hJ p)

/-! ## Regrouping a partition along a partition of the index set -/

section Regroup

variable {ι : Type u}

/-- Regroup the partition `P` of `ι` along the family `G` of sets of positions: the piece at `p`
is the union of the `P`-pieces at all positions in `G p`. -/
def regroup (P : ι × ℕ → Set ι) (G : ι × ℕ → Set (ι × ℕ)) (p : ι × ℕ) : Set ι :=
  ⋃ ν ∈ G p, P ν

theorem regroup_finite {P : ι × ℕ → Set ι} {G : ι × ℕ → Set (ι × ℕ)} {p : ι × ℕ}
    (hP : ∀ ν, (P ν).Finite) (hG : (G p).Finite) : (regroup P G p).Finite :=
  hG.biUnion fun ν _ => hP ν

theorem regroup_disjoint {P : ι × ℕ → Set ι} {G : ι × ℕ → Set (ι × ℕ)}
    (hP : ∀ ν ρ, ν ≠ ρ → Disjoint (P ν) (P ρ))
    (hG : ∀ p q, p ≠ q → Disjoint (G p) (G q)) {p q : ι × ℕ} (hpq : p ≠ q) :
    Disjoint (regroup P G p) (regroup P G q) := by
  rw [Set.disjoint_left]
  intro i hi hj
  simp only [regroup, Set.mem_iUnion, exists_prop] at hi hj
  obtain ⟨ν, hν, hiν⟩ := hi
  obtain ⟨ρ, hρ, hiρ⟩ := hj
  have hνρ : ν = ρ := by
    by_contra hne
    exact Set.disjoint_left.mp (hP ν ρ hne) hiν hiρ
  subst hνρ
  exact Set.disjoint_left.mp (hG p q hpq) hν hρ

theorem regroup_cover {P : ι × ℕ → Set ι} {G : ι × ℕ → Set (ι × ℕ)}
    (hP : (⋃ ν, P ν) = Set.univ) (hG : (⋃ p, G p) = Set.univ) :
    (⋃ p, regroup P G p) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro i
  obtain ⟨ν, hν⟩ := Set.mem_iUnion.mp (hP ▸ Set.mem_univ i)
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hG ▸ Set.mem_univ ν)
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_biUnion hp hν⟩

theorem regroup_finsum {X : Type v} [AddCommMonoid X] {P : ι × ℕ → Set ι}
    {G : ι × ℕ → Set (ι × ℕ)} (hP : ∀ ν ρ, ν ≠ ρ → Disjoint (P ν) (P ρ))
    (hPfin : ∀ ν, (P ν).Finite) {p : ι × ℕ} (hG : (G p).Finite) (f : ι → X) :
    ∑ᶠ i ∈ regroup P G p, f i = ∑ᶠ ν ∈ G p, ∑ᶠ i ∈ P ν, f i :=
  finsum_mem_biUnion (fun ν _ ρ _ hne => hP ν ρ hne) hG fun ν _ => hPfin ν

end Regroup


/-! ## Basic properties of the braiding relation -/

namespace IsBraided

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u}

/-- The partition of the index type into singletons parked at the limit slots: `{f p.1}` at
`(p.1, 0)` and nothing elsewhere, for a bijection `f`. -/
def slot0 (f : ι → ι) (p : ι × ℕ) : Set ι := if p.2 = 0 then {f p.1} else ∅

@[simp] theorem slot0_zero (f : ι → ι) (a : ι) : slot0 f (a, 0) = {f a} := if_pos rfl

@[simp] theorem slot0_succ (f : ι → ι) (a : ι) (n : ℕ) : slot0 f (a, n + 1) = ∅ :=
  if_neg (Nat.succ_ne_zero n)

theorem slot0_disjoint {f : ι → ι} (hf : Function.Injective f) :
    ∀ p q : ι × ℕ, p ≠ q → Disjoint (slot0 f p) (slot0 f q) := by
  rintro ⟨a, (_ | n)⟩ ⟨b, (_ | m)⟩ hpq
  · rw [slot0_zero, slot0_zero, Set.disjoint_singleton]
    exact fun h => hpq (by rw [hf h])
  · rw [slot0_succ]; exact disjoint_bot_right
  · rw [slot0_succ]; exact disjoint_bot_left
  · rw [slot0_succ]; exact disjoint_bot_left

theorem slot0_cover {f : ι → ι} (hf : Function.Surjective f) : (⋃ p, slot0 f p) = Set.univ := by
  refine Set.eq_univ_of_forall fun i => Set.mem_iUnion.mpr ?_
  obtain ⟨a, rfl⟩ := hf i
  exact ⟨(a, 0), by rw [slot0_zero]; rfl⟩

theorem slot0_small (hlam0 : ℵ₀ ≤ lam) (f : ι → ι) : ∀ p, #(slot0 f p) < lam := by
  rintro ⟨a, (_ | n)⟩
  · rw [slot0_zero, Cardinal.mk_singleton]; exact lt_of_lt_of_le one_lt_aleph0 hlam0
  · rw [slot0_succ, Cardinal.mk_eq_zero]; exact Cardinal.aleph0_pos.trans_le hlam0

theorem lsumOf_slot0 (hlam0 : ℵ₀ ≤ lam) (f : ι → ι) (x : ι → X) (p : ι × ℕ) :
    lsumOf (lam := lam) (slot0_small hlam0 f p) (fun i : slot0 f p => x i)
      = if p.2 = 0 then x (f p.1) else 0 := by
  obtain ⟨a, (_ | n)⟩ := p
  · let : Unique ↥(slot0 f (a, 0)) := Set.uniqueSingleton (f a)
    rw [lsumOf_unique (slot0_small hlam0 f (a, 0)) (fun i : slot0 f (a, 0) => x i), if_pos rfl]
    rfl
  · let : IsEmpty ↥(slot0 f (a, n + 1)) := inferInstanceAs (IsEmpty (↥(∅ : Set ι)))
    rw [lsumOf_isEmpty (slot0_small hlam0 f (a, n + 1)) (fun i => x i),
      if_neg (Nat.succ_ne_zero n)]

/-- The basic way of producing a braiding: if the two families admit indexed partitions of
the index set into pieces of size `< λ` whose partial sums *agree piece by piece*, then they
are `λ⁻`-braided — take `v ≡ 0` and let `u` be the common partial sums.

This is the easy half of Lemma 3.4(4), and it needs no hypothesis on `λ`. -/
def _root_.KappaMonoid.BraidingData.ofPartition {x y : ι → X} (I J : ι × ℕ → Set ι)
    (hIdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q))
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hIcov : (⋃ p, I p) = Set.univ) (hJcov : (⋃ p, J p) = Set.univ)
    (hIsmall : ∀ p, #(I p) < lam) (hJsmall : ∀ p, #(J p) < lam)
    (heq : ∀ p, ∑[lam] i ∈ I p, x i
        = ∑[lam] j ∈ J p, y j) :
    BraidingData lam x y where
  I := I
  J := J
  I_disjoint := hIdisj
  J_disjoint := hJdisj
  I_cover := hIcov
  J_cover := hJcov
  I_small := fun p => ⟨hIsmall p⟩
  J_small := fun p => ⟨hJsmall p⟩
  u := fun p => ∑[lam] i ∈ I p, x i
  v := fun _ => 0
  v_limit := fun _ => rfl
  hI := fun _ => (zero_add _).symm
  hJ := fun p => (heq p).symm.trans (zero_add _).symm

theorem of_partition {x y : ι → X} (I J : ι × ℕ → Set ι)
    (hIdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q))
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hIcov : (⋃ p, I p) = Set.univ) (hJcov : (⋃ p, J p) = Set.univ)
    (hIsmall : ∀ p, #(I p) < lam) (hJsmall : ∀ p, #(J p) < lam)
    (heq : ∀ p, ∑[lam] i ∈ I p, x i
        = ∑[lam] j ∈ J p, y j) :
    IsBraided lam x y :=
  ⟨BraidingData.ofPartition I J hIdisj hJdisj hIcov hJcov hIsmall hJsmall heq⟩

/-- **Braiding from two level functions.**

The partitions built by hand in the paper — Lemma 5.2(3) writes down three interleaved partitions
of `ℕ` — always park all the action on a single `ω`-chain `(a₀, k)_{k ∈ ℕ}` of the index type
`ι × ℕ` and cut `ι` into the fibers of a *level function* `c : ι → ℕ`.  Fibers are automatically
disjoint and cover, so the only obligations left are finiteness of each fiber and the two block
equations, which is what this builder takes.

`of_partition` is the special case `v ≡ 0` (and a different pair of partitions). -/
theorem of_levels {X : Type v} [LMonoid ℵ₀ X] {ι : Type u} {x y : ι → X} (a₀ : ι)
    (cI cJ : ι → ℕ) (hIfin : ∀ k, {i | cI i = k}.Finite) (hJfin : ∀ k, {i | cJ i = k}.Finite)
    (u v : ℕ → X) (hv0 : v 0 = 0)
    (hIeq : ∀ k, ∑ᶠ i ∈ {i | cI i = k}, x i = v k + u k)
    (hJeq : ∀ k, ∑ᶠ i ∈ {i | cJ i = k}, y i = v (k + 1) + u k) :
    IsBraided ℵ₀ x y := by
  classical
  have hdisj : ∀ (c : ι → ℕ) (p q : ι × ℕ), p ≠ q →
      Disjoint (if p.1 = a₀ then {i | c i = p.2} else ∅)
        (if q.1 = a₀ then {i | c i = q.2} else ∅) := by
    intro c p q hpq
    by_cases hp : p.1 = a₀
    · by_cases hq : q.1 = a₀
      · rw [if_pos hp, if_pos hq]
        refine Set.disjoint_left.mpr fun i hi hi' => hpq ?_
        exact Prod.ext (hp.trans hq.symm) (hi.symm.trans hi')
      · rw [if_neg hq]; exact disjoint_bot_right
    · rw [if_neg hp]; exact disjoint_bot_left
  have hcov : ∀ c : ι → ℕ,
      (⋃ p : ι × ℕ, if p.1 = a₀ then {i | c i = p.2} else ∅) = Set.univ := by
    intro c
    refine Set.eq_univ_of_forall fun i => Set.mem_iUnion.mpr ⟨(a₀, c i), ?_⟩
    rw [if_pos rfl]
    rfl
  have hfin : ∀ (c : ι → ℕ), (∀ k, {i | c i = k}.Finite) →
      ∀ p : ι × ℕ, (if p.1 = a₀ then {i | c i = p.2} else ∅).Finite := by
    intro c hc p
    by_cases hp : p.1 = a₀
    · rw [if_pos hp]; exact hc p.2
    · rw [if_neg hp]; exact Set.finite_empty
  refine ⟨BraidingData.mk_finsum
    (fun p => if p.1 = a₀ then {i | cI i = p.2} else ∅)
    (fun p => if p.1 = a₀ then {i | cJ i = p.2} else ∅)
    (hfin cI hIfin) (hfin cJ hJfin) (hdisj cI) (hdisj cJ) (hcov cI) (hcov cJ)
    (fun p => if p.1 = a₀ then u p.2 else 0) (fun p => if p.1 = a₀ then v p.2 else 0)
    (fun a => ?_) (fun p => ?_) (fun p => ?_)⟩
  · by_cases ha : a = a₀
    · rw [if_pos ha]; exact hv0
    · rw [if_neg ha]
  · by_cases hp : p.1 = a₀
    · rw [if_pos hp, if_pos hp, if_pos hp]; exact hIeq p.2
    · rw [if_neg hp, if_neg hp, if_neg hp, finsum_mem_empty, add_zero]
  · by_cases hp : p.1 = a₀
    · rw [if_pos hp, if_pos hp, show (bsucc p).1 = a₀ from hp, if_pos rfl]
      exact hJeq p.2
    · have hbp : ¬ ((bsucc p).1 = a₀) := hp
      rw [if_neg hp, if_neg hp, if_neg hbp, finsum_mem_empty, add_zero]

/-- **Braiding from a pair of `ℕ`-block decompositions.**

Both families of Examples 3.3 are built the same way: a bijection `φ : ℕ ≃ ι` carries the problem
to `ℕ`, where two strictly increasing sequences of block boundaries `bI`, `bJ` starting at `0` cut
`ℕ` into consecutive intervals, and the partial sums over those intervals telescope through the
carries `u` and the deficits `v`.  This packages that argument once: the level functions of
`of_levels` are the block indices `Nat.blockIdx`, whose fibres are exactly the intervals
(`Nat.blockIdx_fibre_of_strictMono`), transported along `φ`.

Note that `φ` is a *bijection with `ℕ`*, not a reindexing in the sense of `comp_equiv`: the two
index types live in different universes, which is why the data is built over `ι` directly. -/
theorem of_nat_blocks {X : Type v} [LMonoid ℵ₀ X] {ι : Type u} (φ : ℕ ≃ ι) {x y : ι → X}
    (bI bJ : ℕ → ℕ) (hbI : StrictMono bI) (hbJ : StrictMono bJ) (hbI0 : bI 0 = 0) (hbJ0 : bJ 0 = 0)
    (u v : ℕ → X) (hv0 : v 0 = 0)
    (hIeq : ∀ k, ∑ i ∈ Finset.Ico (bI k) (bI (k + 1)), x (φ i) = v k + u k)
    (hJeq : ∀ k, ∑ i ∈ Finset.Ico (bJ k) (bJ (k + 1)), y (φ i) = v (k + 1) + u k) :
    IsBraided ℵ₀ x y := by
  classical
  have hfib : ∀ (b : ℕ → ℕ), StrictMono b → b 0 = 0 → ∀ k : ℕ,
      {i : ι | Nat.blockIdx b (φ.symm i) = k} = φ '' Set.Ico (b k) (b (k + 1)) := by
    intro b hb hb0 k
    rw [← Nat.blockIdx_fibre_of_strictMono hb hb0]
    ext i
    constructor
    · exact fun hi => ⟨φ.symm i, hi, φ.apply_symm_apply i⟩
    · rintro ⟨j, hj, rfl⟩
      show Nat.blockIdx b (φ.symm (φ j)) = k
      rwa [φ.symm_apply_apply]
  have hsum : ∀ (b : ℕ → ℕ), StrictMono b → b 0 = 0 → ∀ (z : ι → X) (k : ℕ),
      (∑ᶠ i ∈ {i : ι | Nat.blockIdx b (φ.symm i) = k}, z i)
        = ∑ i ∈ Finset.Ico (b k) (b (k + 1)), z (φ i) := by
    intro b hb hb0 z k
    rw [hfib b hb hb0 k, finsum_mem_image φ.injective.injOn,
      show (Set.Ico (b k) (b (k + 1)) : Set ℕ) = (↑(Finset.Ico (b k) (b (k + 1))) : Set ℕ) from
        (Finset.coe_Ico _ _).symm,
      finsum_mem_coe_finset]
  refine of_levels (φ 0) (fun i => Nat.blockIdx bI (φ.symm i))
    (fun i => Nat.blockIdx bJ (φ.symm i)) (fun k => ?_) (fun k => ?_) u v hv0 (fun k => ?_)
    (fun k => ?_)
  · rw [hfib bI hbI hbI0 k]; exact (Set.finite_Ico _ _).image _
  · rw [hfib bJ hbJ hbJ0 k]; exact (Set.finite_Ico _ _).image _
  · rw [hsum bI hbI hbI0 x k]; exact hIeq k
  · rw [hsum bJ hbJ hbJ0 y k]; exact hJeq k

/-- **Braiding transports along a bijection of index types.**

`IsBraided` is stated for two families over one index type, but §5 needs to compare families
indexed by `FormIdx` with families indexed by `Idx ℵ₀`; both are countable, and this moves a
braiding across such an identification.  The partitions are pulled back through `E`, which is
harmless because `E` is a bijection: preimages of disjoint sets are disjoint, they still cover,
and each has the same cardinality as the piece it comes from. -/
theorem comp_equiv {ι' : Type u} (E : ι ≃ ι') {x y : ι' → X} (h : IsBraided lam x y) :
    IsBraided lam (fun i => x (E i)) (fun i => y (E i)) := by
  obtain ⟨d⟩ := h
  have hpre : ∀ T : Set ι', #(E ⁻¹' T) = #T := fun T =>
    Cardinal.mk_congr ⟨fun i => ⟨E i, i.2⟩, fun j => ⟨E.symm j, by simp⟩,
      fun i => by simp, fun j => by simp⟩
  have hdisj : ∀ (P : ι' × ℕ → Set ι'), (∀ p q, p ≠ q → Disjoint (P p) (P q)) →
      ∀ p q : ι × ℕ, p ≠ q →
        Disjoint (E ⁻¹' P (E p.1, p.2)) (E ⁻¹' P (E q.1, q.2)) := by
    intro P hP p q hpq
    have hpq' : ((E p.1, p.2) : ι' × ℕ) ≠ (E q.1, q.2) := by
      obtain ⟨a, k⟩ := p
      obtain ⟨b, l⟩ := q
      intro hEq
      simp only [Prod.mk.injEq] at hEq
      exact hpq (by rw [E.injective hEq.1, hEq.2])
    exact Set.disjoint_left.mpr fun i hi hi' =>
      Set.disjoint_left.mp (hP (E p.1, p.2) (E q.1, q.2) hpq') hi hi'
  have hcov : ∀ (P : ι' × ℕ → Set ι'), (⋃ q, P q) = Set.univ →
      (⋃ p : ι × ℕ, E ⁻¹' P (E p.1, p.2)) = Set.univ := by
    intro P hP
    refine Set.eq_univ_of_forall fun i => ?_
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (by rw [hP]; exact Set.mem_univ (E i))
    refine Set.mem_iUnion.mpr ⟨(E.symm q.1, q.2), ?_⟩
    show E i ∈ P (E (E.symm q.1), q.2)
    rw [Equiv.apply_symm_apply]
    exact hq
  have hsum : ∀ (P : ι' × ℕ → Set ι') (hs : ∀ q, #(P q) < lam) (p : ι × ℕ) (f : ι' → X),
      lsumOf (lam := lam) (lt_of_eq_of_lt (hpre _) (hs (E p.1, p.2)))
          (fun i : E ⁻¹' P (E p.1, p.2) => f (E i))
        = ∑[lam] j ∈ P (E p.1, p.2), f j := by
    intro P hs p f
    let e : ↥(E ⁻¹' P (E p.1, p.2)) ≃ ↥(P (E p.1, p.2)) :=
      ⟨fun i => ⟨E i, i.2⟩, fun j => ⟨E.symm j, by simp⟩, fun i => by simp, fun j => by simp⟩
    exact (lsumOf_equiv (lam := lam) e (fun j : P (E p.1, p.2) => f j) (hs (E p.1, p.2))).symm
  exact ⟨{ I := fun p => E ⁻¹' d.I (E p.1, p.2)
           J := fun p => E ⁻¹' d.J (E p.1, p.2)
           I_disjoint := hdisj d.I d.I_disjoint
           J_disjoint := hdisj d.J d.J_disjoint
           I_cover := hcov d.I d.I_cover
           J_cover := hcov d.J d.J_cover
           I_small := fun p => ⟨lt_of_eq_of_lt (hpre _) (d.I_lt (E p.1, p.2))⟩
           J_small := fun p => ⟨lt_of_eq_of_lt (hpre _) (d.J_lt (E p.1, p.2))⟩
           u := fun p => d.u (E p.1, p.2)
           v := fun p => d.v (E p.1, p.2)
           v_limit := fun a => d.v_limit (E a)
           hI := fun p => (hsum d.I d.I_lt p x).trans (d.hI (E p.1, p.2))
           hJ := fun p => (hsum d.J d.J_lt p y).trans (d.hJ (E p.1, p.2)) }⟩

/-- Lemma 3.6(1): a family is braided to any reindexing of itself along a bijection — take the
partition into singletons on both sides. -/
theorem of_perm (x : ι → X) (π : ι ≃ ι) : IsBraided lam x (x ∘ π) := by
  have hlam0 : ℵ₀ ≤ lam := LMonoid.aleph0_le (lam := lam) (X := X)
  refine of_partition (slot0 id) (slot0 π.symm)
    (slot0_disjoint Function.injective_id) (slot0_disjoint π.symm.injective)
    (slot0_cover Function.surjective_id) (slot0_cover π.symm.surjective)
    (slot0_small hlam0 id) (slot0_small hlam0 π.symm) fun p => ?_
  rw [lsumOf_slot0 hlam0 id x p, lsumOf_slot0 hlam0 π.symm (x ∘ π) p]
  by_cases hp : p.2 = 0
  · rw [if_pos hp, if_pos hp]
    show x p.1 = x (π (π.symm p.1))
    rw [Equiv.apply_symm_apply]
  · rw [if_neg hp, if_neg hp]

/-- Lemma 3.6(2), reflexivity. -/
@[refl] theorem refl (x : ι → X) : IsBraided lam x x := by
  simpa using of_perm x (Equiv.refl ι)

/-- Lemma 3.6(2), symmetry.  Paper proof: shift the indices, replacing `(u, v)` by
`u' μ = u μ + v (μ+1)`, `v' μ = 0` at limit elements and `u' μ = v (μ+1)`, `v' μ = u μ`
otherwise; the new partitions are `I' = J` and `J'_μ = I_μ ∪ I_{μ+1}` at limit elements,
`J'_μ = I_{μ+1}` otherwise.  That `J'` is again an indexed partition, which the paper leaves
implicit, is `regroup` along the fibres of `(a, n) ↦ (a, n - 1)`. -/
@[symm] theorem symm {x y : ι → X} (h : IsBraided lam x y) : IsBraided lam y x := by
  obtain ⟨d⟩ := h
  -- The paper's shifted data.  At a limit `μ = (a, 0)`: `J'_μ = I_μ ∪ I_{μ+1}`,
  -- `u'_μ = u_μ + v_{μ+1}`, `v'_μ = 0`.  Otherwise: `J'_μ = I_{μ+1}`, `u'_μ = v_{μ+1}`,
  -- `v'_μ = u_μ`.  The roles of `I` and `J` are swapped: `I' = J`.
  let J' : ι × ℕ → Set ι := fun p => if p.2 = 0 then d.I p ∪ d.I (bsucc p) else d.I (bsucc p)
  let u' : ι × ℕ → X := fun p => if p.2 = 0 then d.u p + d.v (bsucc p) else d.v (bsucc p)
  let v' : ι × ℕ → X := fun p => if p.2 = 0 then 0 else d.u p
  -- `J'` is `I` regrouped along the fibres of `pred : (a, n) ↦ (a, n - 1)`, so it is again an
  -- indexed partition.
  let pred : ι × ℕ → ι × ℕ := fun p => (p.1, p.2 - 1)
  have hJ' : J' = regroup d.I fun p => pred ⁻¹' {p} := by
    funext ⟨a, n⟩
    ext i
    simp only [J', regroup, pred, bsucc, Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff,
      Set.mem_iUnion, exists_prop, Prod.exists]
    constructor
    · rintro hi
      split_ifs at hi with hn
      · rcases hi with hi | hi
        · exact ⟨a, n, ⟨rfl, by omega⟩, hi⟩
        · exact ⟨a, n + 1, ⟨rfl, by omega⟩, hi⟩
      · exact ⟨a, n + 1, ⟨rfl, by omega⟩, hi⟩
    · rintro ⟨b, m, ⟨rfl, hm⟩, hi⟩
      split_ifs with hn
      · subst hn
        rcases Nat.lt_or_ge m 1 with h | h
        · exact Or.inl (by rwa [show m = 0 by omega] at hi)
        · exact Or.inr (by rwa [show m = 0 + 1 by omega] at hi)
      · rwa [show m = n + 1 by omega] at hi
  have J'_disjoint : ∀ p q, p ≠ q → Disjoint (J' p) (J' q) := by
    rw [hJ']
    exact fun p q hpq => regroup_disjoint d.I_disjoint
      (fun p q hpq => Set.disjoint_left.mpr fun r hp hq => hpq (hp.symm.trans hq)) hpq
  have J'_cover : (⋃ p, J' p) = Set.univ := by
    rw [hJ']
    exact regroup_cover d.I_cover (Set.eq_univ_of_forall fun r => Set.mem_iUnion.mpr ⟨pred r, rfl⟩)
  have J'_small : ∀ p, #(J' p) < lam := fun p => by
    have hsub : J' p ⊆ d.I p ∪ d.I (bsucc p) := by
      dsimp only [J']; split_ifs
      exacts [le_rfl, Set.subset_union_right]
    exact (mk_le_mk_of_subset hsub).trans_lt ((mk_union_le _ _).trans_lt
      (add_lt_of_lt (aleph0_le (X := X)) (d.I_lt p) (d.I_lt (bsucc p))))
  refine ⟨{ I := d.J
            J := J'
            I_disjoint := d.J_disjoint
            J_disjoint := J'_disjoint
            I_cover := d.J_cover
            J_cover := J'_cover
            I_small := d.J_small
            J_small := fun p => ⟨J'_small p⟩
            u := u'
            v := v'
            v_limit := fun _ => rfl
            hI := fun p => ?_
            hJ := fun p => ?_ }⟩
  · -- `Σ_{I'_μ} y = v_{μ+1} + u_μ = v'_μ + u'_μ`
    rw [d.hJ p]
    obtain ⟨a, _ | m⟩ := p
    · simp [v', u', add_comm]
    · simp [v', u', bsucc, add_comm]
  · -- `Σ_{J'_μ} x = v'_{μ+1} + u'_μ`
    obtain ⟨a, _ | m⟩ := p
    · -- limit: `Σ_{I_μ ∪ I_{μ+1}} x = (v_μ + u_μ) + (v_{μ+1} + u_{μ+1})`, and `v_μ = 0`
      have hdisj : Disjoint (d.I (a, 0)) (d.I (bsucc (a, 0))) :=
        d.I_disjoint _ _ fun h => by simp [bsucc] at h
      refine (lsumOf_union _ _ hdisj (d.I_lt _) (d.I_lt _) x (J'_small (a, 0))).trans ?_
      rw [d.hI, d.hI, d.v_limit]
      simp only [v', u', bsucc]
      simp
      abel
    · -- successor: `Σ_{I_{μ+1}} x = v_{μ+1} + u_{μ+1}`
      refine (d.hI (bsucc (a, m + 1))).trans ?_
      simp [v', u', bsucc, add_comm]

end IsBraided

end KappaMonoid
