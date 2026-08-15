/-
**Definition 3.1(1)**: `BraidingData`, `IsBraided`, regrouping a partition along a partition
of the index set, and the basic properties of the braiding relation - **Lemma 3.6**.
-/
import KappaMonoid.Braiding.Prelim

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
  I_small : ∀ p, #(I p) < lam
  J_small : ∀ p, #(J p) < lam
  u : ι × ℕ → X
  v : ι × ℕ → X
  /-- `v` vanishes at the limit elements of the well-order. -/
  v_limit : ∀ a : ι, v (a, 0) = 0
  hI : ∀ p, lsumOf (lam := lam) (I_small p) (fun i : I p => x i) = v p + u p
  hJ : ∀ p, lsumOf (lam := lam) (J_small p) (fun j : J p => y j) = v (bsucc p) + u p

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
  I_small := fun p => lt_aleph0_iff_set_finite.mpr (hIfin p)
  J_small := fun p => lt_aleph0_iff_set_finite.mpr (hJfin p)
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
theorem of_partition {x y : ι → X} (I J : ι × ℕ → Set ι)
    (hIdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q))
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hIcov : (⋃ p, I p) = Set.univ) (hJcov : (⋃ p, J p) = Set.univ)
    (hIsmall : ∀ p, #(I p) < lam) (hJsmall : ∀ p, #(J p) < lam)
    (heq : ∀ p, lsumOf (lam := lam) (hIsmall p) (fun i : I p => x i)
        = lsumOf (lam := lam) (hJsmall p) (fun j : J p => y j)) :
    IsBraided lam x y :=
  ⟨{ I := I
     J := J
     I_disjoint := hIdisj
     J_disjoint := hJdisj
     I_cover := hIcov
     J_cover := hJcov
     I_small := hIsmall
     J_small := hJsmall
     u := fun p => lsumOf (lam := lam) (hIsmall p) (fun i : I p => x i)
     v := fun _ => 0
     v_limit := fun _ => rfl
     hI := fun _ => (zero_add _).symm
     hJ := fun p => (heq p).symm.trans (zero_add _).symm }⟩

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
        = lsumOf (lam := lam) (hs (E p.1, p.2)) (fun j : P (E p.1, p.2) => f j) := by
    intro P hs p f
    refine (lsumOf_equiv (lam := lam) (hs (E p.1, p.2))
      (lt_of_eq_of_lt (hpre _) (hs (E p.1, p.2)))
      ⟨fun i => ⟨E i, i.2⟩, fun j => ⟨E.symm j, by simp⟩, fun i => by simp,
        fun j => by simp⟩ (fun j : P (E p.1, p.2) => f j)).symm
  exact ⟨{ I := fun p => E ⁻¹' d.I (E p.1, p.2)
           J := fun p => E ⁻¹' d.J (E p.1, p.2)
           I_disjoint := hdisj d.I d.I_disjoint
           J_disjoint := hdisj d.J d.J_disjoint
           I_cover := hcov d.I d.I_cover
           J_cover := hcov d.J d.J_cover
           I_small := fun p => lt_of_eq_of_lt (hpre _) (d.I_small (E p.1, p.2))
           J_small := fun p => lt_of_eq_of_lt (hpre _) (d.J_small (E p.1, p.2))
           u := fun p => d.u (E p.1, p.2)
           v := fun p => d.v (E p.1, p.2)
           v_limit := fun a => d.v_limit (E a)
           hI := fun p => (hsum d.I d.I_small p x).trans (d.hI (E p.1, p.2))
           hJ := fun p => (hsum d.J d.J_small p y).trans (d.hJ (E p.1, p.2)) }⟩

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
otherwise. -/
@[symm] theorem symm {x y : ι → X} (h : IsBraided lam x y) : IsBraided lam y x := by
  classical
  obtain ⟨d⟩ := h
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  set J' : ι × ℕ → Set ι :=
    fun p => if p.2 = 0 then d.I p ∪ d.I (bsucc p) else d.I (bsucc p) with hJ'def
  set u' : ι × ℕ → X :=
    fun p => if p.2 = 0 then d.u p + d.v (bsucc p) else d.v (bsucc p) with hu'def
  set v' : ι × ℕ → X := fun p => if p.2 = 0 then (0 : X) else d.u p with hv'def
  -- `bsucc` never fixes an index, and distinct pieces of `I` are disjoint, so each element
  -- of `ι` lies in exactly one piece.
  have hne_succ : ∀ p : ι × ℕ, p ≠ bsucc p := fun p hp =>
    Nat.succ_ne_self p.2 (congrArg Prod.snd hp).symm
  have huniq : ∀ (r s : ι × ℕ) (i : ι), i ∈ d.I r → i ∈ d.I s → r = s := by
    intro r s i hir his
    by_contra hrs
    exact Set.disjoint_left.mp (d.I_disjoint r s hrs) hir his
  have hJ'zero : ∀ a : ι, J' (a, 0) = d.I (a, 0) ∪ d.I (bsucc (a, 0)) := fun _ => rfl
  have hJ'succ : ∀ (a : ι) (m : ℕ), J' (a, m + 1) = d.I (bsucc (a, m + 1)) := fun _ _ => rfl
  have hJ'small : ∀ p, #(J' p) < lam := by
    rintro ⟨a, n⟩
    rcases n with _ | m
    · rw [hJ'zero a]
      exact lt_of_le_of_lt (Cardinal.mk_union_le _ _)
        (Cardinal.add_lt_of_lt hlam0 (d.I_small (a, 0)) (d.I_small (bsucc (a, 0))))
    · rw [hJ'succ a m]
      exact d.I_small _
  have hJ'mem : ∀ (p : ι × ℕ) (i : ι), i ∈ J' p →
      ∃ r : ι × ℕ, i ∈ d.I r ∧ (r = bsucc p ∨ (p.2 = 0 ∧ r = p)) := by
    rintro ⟨a, n⟩ i hi
    rcases n with _ | m
    · rw [hJ'zero a] at hi
      rcases hi with hi | hi
      · exact ⟨(a, 0), hi, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨bsucc (a, 0), hi, Or.inl rfl⟩
    · rw [hJ'succ a m] at hi
      exact ⟨bsucc (a, m + 1), hi, Or.inl rfl⟩
  have hJ'disjoint : ∀ p q, p ≠ q → Disjoint (J' p) (J' q) := by
    intro p q hpq
    rw [Set.disjoint_left]
    intro i hip hiq
    obtain ⟨r, hir, hr⟩ := hJ'mem p i hip
    obtain ⟨s, his, hs⟩ := hJ'mem q i hiq
    have hrs : r = s := huniq r s i hir his
    refine hpq ?_
    rcases hr with hr | ⟨hp0, hrp⟩ <;> rcases hs with hs | ⟨hq0, hsq⟩
    · exact bsucc_injective (hr.symm.trans (hrs.trans hs))
    · exact absurd ((congrArg Prod.snd (hr.symm.trans (hrs.trans hsq))).trans hq0)
        (Nat.succ_ne_zero p.2)
    · exact absurd ((congrArg Prod.snd (hrp.symm.trans (hrs.trans hs))).symm.trans hp0)
        (Nat.succ_ne_zero q.2)
    · exact hrp.symm.trans (hrs.trans hsq)
  have hJ'cover : (⋃ p, J' p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    have hi : i ∈ (⋃ r, d.I r) := d.I_cover ▸ Set.mem_univ i
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hi
    obtain ⟨a, m⟩ := r
    rcases m with _ | m
    · exact Set.mem_iUnion.mpr ⟨(a, 0), by rw [hJ'zero a]; exact Or.inl hr⟩
    · refine Set.mem_iUnion.mpr ⟨(a, m), ?_⟩
      rcases m with _ | m'
      · rw [hJ'zero a]; exact Or.inr hr
      · rw [hJ'succ a m']; exact hr
  -- the shifted braiding families
  have hv'zero : ∀ a : ι, v' (a, 0) = 0 := fun _ => rfl
  have hv'succ : ∀ p : ι × ℕ, v' (bsucc p) = d.u (bsucc p) := fun _ => rfl
  have hu'zero : ∀ a : ι, u' (a, 0) = d.u (a, 0) + d.v (bsucc (a, 0)) := fun _ => rfl
  have hu'succ : ∀ (a : ι) (m : ℕ), u' (a, m + 1) = d.v (bsucc (a, m + 1)) := fun _ _ => rfl
  have hvu' : ∀ p : ι × ℕ, v' p + u' p = d.u p + d.v (bsucc p) := by
    rintro ⟨a, n⟩
    rcases n with _ | m
    · rw [hv'zero a, hu'zero a, zero_add]
    · rw [hu'succ a m]
      exact congrArg₂ (· + ·) rfl rfl
  -- the two defining equations
  have hI'eq : ∀ p, lsumOf (lam := lam) (d.J_small p) (fun i : d.J p => y i) = v' p + u' p := by
    intro p
    rw [d.hJ p, hvu' p]
    exact add_comm _ _
  have hJ'eq : ∀ p, lsumOf (lam := lam) (hJ'small p) (fun j : J' p => x j)
      = v' (bsucc p) + u' p := by
    rintro ⟨a, n⟩
    rcases n with _ | m
    · have hdisj : Disjoint (d.I (a, 0)) (d.I (bsucc (a, 0))) :=
        d.I_disjoint _ _ (hne_succ (a, 0))
      refine (lsumOf_union (d.I (a, 0)) (d.I (bsucc (a, 0))) hdisj (d.I_small (a, 0))
        (d.I_small (bsucc (a, 0))) (hJ'small (a, 0)) x).trans ?_
      rw [d.hI (a, 0), d.hI (bsucc (a, 0)), d.v_limit a, hv'succ (a, 0), hu'zero a, zero_add]
      abel
    · have hU : lsumOf (lam := lam) (hJ'small (a, m + 1)) (fun j : J' (a, m + 1) => x j)
          = d.v (bsucc (a, m + 1)) + d.u (bsucc (a, m + 1)) := d.hI (bsucc (a, m + 1))
      rw [hU, hv'succ (a, m + 1), hu'succ a m]
      exact add_comm _ _
  exact ⟨{ I := d.J
           J := J'
           I_disjoint := d.J_disjoint
           J_disjoint := hJ'disjoint
           I_cover := d.J_cover
           J_cover := hJ'cover
           I_small := d.J_small
           J_small := hJ'small
           u := u'
           v := v'
           v_limit := hv'zero
           hI := hI'eq
           hJ := hJ'eq }⟩

end IsBraided

end KappaMonoid
