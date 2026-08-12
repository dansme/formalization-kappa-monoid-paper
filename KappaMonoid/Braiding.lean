/-
Part 2 — Section 3: braiding of `κ`-indexed families over a `λ⁻`-monoid.

Modelling the "limit well-order" of Definition 3.1
-------------------------------------------------
The paper fixes a *limit well-order* on `κ`: a well-order in which every element has a
successor (equivalently, one with no maximum).  Such an order decomposes uniquely into
`ω`-blocks indexed by its limit elements, and for a limit well-order of cardinality `κ`
there are exactly `κ` many blocks (as `κ · ℵ₀ = κ`).  Conversely `ι × ℕ`, ordered
lexicographically, is a limit well-order of cardinality `#ι` whenever `ι` is infinite.

We therefore index braiding partitions and braiding families by `ι × ℕ`, with successor
`(a, n) ↦ (a, n + 1)` and limit elements `(a, 0)`.  This is *not* a loss of generality: it
is exactly the content of Lemma 3.4(2)(3) (a braiding decomposes into countable braidings)
together with Lemma 3.5 (independence of the chosen well-order), which is why those two
lemmas do not appear as separate results below — they are absorbed into the definition.
-/
import KappaMonoid.Basic

universe u v w

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid

/-! ## Auxiliary lemmas

Cardinal bookkeeping for the index type `ι × ℕ` of braiding partitions, and the `finsum`
bridge used for `λ = ℵ₀`. -/

section Aux

/-- `#(ι × ℕ) ≤ κ` whenever `#ι ≤ κ` and `κ` is infinite: the index type of braiding
partitions is no bigger than the index type of the families. -/
theorem mk_prod_nat_le {κ : Cardinal.{u}} {ι : Type u} (hκ : ℵ₀ ≤ κ) (hι : #ι ≤ κ) :
    #(ι × ℕ) ≤ κ := by
  have hmp : #(ι × ℕ) = #ι * ℵ₀ := by simp [Cardinal.mk_prod]
  rw [hmp]
  calc #ι * ℵ₀ ≤ κ * κ := mul_le_mul' hι hκ
    _ = κ := Cardinal.mul_eq_self hκ

/-! ## Finsum bridge for `λ = ℵ₀`

For `lam = ℵ₀` every index set occurring in a braiding is finite, so all the sums involved are
ordinary finite sums.  Working with `∑ᶠ i ∈ S, f i` (Mathlib's `finsum`) instead of
`lsumOf hS (fun i : S => f i)` removes the finiteness side conditions from the *terms* and gives
access to Mathlib's `finsum_mem_*` API. -/

/-- Splitting a `finsum` over a finite set along a subset. -/
theorem finsum_mem_split {α : Type u} {M : Type v} [AddCommMonoid M] (f : α → M) {S T : Set α}
    (hST : S ⊆ T) (hT : T.Finite) :
    ∑ᶠ i ∈ T, f i = (∑ᶠ i ∈ S, f i) + ∑ᶠ i ∈ T \ S, f i := by
  have hdisj : Disjoint S (T \ S) := by
    rw [Set.disjoint_left]; intro i hi hi'; exact hi'.2 hi
  rw [← finsum_mem_union hdisj (hT.subset hST) (hT.sdiff (t := S)), Set.union_sdiff_cancel hST]

/-- Indices outside a subset where the summand vanishes may be dropped from a `finsum`. -/
theorem finsum_mem_eq_of_diff_eq_zero {α : Type u} {M : Type v} [AddCommMonoid M] {f : α → M}
    {S T : Set α} (hST : S ⊆ T) (hT : T.Finite) (h0 : ∀ i ∈ T \ S, f i = 0) :
    ∑ᶠ i ∈ T, f i = ∑ᶠ i ∈ S, f i := by
  rw [finsum_mem_split f hST hT, finsum_mem_eq_zero_of_forall_eq_zero h0, add_zero]

/-- A set contained in a union splits into the parts it shares with the two pieces. -/
theorem eq_union_inter_of_subset_union {α : Type u} {A B C : Set α} (h : A ⊆ B ∪ C) :
    A = (B ∩ A) ∪ (A ∩ C) := by
  refine Set.Subset.antisymm (fun j hj => ?_) ?_
  · rcases h hj with hj' | hj'
    · exact Or.inl ⟨hj', hj⟩
    · exact Or.inr ⟨hj, hj'⟩
  · rintro j (⟨-, hj⟩ | ⟨hj, -⟩) <;> exact hj

/-- Variant of `eq_union_inter_of_subset_union` when the first piece is contained in `A`. -/
theorem eq_union_inter_of_subset_union' {α : Type u} {A B C : Set α} (h : A ⊆ B ∪ C)
    (hB : B ⊆ A) : A = B ∪ (A ∩ C) := by
  refine Set.Subset.antisymm (fun j hj => ?_) ?_
  · rcases h hj with hj' | hj'
    · exact Or.inl hj'
    · exact Or.inr ⟨hj, hj'⟩
  · rintro j (hj | ⟨hj, -⟩)
    · exact hB hj
    · exact hj

/-- A `finsum` over a three-element set. -/
theorem finsum_mem_triple {α : Type u} {M : Type v} [AddCommMonoid M] {a b c : α} (f : α → M)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ᶠ i ∈ ({a, b, c} : Set α), f i = f a + f b + f c := by
  rw [show ({a, b, c} : Set α) = insert a {b, c} from rfl,
    finsum_mem_insert f (by simp [hab, hac]) ((Set.finite_singleton c).insert b),
    finsum_mem_pair hbc, add_assoc]


end Aux

/-- The successor map of the limit well-order modelled by `ι × ℕ`. -/
def bsucc {ι : Type u} (p : ι × ℕ) : ι × ℕ := (p.1, p.2 + 1)

theorem bsucc_injective {ι : Type u} : Function.Injective (bsucc (ι := ι)) := by
  rintro ⟨a, n⟩ ⟨b, m⟩ h
  simp [bsucc, Prod.ext_iff] at h
  simp [h.1, h.2]

@[simp] theorem bsucc_snd_ne_zero {ι : Type u} (p : ι × ℕ) : (bsucc p).2 ≠ 0 := Nat.succ_ne_zero _

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
  · letI : Unique ↥(slot0 f (a, 0)) := Set.uniqueSingleton (f a)
    rw [lsumOf_unique (slot0_small hlam0 f (a, 0)) (fun i : slot0 f (a, 0) => x i), if_pos rfl]
    rfl
  · letI : IsEmpty ↥(slot0 f (a, n + 1)) := inferInstanceAs (IsEmpty (↥(∅ : Set ι)))
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
    Cardinal.mk_congr ⟨fun i => ⟨E i, i.2⟩, fun j => ⟨E.symm j, by simpa using j.2⟩,
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
      ⟨fun i => ⟨E i, i.2⟩, fun j => ⟨E.symm j, by simpa using j.2⟩, fun i => by simp,
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

/-! ### Well-order scaffolding for `λ = ℵ₀` transitivity

The paper's proof of Lemma 3.7 runs a transfinite recursion along the "limit well-order on
`κ`" (the well-order whose successor structure matches `bsucc`, i.e. whose limit elements are
exactly the pairs `(a, 0)`). We model this well-order concretely as the lexicographic order on
`ι × ℕ`: an arbitrary (choice-provided) well-order on the "block" type `ι`, refined within each
block by the usual order on the "offset" `ℕ`. -/

section TransAleph0

variable {X : Type v} [LMonoid ℵ₀ X] {ι : Type u}

/-- The lexicographic well-order on `ι × ℕ` modeling the paper's limit well-order on `κ`:
blocks are ordered by an arbitrary well-order on `ι`, and offsets within a block by the usual
order on `ℕ`. Each block `a` contributes a run `(a, 0) < (a, 1) < (a, 2) < ⋯`. -/
def kOrd (ι : Type u) : (ι × ℕ) → (ι × ℕ) → Prop :=
  Prod.Lex (WellOrderingRel : ι → ι → Prop) (· < · : ℕ → ℕ → Prop)

instance kOrd.isWellOrder : IsWellOrder (ι × ℕ) (kOrd ι) :=
  inferInstanceAs (IsWellOrder _ (Prod.Lex _ _))

theorem kOrd_iff {p q : ι × ℕ} :
    kOrd ι p q ↔ WellOrderingRel p.1 q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) :=
  Prod.lex_def

theorem kOrd_bsucc (p : ι × ℕ) : kOrd ι p (bsucc p) :=
  Prod.Lex.right p.1 (Nat.lt_succ_self p.2)

/-- `bsucc p` is the immediate `kOrd`-successor of `p`: nothing lies strictly between them. -/
theorem kOrd_not_between {p q : ι × ℕ} (h1 : kOrd ι p q) (h2 : kOrd ι q (bsucc p)) : False := by
  have hirr : ∀ c d : ι, WellOrderingRel c d → ¬ WellOrderingRel d c :=
    (IsWellFounded.wf (r := (WellOrderingRel : ι → ι → Prop))).asymmetric
  rw [kOrd_iff] at h1 h2
  simp only [bsucc] at h2
  rcases h1 with h1 | ⟨h1a, h1n⟩ <;> rcases h2 with h2 | ⟨h2a, h2n⟩
  · exact hirr _ _ h1 h2
  · rw [h2a] at h1; exact hirr _ _ h1 h1
  · rw [← h1a] at h2; exact hirr _ _ h2 h2
  · omega

/-! ### The `blockOf` choice function

Given an indexed partition `I : ι × ℕ → Set ι` of `ι` (disjoint pieces covering `ι`), each
`i : ι` lies in exactly one piece; `blockOf` picks it out. -/

/-- The (unique) position whose piece contains `i`, for a partition `I` of `ι`. -/
noncomputable def blockOf (I : ι × ℕ → Set ι) (hcov : (⋃ p, I p) = Set.univ) (i : ι) : ι × ℕ :=
  (Set.mem_iUnion.mp (by rw [hcov]; exact Set.mem_univ i)).choose

theorem mem_blockOf (I : ι × ℕ → Set ι) (hcov : (⋃ p, I p) = Set.univ) (i : ι) :
    i ∈ I (blockOf I hcov i) :=
  (Set.mem_iUnion.mp (by rw [hcov]; exact Set.mem_univ i)).choose_spec

theorem blockOf_eq {I : ι × ℕ → Set ι} (hdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q))
    (hcov : (⋃ p, I p) = Set.univ) {i : ι} {p : ι × ℕ} (hp : i ∈ I p) :
    blockOf I hcov i = p := by
  by_contra hne
  exact Set.disjoint_left.mp (hdisj _ _ hne) (mem_blockOf I hcov i) hp

/-! ### Left-saturation closure

Terminology from the paper's proof of Lemma 3.7 (`lep`, `rep`, left saturation), and the
`satClosure` construction used to build each step `𝒜_α`/`ℬ_α` of the transfinite recursion:
starting from a finite "seed" of positions, grow it backwards along `bsucc`-predecessors until
either a block-start or an already-used (`Ua`) position is reached. -/

/-- The "left endpoints" of `S`: positions in `S` with no `bsucc`-predecessor in `S`. -/
def lep (S : Set (ι × ℕ)) : Set (ι × ℕ) := {p ∈ S | ∀ q, bsucc q = p → q ∉ S}

/-- The "right endpoints" of `S`: positions in `S` whose `bsucc`-successor is not in `S`. -/
def rep (S : Set (ι × ℕ)) : Set (ι × ℕ) := {p ∈ S | bsucc p ∉ S}

/-- The successors of the right endpoints of `S`. -/
def repSucc (S : Set (ι × ℕ)) : Set (ι × ℕ) := bsucc '' rep S

/-- `S` is left saturated relative to `T`: if `p ∈ S` is `bsucc q`, and `q` is not already
accounted for by `T`, then `q` must also lie in `S`. -/
def LeftSaturated (S T : Set (ι × ℕ)) : Prop :=
  ∀ p q, bsucc q = p → p ∈ S → q ∉ T → q ∈ S

/-- One step of left-saturation growth: add every `bsucc`-predecessor not already in `Ua`. -/
def satStep (Ua S : Set (ι × ℕ)) : Set (ι × ℕ) :=
  S ∪ {q | q ∉ Ua ∧ bsucc q ∈ S}

/-- The left-saturation closure of a seed `C`, relative to the already-used set `Ua`: iterate
`satStep` countably often. Each block's descent terminates after finitely many steps (bounded
by the seed's maximal offset in that block), so this stabilizes; see `satClosure_finite`. -/
def satClosure (Ua C : Set (ι × ℕ)) : Set (ι × ℕ) :=
  ⋃ k : ℕ, (satStep Ua)^[k] C

theorem subset_satClosure (Ua C : Set (ι × ℕ)) : C ⊆ satClosure Ua C := by
  unfold satClosure
  simpa using Set.subset_iUnion (fun k => (satStep Ua)^[k] C) 0

theorem satClosure_disjoint {Ua C : Set (ι × ℕ)} (hC : Disjoint C Ua) :
    Disjoint (satClosure Ua C) Ua := by
  rw [Set.disjoint_left]
  intro p hp hpUa
  simp only [satClosure, Set.mem_iUnion] at hp
  obtain ⟨k, hp⟩ := hp
  induction k with
  | zero => exact Set.disjoint_left.mp hC hp hpUa
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hp
    rcases hp with hp | ⟨hp, -⟩
    · exact ih hp
    · exact hp hpUa

theorem leftSaturated_satClosure (Ua C : Set (ι × ℕ)) :
    LeftSaturated (satClosure Ua C) Ua := by
  intro p q hpq hp hq
  simp only [satClosure, Set.mem_iUnion] at hp ⊢
  obtain ⟨k, hp⟩ := hp
  refine ⟨k + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact Or.inr ⟨hq, by rw [hpq]; exact hp⟩

theorem satStep_bound (Ua : Set (ι × ℕ)) {F : Set ι} {N : ℕ} {S : Set (ι × ℕ)}
    (hS : S ⊆ {p : ι × ℕ | p.1 ∈ F ∧ p.2 ≤ N}) :
    satStep Ua S ⊆ {p : ι × ℕ | p.1 ∈ F ∧ p.2 ≤ N} := by
  rintro p (hp | ⟨-, hp⟩)
  · exact hS hp
  · obtain ⟨hF, hN⟩ := hS hp
    simp only [bsucc] at hF hN
    exact ⟨hF, by omega⟩

theorem satClosure_subset_bound (Ua : Set (ι × ℕ)) {F : Set ι} {N : ℕ} {C : Set (ι × ℕ)}
    (hC : C ⊆ {p : ι × ℕ | p.1 ∈ F ∧ p.2 ≤ N}) :
    satClosure Ua C ⊆ {p : ι × ℕ | p.1 ∈ F ∧ p.2 ≤ N} := by
  apply Set.iUnion_subset
  intro k
  induction k with
  | zero => simpa using hC
  | succ n ih => rw [Function.iterate_succ_apply']; exact satStep_bound Ua ih

theorem satClosure_finite {Ua C : Set (ι × ℕ)} (hC : C.Finite) : (satClosure Ua C).Finite := by
  obtain ⟨N, hN⟩ := (hC.image Prod.snd).bddAbove
  have hCF : C ⊆ {p : ι × ℕ | p.1 ∈ Prod.fst '' C ∧ p.2 ≤ N} := fun p hp =>
    ⟨Set.mem_image_of_mem _ hp, hN (Set.mem_image_of_mem _ hp)⟩
  have hbound : {p : ι × ℕ | p.1 ∈ Prod.fst '' C ∧ p.2 ≤ N}.Finite := by
    have heq : {p : ι × ℕ | p.1 ∈ Prod.fst '' C ∧ p.2 ≤ N} = (Prod.fst '' C) ×ˢ Set.Iic N := by
      ext p; simp [Set.mem_prod, Set.mem_Iic]
    rw [heq]
    exact (hC.image Prod.fst).prod (Set.finite_Iic N)
  exact hbound.subset (satClosure_subset_bound Ua hCF)

/-- The key covering-existence step of Lemma 3.7's recursion: given already-used positions `Ua`
and a finite residual `R ⊆ ι` still to be covered by pieces of a partition `d.J`, there is a
finite set of positions `𝒜`, disjoint from `Ua` and left saturated in `Ua`, whose `d.J`-pieces
cover `R`. -/
theorem exists_cover_step {x y : ι → X} (d : BraidingData ℵ₀ x y) {Ua : Set (ι × ℕ)} {R : Set ι}
    (hR : R.Finite) (hRUa : ∀ i ∈ R, blockOf d.J d.J_cover i ∉ Ua) :
    ∃ 𝒜 : Set (ι × ℕ), 𝒜.Finite ∧ Disjoint 𝒜 Ua ∧ LeftSaturated 𝒜 Ua ∧
      R ⊆ ⋃ ν ∈ 𝒜, d.J ν := by
  refine ⟨satClosure Ua (blockOf d.J d.J_cover '' R), satClosure_finite (hR.image _),
    satClosure_disjoint ?_, leftSaturated_satClosure _ _, ?_⟩
  · rw [Set.disjoint_left]
    rintro p ⟨i, hi, rfl⟩ hpUa
    exact hRUa i hi hpUa
  · intro i hi
    simp only [Set.mem_iUnion]
    exact ⟨blockOf d.J d.J_cover i, subset_satClosure _ _ (Set.mem_image_of_mem _ hi),
      mem_blockOf d.J d.J_cover i⟩

theorem kOrd_wf : WellFounded (kOrd ι) := IsWellFounded.wf

/-- The `kOrd`-least position not yet used, when some position remains unused: this is seeded
into every recursion step to guarantee the constructed partition eventually exhausts `ι × ℕ`. -/
noncomputable def minCompl (Ua : Set (ι × ℕ)) (h : Uaᶜ.Nonempty) : ι × ℕ :=
  kOrd_wf.min Uaᶜ h

theorem minCompl_mem (Ua : Set (ι × ℕ)) (h : Uaᶜ.Nonempty) : minCompl Ua h ∈ Uaᶜ :=
  WellFounded.min_mem _ Uaᶜ h

/-! ## Lemma 3.8: transitivity from an aligned pair of braidings

The grouping of the index set used in the paper's proof: blocks are merged in groups of three,
with the limit position of each block left alone. -/

variable {x y z : ι → X}

/-- The "three-block grouping": `(a, 0)` keeps its own position, and `(a, l+1)` collects the
three positions `(a, 3l+1)`, `(a, 3l+2)`, `(a, 3l+3)`. -/
def grp3 (p : ι × ℕ) : Set (ι × ℕ) :=
  match p.2 with
  | 0 => {(p.1, 0)}
  | l + 1 => {(p.1, 3 * l + 1), (p.1, 3 * l + 2), (p.1, 3 * l + 3)}

theorem grp3_zero (a : ι) : grp3 (a, 0) = {(a, 0)} := rfl

theorem grp3_succ (a : ι) (l : ℕ) :
    grp3 (a, l + 1) = {(a, 3 * l + 1), (a, 3 * l + 2), (a, 3 * l + 3)} := rfl

theorem pair_ne {a : ι} {i j : ℕ} (hij : i ≠ j) : ((a, i) : ι × ℕ) ≠ (a, j) :=
  fun h => hij (congrArg Prod.snd h)

theorem grp3_finite (p : ι × ℕ) : (grp3 p).Finite := by
  obtain ⟨a, n⟩ := p
  cases n with
  | zero => rw [grp3_zero]; exact Set.finite_singleton _
  | succ l => rw [grp3_succ]; exact ((Set.finite_singleton _).insert _).insert _

theorem grp3_mem_fst {p ν : ι × ℕ} (h : ν ∈ grp3 p) : ν.1 = p.1 := by
  obtain ⟨a, n⟩ := p
  cases n with
  | zero => rw [grp3_zero] at h; rw [h]
  | succ l =>
    rw [grp3_succ] at h
    rcases h with h | h | h <;> rw [h]

theorem grp3_disjoint (p q : ι × ℕ) (hpq : p ≠ q) : Disjoint (grp3 p) (grp3 q) := by
  obtain ⟨a, n⟩ := p
  obtain ⟨b, m⟩ := q
  rw [Set.disjoint_left]
  intro ν hν hν'
  have hab : a = b := by
    have h1 := grp3_mem_fst hν
    have h2 := grp3_mem_fst hν'
    simp only at h1 h2
    rw [← h1, h2]
  subst hab
  have hnm : n ≠ m := fun h => hpq (by rw [h])
  cases n with
  | zero =>
    cases m with
    | zero => exact hnm rfl
    | succ l =>
      rw [grp3_zero] at hν
      rw [grp3_succ] at hν'
      rw [hν] at hν'
      rcases hν' with h | h | h <;> exact absurd (congrArg Prod.snd h) (by omega)
  | succ l =>
    cases m with
    | zero =>
      rw [grp3_zero] at hν'
      rw [grp3_succ] at hν
      rw [hν'] at hν
      rcases hν with h | h | h <;> exact absurd (congrArg Prod.snd h) (by omega)
    | succ k =>
      rw [grp3_succ] at hν hν'
      have hl : l ≠ k := fun h => hnm (by rw [h])
      rcases hν with h | h | h <;> rcases hν' with h' | h' <;>
        first
          | (rw [h] at h'; exact absurd (congrArg Prod.snd h') (by omega))
          | (rcases h' with h' | h' <;> rw [h] at h' <;>
              exact absurd (congrArg Prod.snd h') (by omega))

theorem grp3_cover : (⋃ p : ι × ℕ, grp3 p) = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨a, n⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Set.mem_iUnion.mpr ⟨(a, 0), by rw [h, grp3_zero]; rfl⟩
  · obtain ⟨l, hl⟩ : ∃ l, n = 3 * l + 1 ∨ n = 3 * l + 2 ∨ n = 3 * l + 3 := ⟨(n - 1) / 3, by omega⟩
    refine Set.mem_iUnion.mpr ⟨(a, l + 1), ?_⟩
    rw [grp3_succ]
    rcases hl with h1 | h1 | h1 <;> rw [h1] <;> simp

/-- Lemma 3.8's combinatorial core: if two braidings sharing the middle family `y` have
partitions of `y` that interleave block by block, they can be merged (in groups of three) into
a braiding of `x` and `z`. -/
theorem of_aligned (d : BraidingData ℵ₀ x y) (e : BraidingData ℵ₀ y z)
    (h1 : ∀ p, e.I p ⊆ d.J p ∪ d.J (bsucc p))
    (h2 : ∀ p, d.J (bsucc p) ⊆ e.I p ∪ e.I (bsucc p))
    (h3 : ∀ a : ι, d.J (a, 0) ⊆ e.I (a, 0)) :
    IsBraided ℵ₀ x z := by
  classical
  have dIfin : ∀ p, (d.I p).Finite := fun p => lt_aleph0_iff_set_finite.mp (d.I_small p)
  have dJfin : ∀ p, (d.J p).Finite := fun p => lt_aleph0_iff_set_finite.mp (d.J_small p)
  have eIfin : ∀ p, (e.I p).Finite := fun p => lt_aleph0_iff_set_finite.mp (e.I_small p)
  have eJfin : ∀ p, (e.J p).Finite := fun p => lt_aleph0_iff_set_finite.mp (e.J_small p)
  have dIsum : ∀ p, ∑ᶠ i ∈ d.I p, x i = d.v p + d.u p := fun p => by
    rw [← LMonoid.lsumOf_eq_finsum (d.I_small p)]; exact d.hI p
  have dJsum : ∀ p, ∑ᶠ j ∈ d.J p, y j = d.v (bsucc p) + d.u p := fun p => by
    rw [← LMonoid.lsumOf_eq_finsum (d.J_small p)]; exact d.hJ p
  have eIsum : ∀ p, ∑ᶠ j ∈ e.I p, y j = e.v p + e.u p := fun p => by
    rw [← LMonoid.lsumOf_eq_finsum (e.I_small p)]; exact e.hI p
  have eJsum : ∀ p, ∑ᶠ k ∈ e.J p, z k = e.v (bsucc p) + e.u p := fun p => by
    rw [← LMonoid.lsumOf_eq_finsum (e.J_small p)]; exact e.hJ p
  have hnesucc : ∀ p : ι × ℕ, p ≠ bsucc p := fun p hp =>
    Nat.succ_ne_self p.2 (congrArg Prod.snd hp).symm
  -- the "overlap" sums `s` and `t`
  obtain ⟨s, hs⟩ : ∃ s : ι × ℕ → X, ∀ p, s p = ∑ᶠ j ∈ e.I p ∩ d.J (bsucc p), y j :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ι × ℕ → X, ∀ p, t p = ∑ᶠ j ∈ d.J (bsucc p) ∩ e.I (bsucc p), y j :=
    ⟨_, fun _ => rfl⟩
  -- (F1)
  have F1 : ∀ p : ι × ℕ, ∑ᶠ j ∈ d.J (bsucc p), y j = s p + t p := by
    intro p
    have hset := eq_union_inter_of_subset_union (h2 p)
    have hdisj : Disjoint (e.I p ∩ d.J (bsucc p)) (d.J (bsucc p) ∩ e.I (bsucc p)) :=
      (e.I_disjoint p (bsucc p) (hnesucc p)).mono Set.inter_subset_left Set.inter_subset_right
    rw [hs p, ht p, ← finsum_mem_union hdisj ((eIfin p).inter_of_left _)
      ((dJfin (bsucc p)).inter_of_left _), ← hset]
  -- (F2)
  have F2 : ∀ p : ι × ℕ, ∑ᶠ j ∈ e.I (bsucc p), y j = t p + s (bsucc p) := by
    intro p
    have hset := eq_union_inter_of_subset_union (h1 (bsucc p))
    have hdisj : Disjoint (d.J (bsucc p) ∩ e.I (bsucc p))
        (e.I (bsucc p) ∩ d.J (bsucc (bsucc p))) :=
      (d.J_disjoint (bsucc p) (bsucc (bsucc p)) (hnesucc (bsucc p))).mono
        Set.inter_subset_left Set.inter_subset_right
    rw [hs (bsucc p), ht p, ← finsum_mem_union hdisj ((dJfin (bsucc p)).inter_of_left _)
      ((eIfin (bsucc p)).inter_of_left _), ← hset]
  -- (F3)
  have F3 : ∀ a : ι, ∑ᶠ j ∈ e.I (a, 0), y j = (∑ᶠ j ∈ d.J (a, 0), y j) + s (a, 0) := by
    intro a
    have hset := eq_union_inter_of_subset_union' (h1 (a, 0)) (h3 a)
    have hdisj : Disjoint (d.J (a, 0)) (e.I (a, 0) ∩ d.J (bsucc (a, 0))) :=
      (d.J_disjoint (a, 0) (bsucc (a, 0)) (hnesucc (a, 0))).mono le_rfl Set.inter_subset_right
    rw [hs (a, 0), ← finsum_mem_union hdisj (dJfin (a, 0))
      ((eIfin (a, 0)).inter_of_left _), ← hset]
  -- the three basic identities
  have G1 : ∀ (a : ι) (n : ℕ), d.v (a, n + 2) + d.u (a, n + 1) = s (a, n) + t (a, n) := by
    intro a n
    exact (dJsum (bsucc (a, n))).symm.trans (F1 (a, n))
  have G2 : ∀ (a : ι) (n : ℕ), e.v (a, n + 1) + e.u (a, n + 1) = t (a, n) + s (a, n + 1) := by
    intro a n
    exact (eIsum (bsucc (a, n))).symm.trans (F2 (a, n))
  have G3 : ∀ a : ι, e.u (a, 0) = d.v (a, 1) + d.u (a, 0) + s (a, 0) := by
    intro a
    have h := (eIsum (a, 0)).symm.trans (F3 a)
    rw [e.v_limit a, zero_add, dJsum (a, 0)] at h
    exact h
  -- the merged braiding families
  obtain ⟨c, hc0, hc1⟩ : ∃ c : ι × ℕ → X, (∀ a : ι, c (a, 0) = d.u (a, 0)) ∧
      (∀ (a : ι) (l : ℕ), c (a, l + 1)
        = e.u (a, 3 * l + 1) + t (a, 3 * l + 1) + d.u (a, 3 * l + 3)) :=
    ⟨fun p => match p.2 with
      | 0 => d.u (p.1, 0)
      | l + 1 => e.u (p.1, 3 * l + 1) + t (p.1, 3 * l + 1) + d.u (p.1, 3 * l + 3),
      fun _ => rfl, fun _ _ => rfl⟩
  obtain ⟨w, hw0, hw1⟩ : ∃ w : ι × ℕ → X, (∀ a : ι, w (a, 0) = 0) ∧
      (∀ (a : ι) (l : ℕ), w (a, l + 1)
        = s (a, 3 * l) + e.v (a, 3 * l + 1) + d.v (a, 3 * l + 1)) :=
    ⟨fun p => match p.2 with
      | 0 => 0
      | l + 1 => s (p.1, 3 * l) + e.v (p.1, 3 * l + 1) + d.v (p.1, 3 * l + 1),
      fun _ => rfl, fun _ _ => rfl⟩
  refine ⟨BraidingData.mk_finsum (regroup d.I grp3) (regroup e.J grp3)
    (fun p => regroup_finite dIfin (grp3_finite p)) (fun p => regroup_finite eJfin (grp3_finite p))
    (fun p q hpq => regroup_disjoint d.I_disjoint grp3_disjoint hpq)
    (fun p q hpq => regroup_disjoint e.J_disjoint grp3_disjoint hpq)
    (regroup_cover d.I_cover grp3_cover) (regroup_cover e.J_cover grp3_cover) c w hw0 ?_ ?_⟩
  · -- `Σ_{M p} x = w p + c p`
    rintro ⟨a, n⟩
    rw [regroup_finsum d.I_disjoint dIfin (grp3_finite _) x]
    cases n with
    | zero =>
      rw [grp3_zero, finsum_mem_singleton, dIsum (a, 0), d.v_limit a, hw0 a, hc0 a, zero_add]
    | succ l =>
      rw [grp3_succ]
      simp only [dIsum]
      rw [finsum_mem_triple _ (pair_ne (by omega)) (pair_ne (by omega)) (pair_ne (by omega)),
        hw1 a l, hc1 a l]
      calc d.v (a, 3 * l + 1) + d.u (a, 3 * l + 1) + (d.v (a, 3 * l + 2) + d.u (a, 3 * l + 2))
              + (d.v (a, 3 * l + 3) + d.u (a, 3 * l + 3))
          = d.v (a, 3 * l + 1) + (d.v (a, 3 * l + 2) + d.u (a, 3 * l + 1))
              + (d.v (a, 3 * l + 3) + d.u (a, 3 * l + 2)) + d.u (a, 3 * l + 3) := by abel
        _ = d.v (a, 3 * l + 1) + (s (a, 3 * l) + t (a, 3 * l))
              + (s (a, 3 * l + 1) + t (a, 3 * l + 1)) + d.u (a, 3 * l + 3) := by
              rw [G1 a (3 * l), G1 a (3 * l + 1)]
        _ = s (a, 3 * l) + (e.v (a, 3 * l + 1) + e.u (a, 3 * l + 1)) + d.v (a, 3 * l + 1)
              + t (a, 3 * l + 1) + d.u (a, 3 * l + 3) := by rw [G2 a (3 * l)]; abel
        _ = s (a, 3 * l) + e.v (a, 3 * l + 1) + d.v (a, 3 * l + 1)
              + (e.u (a, 3 * l + 1) + t (a, 3 * l + 1) + d.u (a, 3 * l + 3)) := by abel
  · -- `Σ_{N p} z = w (p+1) + c p`
    rintro ⟨a, n⟩
    rw [regroup_finsum e.J_disjoint eJfin (grp3_finite _) z]
    show _ = w (a, n + 1) + c (a, n)
    cases n with
    | zero =>
      rw [grp3_zero, finsum_mem_singleton, eJsum (a, 0), hw1 a 0, hc0 a, G3 a]
      show e.v (a, 1) + (d.v (a, 1) + d.u (a, 0) + s (a, 0))
        = s (a, 0) + e.v (a, 0 + 1) + d.v (a, 0 + 1) + d.u (a, 0)
      abel
    | succ l =>
      rw [grp3_succ]
      simp only [eJsum]
      rw [finsum_mem_triple _ (pair_ne (by omega)) (pair_ne (by omega)) (pair_ne (by omega)),
        hw1 a (l + 1), hc1 a l]
      show e.v (a, 3 * l + 2) + e.u (a, 3 * l + 1) + (e.v (a, 3 * l + 3) + e.u (a, 3 * l + 2))
            + (e.v (a, 3 * l + 4) + e.u (a, 3 * l + 3))
          = s (a, 3 * l + 3) + e.v (a, 3 * l + 4) + d.v (a, 3 * l + 4)
            + (e.u (a, 3 * l + 1) + t (a, 3 * l + 1) + d.u (a, 3 * l + 3))
      calc e.v (a, 3 * l + 2) + e.u (a, 3 * l + 1) + (e.v (a, 3 * l + 3) + e.u (a, 3 * l + 2))
              + (e.v (a, 3 * l + 4) + e.u (a, 3 * l + 3))
          = e.u (a, 3 * l + 1) + (e.v (a, 3 * l + 2) + e.u (a, 3 * l + 2))
              + (e.v (a, 3 * l + 3) + e.u (a, 3 * l + 3)) + e.v (a, 3 * l + 4) := by abel
        _ = e.u (a, 3 * l + 1) + (t (a, 3 * l + 1) + s (a, 3 * l + 2))
              + (t (a, 3 * l + 2) + s (a, 3 * l + 3)) + e.v (a, 3 * l + 4) := by
              rw [G2 a (3 * l + 1), G2 a (3 * l + 2)]
        _ = s (a, 3 * l + 3) + e.v (a, 3 * l + 4) + (d.v (a, 3 * l + 4) + d.u (a, 3 * l + 3))
              + (e.u (a, 3 * l + 1) + t (a, 3 * l + 1)) := by rw [G1 a (3 * l + 2)]; abel
        _ = s (a, 3 * l + 3) + e.v (a, 3 * l + 4) + d.v (a, 3 * l + 4)
              + (e.u (a, 3 * l + 1) + t (a, 3 * l + 1) + d.u (a, 3 * l + 3)) := by abel

/-! ### Stage 1d of Lemma 3.7: regrouping a braiding along a family of position blocks -/

theorem mem_lep {S : Set (ι × ℕ)} {p : ι × ℕ} :
    p ∈ lep S ↔ p ∈ S ∧ ∀ q, bsucc q = p → q ∉ S := Iff.rfl

theorem mem_rep {S : Set (ι × ℕ)} {p : ι × ℕ} : p ∈ rep S ↔ p ∈ S ∧ bsucc p ∉ S := Iff.rfl

theorem lep_subset {S : Set (ι × ℕ)} : lep S ⊆ S := fun _ h => h.1

theorem rep_subset {S : Set (ι × ℕ)} : rep S ⊆ S := fun _ h => h.1

theorem bsucc_ne_self (p : ι × ℕ) : p ≠ bsucc p := fun hp =>
  Nat.succ_ne_self p.2 (congrArg Prod.snd hp).symm

/-- The image of `A ∖ rep A` under the successor map is `A ∖ lep A`. -/
theorem image_bsucc_diff_rep (A : Set (ι × ℕ)) : bsucc '' (A \ rep A) = A \ lep A := by
  apply Set.Subset.antisymm
  · rintro ρ ⟨ν, ⟨hν, hνrep⟩, rfl⟩
    have hbs : bsucc ν ∈ A := by
      by_contra hcon
      exact hνrep (mem_rep.mpr ⟨hν, hcon⟩)
    exact ⟨hbs, fun hlep => hlep.2 ν rfl hν⟩
  · rintro ρ ⟨hρ, hρlep⟩
    have hex : ∃ q, bsucc q = ρ ∧ q ∈ A := by
      by_contra hno
      exact hρlep (mem_lep.mpr ⟨hρ, fun q hq hqA => hno ⟨q, hq, hqA⟩⟩)
    obtain ⟨q, hq, hqA⟩ := hex
    refine ⟨q, ⟨hqA, fun hqrep => hqrep.2 ?_⟩, hq⟩
    rw [hq]; exact hρ

/-- Stage 1d of Lemma 3.7.  Given a braiding of `x` and `y` and a family `A` of finite sets of
positions that partitions the position set, is closed under the successor-linking condition
(`hsucc`) and left-saturated in the local sense (`hloc`), the `A`-regrouped partitions again
carry a braiding of `x` and `y`, with the braiding families given by the paper's formulas
`u_μ = Σ_{ν ∈ 𝒜_μ} a_ν + Σ_{ν ∈ 𝒜_μ ∖ lep 𝒜_μ} b_ν` and `v_μ = Σ_{ν ∈ lep 𝒜_μ} b_ν`. -/
theorem exists_repartition (d : BraidingData ℵ₀ x y) (A : ι × ℕ → Set (ι × ℕ))
    (hfin : ∀ μ, (A μ).Finite)
    (hdisj : ∀ μ ρ, μ ≠ ρ → Disjoint (A μ) (A ρ))
    (hcov : (⋃ μ, A μ) = Set.univ)
    (hsucc : ∀ μ, repSucc (A μ) ⊆ A (bsucc μ))
    (hloc : ∀ μ ν, bsucc ν ∈ A μ → ν ∉ A μ → ∃ ρ, μ = bsucc ρ ∧ ν ∈ rep (A ρ)) :
    ∃ e : BraidingData ℵ₀ x y,
      (∀ μ, e.I μ = regroup d.I A μ) ∧ (∀ μ, e.J μ = regroup d.J A μ) := by
  classical
  have dIfin : ∀ p, (d.I p).Finite := fun p => lt_aleph0_iff_set_finite.mp (d.I_small p)
  have dJfin : ∀ p, (d.J p).Finite := fun p => lt_aleph0_iff_set_finite.mp (d.J_small p)
  have dIsum : ∀ p, ∑ᶠ i ∈ d.I p, x i = d.v p + d.u p := fun p => by
    rw [← LMonoid.lsumOf_eq_finsum (d.I_small p)]; exact d.hI p
  have dJsum : ∀ p, ∑ᶠ j ∈ d.J p, y j = d.v (bsucc p) + d.u p := fun p => by
    rw [← LMonoid.lsumOf_eq_finsum (d.J_small p)]; exact d.hJ p
  -- `d.v` vanishes at every position with zero offset
  have hvzero : ∀ ν : ι × ℕ, ν.2 = 0 → d.v ν = 0 := by
    intro ν h2
    rw [show ν = (ν.1, 0) from Prod.ext_iff.mpr ⟨rfl, h2⟩]
    exact d.v_limit _
  -- the successors of right endpoints of `A μ` are exactly the non-limit left endpoints of
  -- `A (bsucc μ)`
  have K5a : ∀ μ, repSucc (A μ) ⊆ lep (A (bsucc μ)) := by
    rintro μ ρ ⟨ν, hν, rfl⟩
    refine mem_lep.mpr ⟨hsucc μ ⟨ν, hν, rfl⟩, ?_⟩
    intro q hq hqA
    rw [bsucc_injective hq] at hqA
    exact Set.disjoint_left.mp (hdisj μ (bsucc μ) (bsucc_ne_self μ)) hν.1 hqA
  have K5b : ∀ (μ : ι × ℕ) (ρ : ι × ℕ), ρ ∈ lep (A (bsucc μ)) → ρ.2 ≠ 0 →
      ρ ∈ repSucc (A μ) := by
    intro μ ρ hρ hρ2
    obtain ⟨b, n⟩ := ρ
    cases n with
    | zero => exact absurd rfl hρ2
    | succ m =>
      have hnot : (b, m) ∉ A (bsucc μ) := hρ.2 (b, m) rfl
      obtain ⟨σ, hσ, hνσ⟩ := hloc (bsucc μ) (b, m) hρ.1 hnot
      rw [← bsucc_injective hσ] at hνσ
      exact ⟨(b, m), hνσ, rfl⟩
  -- at limit positions all left endpoints are limit positions
  have K6 : ∀ (a : ι) (ν : ι × ℕ), ν ∈ lep (A (a, 0)) → ν.2 = 0 := by
    intro a ν hν
    by_contra hcon
    obtain ⟨b, n⟩ := ν
    cases n with
    | zero => exact hcon rfl
    | succ m =>
      obtain ⟨σ, hσ, -⟩ := hloc (a, 0) (b, m) hν.1 (hν.2 (b, m) rfl)
      exact absurd (congrArg Prod.snd hσ) (by simp [bsucc])
  -- the braiding families
  obtain ⟨v, hv⟩ : ∃ v : ι × ℕ → X, ∀ μ, v μ = ∑ᶠ ν ∈ lep (A μ), d.v ν := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ι × ℕ → X,
      ∀ μ, u μ = (∑ᶠ ν ∈ A μ, d.u ν) + ∑ᶠ ν ∈ A μ \ lep (A μ), d.v ν := ⟨_, fun _ => rfl⟩
  have hsplitv : ∀ μ, ∑ᶠ ν ∈ A μ, d.v ν = v μ + ∑ᶠ ν ∈ A μ \ lep (A μ), d.v ν := by
    intro μ
    rw [hv μ]
    exact finsum_mem_split d.v lep_subset (hfin μ)
  refine ⟨BraidingData.mk_finsum (regroup d.I A) (regroup d.J A)
    (fun p => regroup_finite dIfin (hfin p)) (fun p => regroup_finite dJfin (hfin p))
    (fun p q hpq => regroup_disjoint d.I_disjoint hdisj hpq)
    (fun p q hpq => regroup_disjoint d.J_disjoint hdisj hpq)
    (regroup_cover d.I_cover hcov) (regroup_cover d.J_cover hcov) u v ?_ ?_ ?_,
    fun _ => rfl, fun _ => rfl⟩
  · -- `v` vanishes at limit positions
    intro a
    rw [hv]
    exact finsum_mem_eq_zero_of_forall_eq_zero fun ν hν => hvzero ν (K6 a ν hν)
  · -- `Σ_{I μ} x = v μ + u μ`
    intro μ
    rw [regroup_finsum d.I_disjoint dIfin (hfin μ) x]
    simp only [dIsum]
    rw [finsum_mem_add_distrib (hfin μ), hsplitv μ, hu μ]
    abel
  · -- `Σ_{J μ} y = v (bsucc μ) + u μ`
    intro μ
    rw [regroup_finsum d.J_disjoint dJfin (hfin μ) y]
    simp only [dJsum]
    rw [finsum_mem_add_distrib (hfin μ)]
    have himg : ∑ᶠ ν ∈ A μ, d.v (bsucc ν) = ∑ᶠ ρ ∈ bsucc '' A μ, d.v ρ :=
      (finsum_mem_image bsucc_injective.injOn).symm
    have himgsplit : bsucc '' A μ = repSucc (A μ) ∪ (A μ \ lep (A μ)) := by
      rw [← image_bsucc_diff_rep (A μ), repSucc, ← Set.image_union,
        Set.union_sdiff_cancel rep_subset]
    have hdisjimg : Disjoint (repSucc (A μ)) (A μ \ lep (A μ)) := by
      rw [← image_bsucc_diff_rep (A μ), repSucc]
      refine Set.disjoint_image_of_injective bsucc_injective ?_
      rw [Set.disjoint_left]
      intro ν hν hν'
      exact hν'.2 hν
    have hrepfin : (repSucc (A μ)).Finite := (hfin μ).subset rep_subset |>.image _
    have hrep : ∑ᶠ ρ ∈ repSucc (A μ), d.v ρ = v (bsucc μ) := by
      rw [hv (bsucc μ)]
      refine (finsum_mem_eq_of_diff_eq_zero (K5a μ)
        ((hfin (bsucc μ)).subset lep_subset) ?_).symm
      intro ρ hρ
      refine hvzero ρ ?_
      by_contra hcon
      exact hρ.2 (K5b μ ρ hρ.1 hcon)
    rw [himg, himgsplit, finsum_mem_union hdisjimg hrepfin
      (((hfin μ).sdiff (t := lep (A μ)))), hrep, hu μ]
    abel

/-! ### Stage 1c of Lemma 3.7: the transfinite recursion

The recursion of Lemma 3.7 constructs, at each position `μ` of the limit well-order, a finite
set `𝒜_μ` of positions of the first braiding and a finite set `ℬ_μ` of positions of the second.
Both are built by the same mechanism: take the left-saturation closure (relative to the
positions already used) of a seed consisting of

* the positions needed to cover the residual indices (`C μ`),
* the successors of the right endpoints of the previous step (successor linking), and
* the position `μ` itself, if it has not been used yet (this forces exhaustion). -/

/-- The positions used strictly before `μ`. -/
def usedBefore (A : ι × ℕ → Set (ι × ℕ)) (μ : ι × ℕ) : Set (ι × ℕ) :=
  {ν | ∃ ρ, ∃ _ : kOrd ι ρ μ, ν ∈ A ρ}

/-- The positions added at the immediately preceding step (empty at limit positions). -/
def prevOf (A : ι × ℕ → Set (ι × ℕ)) (μ : ι × ℕ) : Set (ι × ℕ) :=
  if μ.2 = 0 then ∅ else A (μ.1, μ.2 - 1)

theorem mem_usedBefore {A : ι × ℕ → Set (ι × ℕ)} {μ ν : ι × ℕ} :
    ν ∈ usedBefore A μ ↔ ∃ ρ, kOrd ι ρ μ ∧ ν ∈ A ρ :=
  exists_congr fun _ => exists_prop

theorem mem_biUnion_iff {P : ι × ℕ → Set ι} {S : Set (ι × ℕ)} {i : ι} :
    i ∈ (⋃ ν ∈ S, P ν) ↔ ∃ ν ∈ S, i ∈ P ν := by
  simp only [Set.mem_iUnion, exists_prop]

theorem kOrd_irrefl {p : ι × ℕ} (h : kOrd ι p p) : False := kOrd_wf.asymmetric p p h h

theorem kOrd_trans {p q r : ι × ℕ} (h1 : kOrd ι p q) (h2 : kOrd ι q r) : kOrd ι p r :=
  _root_.trans h1 h2

theorem kOrd_pred {μ : ι × ℕ} (h : μ.2 ≠ 0) : kOrd ι (μ.1, μ.2 - 1) μ := by
  rw [kOrd_iff]
  exact Or.inr ⟨rfl, by omega⟩

theorem bsucc_prev {μ : ι × ℕ} (h : μ.2 ≠ 0) : bsucc (μ.1, μ.2 - 1) = μ := by
  obtain ⟨a, n⟩ := μ
  cases n with
  | zero => exact absurd rfl h
  | succ m => rfl

/-- Anything strictly below `bsucc μ` is either below `μ` or equal to `μ`. -/
theorem kOrd_lt_bsucc_iff {ρ μ : ι × ℕ} : kOrd ι ρ (bsucc μ) ↔ kOrd ι ρ μ ∨ ρ = μ := by
  constructor
  · intro h
    rcases trichotomous_of (kOrd ι) ρ μ with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd (kOrd_not_between h' h) not_false
  · rintro (h | rfl)
    · exact kOrd_trans h (kOrd_bsucc μ)
    · exact kOrd_bsucc ρ

theorem usedBefore_bsucc (A : ι × ℕ → Set (ι × ℕ)) (μ : ι × ℕ) :
    usedBefore A (bsucc μ) = usedBefore A μ ∪ A μ := by
  apply Set.Subset.antisymm
  · intro ν hν
    obtain ⟨ρ, hρ, hρA⟩ := mem_usedBefore.mp hν
    rcases kOrd_lt_bsucc_iff.mp hρ with h | rfl
    · exact Or.inl (mem_usedBefore.mpr ⟨ρ, h, hρA⟩)
    · exact Or.inr hρA
  · rintro ν (hν | hν)
    · obtain ⟨ρ, hρ, hρA⟩ := mem_usedBefore.mp hν
      exact mem_usedBefore.mpr ⟨ρ, kOrd_trans hρ (kOrd_bsucc μ), hρA⟩
    · exact mem_usedBefore.mpr ⟨μ, kOrd_bsucc μ, hν⟩

theorem usedBefore_mono {A : ι × ℕ → Set (ι × ℕ)} {ρ μ : ι × ℕ} (h : kOrd ι ρ μ) :
    usedBefore A ρ ⊆ usedBefore A μ := by
  intro ν hν
  obtain ⟨σ, hσ, hσA⟩ := mem_usedBefore.mp hν
  exact mem_usedBefore.mpr ⟨σ, kOrd_trans hσ h, hσA⟩

theorem subset_usedBefore {A : ι × ℕ → Set (ι × ℕ)} {ρ μ : ι × ℕ} (h : kOrd ι ρ μ) :
    A ρ ⊆ usedBefore A μ := fun _ hν => mem_usedBefore.mpr ⟨ρ, h, hν⟩

theorem prevOf_of_zero (A : ι × ℕ → Set (ι × ℕ)) {μ : ι × ℕ} (h : μ.2 = 0) :
    prevOf A μ = ∅ := by
  unfold prevOf; rw [if_pos h]

theorem prevOf_of_ne_zero (A : ι × ℕ → Set (ι × ℕ)) {μ : ι × ℕ} (h : μ.2 ≠ 0) :
    prevOf A μ = A (μ.1, μ.2 - 1) := by
  unfold prevOf; rw [if_neg h]

theorem prevOf_bsucc (A : ι × ℕ → Set (ι × ℕ)) (μ : ι × ℕ) : prevOf A (bsucc μ) = A μ := by
  rw [prevOf_of_ne_zero A (bsucc_snd_ne_zero μ)]
  congr 1

theorem prevOf_finite {A : ι × ℕ → Set (ι × ℕ)} {μ : ι × ℕ}
    (h : ∀ ρ, kOrd ι ρ μ → (A ρ).Finite) : (prevOf A μ).Finite := by
  by_cases hμ : μ.2 = 0
  · rw [prevOf_of_zero A hμ]; exact Set.finite_empty
  · rw [prevOf_of_ne_zero A hμ]; exact h _ (kOrd_pred hμ)

theorem biUnion_disjoint {P : ι × ℕ → Set ι} (hP : ∀ ν ρ, ν ≠ ρ → Disjoint (P ν) (P ρ))
    {S T : Set (ι × ℕ)} (hST : Disjoint S T) : Disjoint (⋃ ν ∈ S, P ν) (⋃ ν ∈ T, P ν) := by
  rw [Set.disjoint_left]
  intro i hi hj
  obtain ⟨ν, hν, hiν⟩ := mem_biUnion_iff.mp hi
  obtain ⟨ρ, hρ, hiρ⟩ := mem_biUnion_iff.mp hj
  have hνρ : ν = ρ := by
    by_contra hne
    exact Set.disjoint_left.mp (hP ν ρ hne) hiν hiρ
  subst hνρ
  exact Set.disjoint_left.mp hST hν hρ

/-- The shape of the families constructed by the recursion of Lemma 3.7. -/
structure IsSatRec (A C : ι × ℕ → Set (ι × ℕ)) : Prop where
  finite : ∀ μ, (A μ).Finite
  seed_disj : ∀ μ, Disjoint (C μ) (usedBefore A μ)
  eq : ∀ μ, A μ = satClosure (usedBefore A μ)
    (C μ ∪ repSucc (prevOf A μ) ∪ ({μ} \ usedBefore A μ))

namespace IsSatRec

variable {A C : ι × ℕ → Set (ι × ℕ)}

theorem seed_subset (h : IsSatRec A C) (μ : ι × ℕ) :
    C μ ∪ repSucc (prevOf A μ) ∪ ({μ} \ usedBefore A μ) ⊆ A μ := by
  rw [h.eq μ]; exact subset_satClosure _ _

theorem leftSat (h : IsSatRec A C) (μ : ι × ℕ) : LeftSaturated (A μ) (usedBefore A μ) := by
  rw [h.eq μ]; exact leftSaturated_satClosure _ _

theorem succ_subset (h : IsSatRec A C) (μ : ι × ℕ) : repSucc (A μ) ⊆ A (bsucc μ) := by
  refine subset_trans ?_ (h.seed_subset (bsucc μ))
  rw [prevOf_bsucc]
  exact fun p hp => Or.inl (Or.inr hp)

theorem cover (h : IsSatRec A C) : (⋃ μ, A μ) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ν
  by_cases hν : ν ∈ usedBefore A ν
  · obtain ⟨ρ, -, hρ⟩ := mem_usedBefore.mp hν
    exact Set.mem_iUnion.mpr ⟨ρ, hρ⟩
  · exact Set.mem_iUnion.mpr ⟨ν, h.seed_subset ν (Or.inr ⟨rfl, hν⟩)⟩

/-- Each step is disjoint from all earlier steps.  This is where the left-saturation invariant
is used: a successor `ν + 1` seeded into step `μ` because `ν` is a right endpoint of step `μ - 1`
cannot already have been used earlier, since an earlier step containing `ν + 1` would, by left
saturation, have had to contain `ν` as well. -/
theorem disj (h : IsSatRec A C) (μ : ι × ℕ) : Disjoint (A μ) (usedBefore A μ) := by
  refine kOrd_wf.induction (C := fun μ => Disjoint (A μ) (usedBefore A μ)) μ ?_
  clear μ
  intro μ IH
  have hpair : ∀ ρ σ, kOrd ι ρ μ → kOrd ι σ μ → ρ ≠ σ → Disjoint (A ρ) (A σ) := by
    intro ρ σ hρ hσ hne
    rcases trichotomous_of (kOrd ι) ρ σ with hlt | heq | hgt
    · exact ((IH σ hσ).mono_right (subset_usedBefore hlt)).symm
    · exact absurd heq hne
    · exact (IH ρ hρ).mono_right (subset_usedBefore hgt)
  rw [h.eq μ]
  refine satClosure_disjoint ?_
  rw [Set.disjoint_left]
  intro p hp hpU
  rcases hp with (hp | hp) | hp
  · exact Set.disjoint_left.mp (h.seed_disj μ) hp hpU
  · obtain ⟨ν, hν, rfl⟩ := hp
    have hμ2 : μ.2 ≠ 0 := by
      intro h0
      rw [prevOf_of_zero A h0] at hν
      exact Set.notMem_empty ν hν.1
    rw [prevOf_of_ne_zero A hμ2] at hν
    have hμ'μ : kOrd ι (μ.1, μ.2 - 1) μ := kOrd_pred hμ2
    obtain ⟨ρ, hρ, hρA⟩ := mem_usedBefore.mp hpU
    by_cases hcase : ρ = (μ.1, μ.2 - 1)
    · rw [hcase] at hρA; exact hν.2 hρA
    · have hνρ : ν ∈ usedBefore A ρ := by
        by_contra hcon
        exact Set.disjoint_left.mp (hpair ρ (μ.1, μ.2 - 1) hρ hμ'μ hcase)
          (h.leftSat ρ (bsucc ν) ν rfl hρA hcon) hν.1
      obtain ⟨σ, hσ, hσA⟩ := mem_usedBefore.mp hνρ
      have hσμ' : σ = (μ.1, μ.2 - 1) := by
        by_contra hcon
        exact Set.disjoint_left.mp (hpair σ (μ.1, μ.2 - 1) (kOrd_trans hσ hρ) hμ'μ hcon)
          hσA hν.1
      rw [hσμ'] at hσ
      exact kOrd_not_between hσ (by rw [bsucc_prev hμ2]; exact hρ)
  · exact hp.2 hpU

theorem pairwise (h : IsSatRec A C) (μ ρ : ι × ℕ) (hne : μ ≠ ρ) : Disjoint (A μ) (A ρ) := by
  rcases trichotomous_of (kOrd ι) μ ρ with hlt | heq | hgt
  · exact ((h.disj ρ).mono_right (subset_usedBefore hlt)).symm
  · exact absurd heq hne
  · exact (h.disj μ).mono_right (subset_usedBefore hgt)

/-- The local form of left saturation used in Stage 1d: if a successor position lies in step `μ`
but its predecessor does not, then `μ` is a successor step and the predecessor is a right
endpoint of the preceding step. -/
theorem loc (h : IsSatRec A C) (μ ν : ι × ℕ) (h1 : bsucc ν ∈ A μ) (h2 : ν ∉ A μ) :
    ∃ ρ, μ = bsucc ρ ∧ ν ∈ rep (A ρ) := by
  have hνU : ν ∈ usedBefore A μ := by
    by_contra hcon
    exact h2 (h.leftSat μ (bsucc ν) ν rfl h1 hcon)
  obtain ⟨ρ, hρ, hρA⟩ := mem_usedBefore.mp hνU
  have hμρ : μ ≠ ρ := fun heq => kOrd_irrefl (heq ▸ hρ)
  have hbne : bsucc ν ∉ A ρ := fun hmem =>
    Set.disjoint_left.mp (h.pairwise μ ρ hμρ) h1 hmem
  have hmemrep : ν ∈ rep (A ρ) := mem_rep.mpr ⟨hρA, hbne⟩
  refine ⟨ρ, ?_, hmemrep⟩
  by_contra hne
  exact Set.disjoint_left.mp (h.pairwise μ (bsucc ρ) hne) h1
    (h.succ_subset ρ ⟨ν, hmemrep, rfl⟩)

end IsSatRec

theorem biUnion_mono {P : ι × ℕ → Set ι} {S T : Set (ι × ℕ)} (h : S ⊆ T) :
    (⋃ ν ∈ S, P ν) ⊆ ⋃ ν ∈ T, P ν := by
  intro i hi
  obtain ⟨ν, hν, hiν⟩ := mem_biUnion_iff.mp hi
  exact Set.mem_biUnion (h hν) hiν

/-! #### The recursion itself -/

/-- One step of Lemma 3.7's recursion: given the values at all earlier positions, the sets of
positions added at `μ` on the two sides.  On the first side the seed covers the indices of the
previous step's `d₂.I`-piece that are not yet covered; on the second side it covers the indices
of the `d₁.J`-piece just constructed that are not yet covered.  Both seeds also contain the
successors of the previous step's right endpoints and the position `μ` itself, if unused. -/
noncomputable def transStep (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z)
    (μ : ι × ℕ) (F : ∀ ρ, kOrd ι ρ μ → Set (ι × ℕ) × Set (ι × ℕ)) :
    Set (ι × ℕ) × Set (ι × ℕ) :=
  let Ua : Set (ι × ℕ) := {ν | ∃ ρ, ∃ h : kOrd ι ρ μ, ν ∈ (F ρ h).1}
  let Ub : Set (ι × ℕ) := {ν | ∃ ρ, ∃ h : kOrd ι ρ μ, ν ∈ (F ρ h).2}
  let pA : Set (ι × ℕ) := if h : μ.2 = 0 then ∅ else (F (μ.1, μ.2 - 1) (kOrd_pred h)).1
  let pB : Set (ι × ℕ) := if h : μ.2 = 0 then ∅ else (F (μ.1, μ.2 - 1) (kOrd_pred h)).2
  let 𝒜 : Set (ι × ℕ) := satClosure Ua
    (blockOf d₁.J d₁.J_cover '' ((⋃ ν ∈ pB, d₂.I ν) \ (⋃ ν ∈ Ua, d₁.J ν))
      ∪ repSucc pA ∪ ({μ} \ Ua))
  (𝒜, satClosure Ub
    (blockOf d₂.I d₂.I_cover '' ((⋃ ν ∈ 𝒜, d₁.J ν) \ (⋃ ν ∈ Ub, d₂.I ν))
      ∪ repSucc pB ∪ ({μ} \ Ub)))

/-- The transfinite recursion of Lemma 3.7, run along the limit well-order `kOrd`. -/
noncomputable def transFam (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z) :
    ι × ℕ → Set (ι × ℕ) × Set (ι × ℕ) :=
  (kOrd_wf (ι := ι)).fix (transStep d₁ d₂)

/-- The positions of the first braiding used at step `μ` (the paper's `𝒜_μ`). -/
noncomputable def Afam (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z) (μ : ι × ℕ) :
    Set (ι × ℕ) := (transFam d₁ d₂ μ).1

/-- The positions of the second braiding used at step `μ` (the paper's `ℬ_μ`). -/
noncomputable def Bfam (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z) (μ : ι × ℕ) :
    Set (ι × ℕ) := (transFam d₁ d₂ μ).2

theorem transFam_eq (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z) (μ : ι × ℕ) :
    transFam d₁ d₂ μ = transStep d₁ d₂ μ (fun ρ _ => transFam d₁ d₂ ρ) :=
  WellFounded.fix_eq _ _ _

theorem Afam_eq (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z) (μ : ι × ℕ) :
    Afam d₁ d₂ μ = satClosure (usedBefore (Afam d₁ d₂) μ)
      (blockOf d₁.J d₁.J_cover '' ((⋃ ν ∈ prevOf (Bfam d₁ d₂) μ, d₂.I ν)
          \ (⋃ ν ∈ usedBefore (Afam d₁ d₂) μ, d₁.J ν))
        ∪ repSucc (prevOf (Afam d₁ d₂) μ) ∪ ({μ} \ usedBefore (Afam d₁ d₂) μ)) := by
  show (transFam d₁ d₂ μ).1 = _
  rw [transFam_eq]
  rfl

theorem Bfam_eq (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z) (μ : ι × ℕ) :
    Bfam d₁ d₂ μ = satClosure (usedBefore (Bfam d₁ d₂) μ)
      (blockOf d₂.I d₂.I_cover '' ((⋃ ν ∈ Afam d₁ d₂ μ, d₁.J ν)
          \ (⋃ ν ∈ usedBefore (Bfam d₁ d₂) μ, d₂.I ν))
        ∪ repSucc (prevOf (Bfam d₁ d₂) μ) ∪ ({μ} \ usedBefore (Bfam d₁ d₂) μ)) := by
  show (transFam d₁ d₂ μ).2 = _
  rw [transFam_eq, Afam_eq d₁ d₂ μ]
  rfl

/-- Both families are finite at every step; this is a simultaneous induction, since the seed on
the first side involves the previous step of the second family and vice versa. -/
theorem transFam_finite (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z) (μ : ι × ℕ) :
    (Afam d₁ d₂ μ).Finite ∧ (Bfam d₁ d₂ μ).Finite := by
  refine kOrd_wf.induction
    (C := fun μ => (Afam d₁ d₂ μ).Finite ∧ (Bfam d₁ d₂ μ).Finite) μ ?_
  clear μ
  intro μ IH
  have hd₁J : ∀ ν, (d₁.J ν).Finite := fun ν => lt_aleph0_iff_set_finite.mp (d₁.J_small ν)
  have hd₂I : ∀ ν, (d₂.I ν).Finite := fun ν => lt_aleph0_iff_set_finite.mp (d₂.I_small ν)
  have hpAfin : (prevOf (Afam d₁ d₂) μ).Finite := prevOf_finite fun ρ hρ => (IH ρ hρ).1
  have hpBfin : (prevOf (Bfam d₁ d₂) μ).Finite := prevOf_finite fun ρ hρ => (IH ρ hρ).2
  have hAfin : (Afam d₁ d₂ μ).Finite := by
    rw [Afam_eq]
    refine satClosure_finite (Set.Finite.union (Set.Finite.union ?_ ?_) ?_)
    · exact ((hpBfin.biUnion fun ν _ => hd₂I ν).subset Set.sdiff_subset).image _
    · exact (hpAfin.subset rep_subset).image _
    · exact (Set.finite_singleton μ).subset Set.sdiff_subset
  refine ⟨hAfin, ?_⟩
  rw [Bfam_eq]
  refine satClosure_finite (Set.Finite.union (Set.Finite.union ?_ ?_) ?_)
  · exact ((hAfin.biUnion fun ν _ => hd₁J ν).subset Set.sdiff_subset).image _
  · exact (hpBfin.subset rep_subset).image _
  · exact (Set.finite_singleton μ).subset Set.sdiff_subset

theorem isSatRec_A (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z) :
    IsSatRec (Afam d₁ d₂) (fun μ => blockOf d₁.J d₁.J_cover ''
      ((⋃ ν ∈ prevOf (Bfam d₁ d₂) μ, d₂.I ν)
        \ (⋃ ν ∈ usedBefore (Afam d₁ d₂) μ, d₁.J ν))) where
  finite := fun μ => (transFam_finite d₁ d₂ μ).1
  eq := Afam_eq d₁ d₂
  seed_disj := by
    intro μ
    rw [Set.disjoint_left]
    rintro p ⟨i, hi, rfl⟩ hpU
    exact hi.2 (Set.mem_biUnion hpU (mem_blockOf d₁.J d₁.J_cover i))

theorem isSatRec_B (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z) :
    IsSatRec (Bfam d₁ d₂) (fun μ => blockOf d₂.I d₂.I_cover ''
      ((⋃ ν ∈ Afam d₁ d₂ μ, d₁.J ν)
        \ (⋃ ν ∈ usedBefore (Bfam d₁ d₂) μ, d₂.I ν))) where
  finite := fun μ => (transFam_finite d₁ d₂ μ).2
  eq := Bfam_eq d₁ d₂
  seed_disj := by
    intro μ
    rw [Set.disjoint_left]
    rintro p ⟨i, hi, rfl⟩ hpU
    exact hi.2 (Set.mem_biUnion hpU (mem_blockOf d₂.I d₂.I_cover i))

/-! #### From the recursion to Lemma 3.7 -/

/-- The conclusion of Lemma 3.7, in the local form needed for Lemma 3.8, from the abstract
properties of the two families constructed by the recursion. -/
theorem aligned_of_isSatRec (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z)
    (A B CA CB : ι × ℕ → Set (ι × ℕ)) (hRA : IsSatRec A CA) (hRB : IsSatRec B CB)
    (hCA : ∀ μ, CA μ = blockOf d₁.J d₁.J_cover ''
      ((⋃ ν ∈ prevOf B μ, d₂.I ν) \ (⋃ ν ∈ usedBefore A μ, d₁.J ν)))
    (hCB : ∀ μ, CB μ = blockOf d₂.I d₂.I_cover ''
      ((⋃ ν ∈ A μ, d₁.J ν) \ (⋃ ν ∈ usedBefore B μ, d₂.I ν))) :
    ∃ (e₁ : BraidingData ℵ₀ x y) (e₂ : BraidingData ℵ₀ y z),
      (∀ p, e₂.I p ⊆ e₁.J p ∪ e₁.J (bsucc p)) ∧
      (∀ p, e₁.J (bsucc p) ⊆ e₂.I p ∪ e₂.I (bsucc p)) ∧
      (∀ a : ι, e₁.J (a, 0) ⊆ e₂.I (a, 0)) := by
  classical
  obtain ⟨e₁, he₁I, he₁J⟩ := exists_repartition d₁ A hRA.finite hRA.pairwise hRA.cover
    hRA.succ_subset hRA.loc
  obtain ⟨e₂, he₂I, he₂J⟩ := exists_repartition d₂ B hRB.finite hRB.pairwise hRB.cover
    hRB.succ_subset hRB.loc
  -- the covering properties built into the seeds
  have hcovA : ∀ μ, ((⋃ ν ∈ prevOf B μ, d₂.I ν) \ (⋃ ν ∈ usedBefore A μ, d₁.J ν))
      ⊆ ⋃ ν ∈ A μ, d₁.J ν := by
    intro μ i hi
    have hmem : blockOf d₁.J d₁.J_cover i ∈ A μ := by
      refine hRA.seed_subset μ (Or.inl (Or.inl ?_))
      rw [hCA μ]
      exact Set.mem_image_of_mem _ hi
    exact Set.mem_biUnion hmem (mem_blockOf d₁.J d₁.J_cover i)
  have hcovB : ∀ μ, ((⋃ ν ∈ A μ, d₁.J ν) \ (⋃ ν ∈ usedBefore B μ, d₂.I ν))
      ⊆ ⋃ ν ∈ B μ, d₂.I ν := by
    intro μ i hi
    have hmem : blockOf d₂.I d₂.I_cover i ∈ B μ := by
      refine hRB.seed_subset μ (Or.inl (Or.inl ?_))
      rw [hCB μ]
      exact Set.mem_image_of_mem _ hi
    exact Set.mem_biUnion hmem (mem_blockOf d₂.I d₂.I_cover i)
  -- each step's indices are disjoint from those of all earlier steps
  have hdA : ∀ μ, Disjoint (⋃ ν ∈ A μ, d₁.J ν) (⋃ ν ∈ usedBefore A μ, d₁.J ν) :=
    fun μ => biUnion_disjoint d₁.J_disjoint (hRA.disj μ)
  have hdB : ∀ μ, Disjoint (⋃ ν ∈ B μ, d₂.I ν) (⋃ ν ∈ usedBefore B μ, d₂.I ν) :=
    fun μ => biUnion_disjoint d₂.I_disjoint (hRB.disj μ)
  have hVA : ∀ μ, (⋃ ν ∈ usedBefore A (bsucc μ), d₁.J ν)
      = (⋃ ν ∈ usedBefore A μ, d₁.J ν) ∪ (⋃ ν ∈ A μ, d₁.J ν) := by
    intro μ; rw [usedBefore_bsucc]; exact Set.biUnion_union _ _ _
  have hVB : ∀ μ, (⋃ ν ∈ usedBefore B (bsucc μ), d₂.I ν)
      = (⋃ ν ∈ usedBefore B μ, d₂.I ν) ∪ (⋃ ν ∈ B μ, d₂.I ν) := by
    intro μ; rw [usedBefore_bsucc]; exact Set.biUnion_union _ _ _
  -- the two interleaving invariants
  have I1 : ∀ μ, (⋃ ν ∈ usedBefore A μ, d₁.J ν) ⊆ ⋃ ν ∈ usedBefore B μ, d₂.I ν := by
    intro μ i hi
    obtain ⟨ν, hν, hiν⟩ := mem_biUnion_iff.mp hi
    obtain ⟨ρ, hρ, hρA⟩ := mem_usedBefore.mp hν
    have hiJJ : i ∈ ⋃ σ ∈ A ρ, d₁.J σ := Set.mem_biUnion hρA hiν
    by_cases hc : i ∈ ⋃ σ ∈ usedBefore B ρ, d₂.I σ
    · exact biUnion_mono (usedBefore_mono hρ) hc
    · exact biUnion_mono (subset_usedBefore hρ) (hcovB ρ ⟨hiJJ, hc⟩)
  have I2 : ∀ μ, (⋃ ν ∈ usedBefore B μ, d₂.I ν)
      ⊆ (⋃ ν ∈ usedBefore A μ, d₁.J ν) ∪ (⋃ ν ∈ prevOf B μ, d₂.I ν) := by
    intro μ i hi
    obtain ⟨ν, hν, hiν⟩ := mem_biUnion_iff.mp hi
    obtain ⟨ρ, hρ, hρB⟩ := mem_usedBefore.mp hν
    by_cases hbs : kOrd ι (bsucc ρ) μ
    · have hiP : i ∈ ⋃ σ ∈ prevOf B (bsucc ρ), d₂.I σ := by
        rw [prevOf_bsucc]; exact Set.mem_biUnion hρB hiν
      by_cases hc : i ∈ ⋃ σ ∈ usedBefore A (bsucc ρ), d₁.J σ
      · exact Or.inl (biUnion_mono (usedBefore_mono hbs) hc)
      · exact Or.inl (biUnion_mono (subset_usedBefore hbs) (hcovA (bsucc ρ) ⟨hiP, hc⟩))
    · have hμ : μ = bsucc ρ := by
        rcases trichotomous_of (kOrd ι) (bsucc ρ) μ with h | h | h
        · exact absurd h hbs
        · exact h.symm
        · exact absurd (kOrd_not_between hρ h) not_false
      refine Or.inr ?_
      rw [hμ, prevOf_bsucc]
      exact Set.mem_biUnion hρB hiν
  refine ⟨e₁, e₂, ?_, ?_, ?_⟩
  · -- `J'_p ⊆ J_p ∪ J_{p+1}`
    intro p
    rw [he₂I p, he₁J p, he₁J (bsucc p)]
    intro i hi
    have hiP : i ∈ ⋃ σ ∈ prevOf B (bsucc p), d₂.I σ := by rw [prevOf_bsucc]; exact hi
    by_cases hc : i ∈ ⋃ σ ∈ usedBefore A (bsucc p), d₁.J σ
    · rw [hVA p] at hc
      rcases hc with hc | hc
      · exact absurd (I1 p hc) (Set.disjoint_left.mp (hdB p) hi)
      · exact Or.inl hc
    · exact Or.inr (hcovA (bsucc p) ⟨hiP, hc⟩)
  · -- `J_{p+1} ⊆ J'_p ∪ J'_{p+1}`
    intro p
    rw [he₁J (bsucc p), he₂I p, he₂I (bsucc p)]
    intro i hi
    by_cases hc : i ∈ ⋃ σ ∈ usedBefore B (bsucc p), d₂.I σ
    · rw [hVB p] at hc
      rcases hc with hc | hc
      · have hcontra : i ∈ ⋃ σ ∈ usedBefore A (bsucc p), d₁.J σ := by
          rw [hVA p]
          rcases I2 p hc with h | h
          · exact Or.inl h
          · by_cases hd : i ∈ ⋃ σ ∈ usedBefore A p, d₁.J σ
            · exact Or.inl hd
            · exact Or.inr (hcovA p ⟨h, hd⟩)
        exact absurd hcontra (Set.disjoint_left.mp (hdA (bsucc p)) hi)
      · exact Or.inl hc
    · exact Or.inr (hcovB (bsucc p) ⟨hi, hc⟩)
  · -- `J_μ ⊆ J'_μ` at limit positions
    intro a
    rw [he₁J (a, 0), he₂I (a, 0)]
    intro i hi
    by_cases hc : i ∈ ⋃ σ ∈ usedBefore B (a, 0), d₂.I σ
    · rcases I2 (a, 0) hc with h | h
      · exact absurd h (Set.disjoint_left.mp (hdA (a, 0)) hi)
      · rw [prevOf_of_zero B rfl] at h
        simp only [Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty] at h
    · exact hcovB (a, 0) ⟨hi, hc⟩

/-- Lemma 3.7 (`λ = ℵ₀`): two braidings sharing the middle family `y` can be replaced by
braidings whose partitions of `y` interleave block by block. -/
theorem exists_aligned (d₁ : BraidingData ℵ₀ x y) (d₂ : BraidingData ℵ₀ y z) :
    ∃ (e₁ : BraidingData ℵ₀ x y) (e₂ : BraidingData ℵ₀ y z),
      (∀ p, e₂.I p ⊆ e₁.J p ∪ e₁.J (bsucc p)) ∧
      (∀ p, e₁.J (bsucc p) ⊆ e₂.I p ∪ e₂.I (bsucc p)) ∧
      (∀ a : ι, e₁.J (a, 0) ⊆ e₂.I (a, 0)) :=
  aligned_of_isSatRec d₁ d₂ _ _ _ _ (isSatRec_A d₁ d₂) (isSatRec_B d₁ d₂)
    (fun _ => rfl) (fun _ => rfl)

/-- Transitivity of the braiding relation for `λ = ℵ₀` (Lemma 3.8). -/
theorem trans_aleph0 {x y z : ι → X} (hxy : IsBraided ℵ₀ x y) (hyz : IsBraided ℵ₀ y z) :
    IsBraided ℵ₀ x z := by
  obtain ⟨d₁⟩ := hxy
  obtain ⟨d₂⟩ := hyz
  obtain ⟨e₁, e₂, h1, h2, h3⟩ := exists_aligned d₁ d₂
  exact of_aligned e₁ e₂ h1 h2 h3


end TransAleph0

end IsBraided

/-! ## Lemma 3.2 and Lemma 3.4 -/

section Ambient

variable {lam κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]
  (hlam : lam.IsRegular) (hlk : lam ≤ κ)

/-- Lemma 3.2 (telescoping): braided families have equal `κ`-sums.

Note that the braiding is taken with respect to the `λ⁻`-monoid structure that `H` carries
as a `κ`-monoid (`KMonoid.toLMonoid`). -/
theorem sumOf_eq_of_isBraided {ι : Type u} (hι : #ι ≤ κ) (x y : ι → H)
    (h : letI := KMonoid.toLMonoidOfLE H hlam hlk; IsBraided lam x y) :
    sumOf (κ := κ) hι x = sumOf (κ := κ) hι y := by
  letI := KMonoid.toLMonoidOfLE H hlam hlk
  obtain ⟨d⟩ := h
  have hκ := KMonoid.aleph0_le (κ := κ) (H := H)
  have hP : #(ι × ℕ) ≤ κ := mk_prod_nat_le hκ hι
  have hIle : ∀ p, #(d.I p) ≤ κ := fun p => (d.I_small p).le.trans hlk
  have hJle : ∀ p, #(d.J p) ≤ κ := fun p => (d.J_small p).le.trans hlk
  -- Regroup each side along its braiding partition and use the defining equations.
  have hxsum : sumOf (κ := κ) hι x = sumOf (κ := κ) hP (fun p => d.v p + d.u p) := by
    rw [← sumOf_biUnion d.I d.I_disjoint d.I_cover hP hι hIle x]
    congr 1
    funext p
    exact (KMonoid.toLMonoidOfLE_lsumOf hlam hlk (d.I_small p)
      (fun i : d.I p => x i)).symm.trans (d.hI p)
  have hysum : sumOf (κ := κ) hι y = sumOf (κ := κ) hP (fun p => d.v (bsucc p) + d.u p) := by
    rw [← sumOf_biUnion d.J d.J_disjoint d.J_cover hP hι hJle y]
    congr 1
    funext p
    exact (KMonoid.toLMonoidOfLE_lsumOf hlam hlk (d.J_small p)
      (fun j : d.J p => y j)).symm.trans (d.hJ p)
  -- The telescoping step: `v` vanishes at the limit elements `(a, 0)`, and `bsucc` is a
  -- bijection onto the non-limit elements, so `Σ v = Σ (v ∘ bsucc)`.
  have hbs : d.v = Function.extend (bsucc (ι := ι)) (fun p => d.v (bsucc p)) 0 := by
    funext p
    obtain ⟨a, n⟩ := p
    cases n with
    | zero =>
      have hnr : ¬ ∃ q : ι × ℕ, bsucc q = (a, 0) := by
        rintro ⟨⟨b, m⟩, hbm⟩
        exact Nat.succ_ne_zero m (congrArg Prod.snd hbm)
      rw [Function.extend_apply' (fun p => d.v (bsucc p)) (0 : ι × ℕ → H) (a, 0) hnr]
      exact d.v_limit a
    | succ m =>
      have hmem : bsucc (a, m) = (a, m + 1) := rfl
      rw [← hmem, bsucc_injective.extend_apply]
  have hvtel : sumOf (κ := κ) hP d.v = sumOf (κ := κ) hP (fun p => d.v (bsucc p)) :=
    calc sumOf (κ := κ) hP d.v
        = sumOf (κ := κ) hP (Function.extend (bsucc (ι := ι)) (fun p => d.v (bsucc p)) 0) := by
          rw [← hbs]
      _ = sumOf (κ := κ) hP (fun p => d.v (bsucc p)) :=
          KMonoid.sumOf_extend hP hP ⟨bsucc, bsucc_injective⟩ _
  refine hxsum.trans (Eq.trans ?_ hysum.symm)
  calc sumOf (κ := κ) hP (fun p => d.v p + d.u p)
      = sumOf (κ := κ) hP d.v + sumOf (κ := κ) hP d.u := KMonoid.sumOf_add hP d.v d.u
    _ = sumOf (κ := κ) hP (fun p => d.v (bsucc p)) + sumOf (κ := κ) hP d.u := by rw [hvtel]
    _ = sumOf (κ := κ) hP (fun p => d.v (bsucc p) + d.u p) :=
        (KMonoid.sumOf_add hP (fun p => d.v (bsucc p)) d.u).symm

end Ambient

section Lemma34

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u}

/-- Lemma 3.4(1): families with support of size `< λ` and equal `λ⁻`-sums are braided.

Paper proof: let `I₀ = J₀` be a set of size `< λ` containing both supports, put the whole
sum there, and distribute the remaining indices arbitrarily among the other pieces.  In the
`ι × ℕ` normal form we can do the distributing explicitly: the leftover index `i` gets its
own piece at the slot `(i, 1)`. -/
theorem isBraided_of_small_support (x y : ι → X)
    (hx : #(Function.support x) < lam) (hy : #(Function.support y) < lam)
    (h : lsumOf (lam := lam) hx (fun i : Function.support x => x i)
        = lsumOf (lam := lam) hy (fun i : Function.support y => y i)) :
    IsBraided lam x y := by
  classical
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  rcases isEmpty_or_nonempty ι with hemp | hne
  · have hxy : x = y := funext fun i => (hemp.false i).elim
    subst hxy
    exact IsBraided.refl x
  obtain ⟨a₀⟩ := hne
  set S : Set ι := Function.support x ∪ Function.support y with hSdef
  have hS : #(S : Set ι) < lam := by
    rw [hSdef]
    exact lt_of_le_of_lt (Cardinal.mk_union_le _ _) (Cardinal.add_lt_of_lt hlam0 hx hy)
  have hxS : Function.support x ⊆ S := by rw [hSdef]; exact Set.subset_union_left
  have hyS : Function.support y ⊆ S := by rw [hSdef]; exact Set.subset_union_right
  have hx0 : ∀ i, i ∉ S → x i = 0 := fun i hi => by by_contra hc; exact hi (hxS hc)
  have hy0 : ∀ i, i ∉ S → y i = 0 := fun i hi => by by_contra hc; exact hi (hyS hc)
  -- One big piece carrying `S`, sitting at the limit slot `(a₀, 0)`; every leftover index
  -- `i ∉ S` gets the singleton piece `{i}` at the slot `(i, 1)`; all other slots are empty.
  set I : ι × ℕ → Set ι :=
    fun p => if p.2 = 0 then (if p.1 = a₀ then S else ∅)
      else if p.2 = 1 then {p.1} \ S else ∅ with hIdef
  have hIzero : ∀ a : ι, I (a, 0) = (if a = a₀ then S else ∅) := fun _ => rfl
  have hIone : ∀ a : ι, I (a, 1) = {a} \ S := fun _ => rfl
  have hItwo : ∀ (a : ι) (m : ℕ), I (a, m + 2) = ∅ := fun _ _ => rfl
  have hIa₀ : I (a₀, 0) = S := by rw [hIzero a₀, if_pos rfl]
  have hIne : ∀ a : ι, a ≠ a₀ → I (a, 0) = ∅ := fun a ha => by rw [hIzero a, if_neg ha]
  have hIsmall : ∀ p, #(I p) < lam := by
    rintro ⟨a, n⟩
    rcases n with _ | _ | m
    · by_cases ha : a = a₀
      · subst ha; rw [hIa₀]; exact hS
      · rw [hIne a ha, Cardinal.mk_eq_zero]; exact Cardinal.aleph0_pos.trans_le hlam0
    · rw [hIone a]
      refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset Set.sdiff_subset) ?_
      rw [Cardinal.mk_singleton]
      exact lt_of_lt_of_le one_lt_aleph0 hlam0
    · rw [hItwo a m, Cardinal.mk_eq_zero]; exact Cardinal.aleph0_pos.trans_le hlam0
  -- Membership analysis: a piece is either the big one, or the singleton belonging to its
  -- own index.
  have hmem : ∀ (p : ι × ℕ) (i : ι), i ∈ I p →
      (p = (a₀, 0) ∧ i ∈ S) ∨ (p = (i, 1) ∧ i ∉ S) := by
    rintro ⟨a, n⟩ i hi
    rcases n with _ | _ | m
    · by_cases ha : a = a₀
      · subst ha; rw [hIa₀] at hi; exact Or.inl ⟨rfl, hi⟩
      · rw [hIne a ha] at hi; exact absurd hi (by simp)
    · rw [hIone a] at hi
      obtain ⟨hia, hiS⟩ := hi
      have hai : i = a := hia
      subst hai
      exact Or.inr ⟨rfl, hiS⟩
    · rw [hItwo a m] at hi; exact absurd hi (by simp)
  have hout : ∀ (p : ι × ℕ), p ≠ (a₀, 0) → ∀ i ∈ I p, i ∉ S := by
    intro p hp i hi
    rcases hmem p i hi with ⟨hp', _⟩ | ⟨_, hiS⟩
    · exact absurd hp' hp
    · exact hiS
  have hIdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q) := by
    intro p q hpq
    rw [Set.disjoint_left]
    intro i hip hiq
    refine hpq ?_
    rcases hmem p i hip with ⟨hp, hpS⟩ | ⟨hp, hpS⟩ <;>
      rcases hmem q i hiq with ⟨hq, hqS⟩ | ⟨hq, hqS⟩
    · rw [hp, hq]
    · exact absurd hpS hqS
    · exact absurd hqS hpS
    · rw [hp, hq]
  have hIcover : (⋃ p, I p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    by_cases hi : i ∈ S
    · exact Set.mem_iUnion.mpr ⟨(a₀, 0), by rw [hIa₀]; exact hi⟩
    · exact Set.mem_iUnion.mpr ⟨(i, 1), by rw [hIone i]; exact ⟨rfl, hi⟩⟩
  refine IsBraided.of_partition I I hIdisj hIdisj hIcover hIcover hIsmall hIsmall ?_
  intro p
  by_cases hp : p = (a₀, 0)
  · subst hp
    rw [LMonoid.lsumOf_of_subset (hIsmall (a₀, 0)) hx (by rw [hIa₀]; exact hxS) x
        (fun i _ hi => by by_contra hc; exact hi hc),
      LMonoid.lsumOf_of_subset (hIsmall (a₀, 0)) hy (by rw [hIa₀]; exact hyS) y
        (fun i _ hi => by by_contra hc; exact hi hc)]
    exact h
  · rw [LMonoid.lsumOf_eq_zero (hIsmall p) x (fun i hi => hx0 i (hout p hp i hi)),
      LMonoid.lsumOf_eq_zero (hIsmall p) y (fun i hi => hy0 i (hout p hp i hi))]

/-- Within a single `ω`-block `a` of a braiding, the parts telescope so that the two
`λ⁻`-sums over the whole block already agree.  This is the content of Lemma 3.4(4) that
survives without needing the general alignment machinery of Lemma 3.7, once `λ` is
uncountable: restricting to one block never needs to compare positions coming from two
different blocks. -/
theorem BraidingData.block_lsumOf_eq {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X]
    {ι : Type u} {x y : ι → X} (d : BraidingData lam x y) (hlam0 : ℵ₀ < lam) (a : ι)
    (hI : #(⋃ n : ULift.{u} ℕ, d.I (a, n.down) : Set ι) < lam)
    (hJ : #(⋃ n : ULift.{u} ℕ, d.J (a, n.down) : Set ι) < lam) :
    lsumOf (lam := lam) hI (fun i : (⋃ n : ULift.{u} ℕ, d.I (a, n.down) : Set ι) => x i)
      = lsumOf (lam := lam) hJ (fun j : (⋃ n : ULift.{u} ℕ, d.J (a, n.down) : Set ι) => y j) := by
  set N := ULift.{u} ℕ with hNdef
  have hNlt : #N < lam := by
    rw [hNdef, Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact hlam0
  set bsuccU : N → N := fun n => ULift.up (n.down + 1) with hbsuccUdef
  have bsuccU_inj : Function.Injective bsuccU := by
    intro n m h
    have hnm : n.down + 1 = m.down + 1 := congrArg ULift.down h
    have hnm' : n.down = m.down := Nat.succ_injective hnm
    calc n = ULift.up n.down := rfl
      _ = ULift.up m.down := by rw [hnm']
      _ = m := rfl
  have hIdisj' : ∀ p q : N, p ≠ q → Disjoint (d.I (a, p.down)) (d.I (a, q.down)) := by
    intro p q hpq
    refine d.I_disjoint (a, p.down) (a, q.down) ?_
    intro h
    apply hpq
    have hd : p.down = q.down := congrArg Prod.snd h
    calc p = ULift.up p.down := rfl
      _ = ULift.up q.down := by rw [hd]
      _ = q := rfl
  have hJdisj' : ∀ p q : N, p ≠ q → Disjoint (d.J (a, p.down)) (d.J (a, q.down)) := by
    intro p q hpq
    refine d.J_disjoint (a, p.down) (a, q.down) ?_
    intro h
    apply hpq
    have hd : p.down = q.down := congrArg Prod.snd h
    calc p = ULift.up p.down := rfl
      _ = ULift.up q.down := by rw [hd]
      _ = q := rfl
  have step1 := (LMonoid.lsumOf_biUnion_subset (⋃ n : N, d.I (a, n.down))
    (fun n : N => d.I (a, n.down)) (fun n => Set.subset_iUnion (fun n : N => d.I (a, n.down)) n)
    hIdisj' rfl hNlt hI (fun n => d.I_small (a, n.down)) x).symm
  have step2 := (LMonoid.lsumOf_biUnion_subset (⋃ n : N, d.J (a, n.down))
    (fun n : N => d.J (a, n.down)) (fun n => Set.subset_iUnion (fun n : N => d.J (a, n.down)) n)
    hJdisj' rfl hNlt hJ (fun n => d.J_small (a, n.down)) y).symm
  rw [step1, step2]
  have hIeq : (fun n : N =>
      lsumOf (lam := lam) (d.I_small (a, n.down)) (fun i : d.I (a, n.down) => x i))
      = fun n : N => d.v (a, n.down) + d.u (a, n.down) := funext fun n => d.hI (a, n.down)
  have hJeq : (fun n : N =>
      lsumOf (lam := lam) (d.J_small (a, n.down)) (fun j : d.J (a, n.down) => y j))
      = fun n : N => d.v (a, n.down + 1) + d.u (a, n.down) := funext fun n => d.hJ (a, n.down)
  rw [hIeq, hJeq, LMonoid.lsumOf_add hNlt (fun n => d.v (a, n.down)) (fun n => d.u (a, n.down)),
    LMonoid.lsumOf_add hNlt (fun n => d.v (a, n.down + 1)) (fun n => d.u (a, n.down))]
  have hbs : (fun n : N => d.v (a, n.down))
      = Function.extend bsuccU (fun n : N => d.v (a, n.down + 1)) 0 := by
    funext n
    cases hcase : n.down with
    | zero =>
      have hnr : ¬ ∃ k : N, bsuccU k = n := by
        rintro ⟨k, hk⟩
        have hkd : k.down + 1 = n.down := congrArg ULift.down hk
        rw [hcase] at hkd
        exact Nat.succ_ne_zero k.down hkd
      rw [Function.extend_apply' (fun k : N => d.v (a, k.down + 1)) (0 : N → X) n hnr]
      exact d.v_limit a
    | succ m =>
      have hmem : bsuccU (ULift.up m) = n := by
        have hd : (bsuccU (ULift.up m)).down = n.down := by
          show m + 1 = n.down
          rw [hcase]
        calc bsuccU (ULift.up m) = ULift.up (bsuccU (ULift.up m)).down := rfl
          _ = ULift.up n.down := by rw [hd]
          _ = n := rfl
      rw [← hmem, bsuccU_inj.extend_apply]
  have hvtel : lsumOf (lam := lam) hNlt (fun n : N => d.v (a, n.down))
      = lsumOf (lam := lam) hNlt (fun n : N => d.v (a, n.down + 1)) := by
    rw [hbs]
    exact LMonoid.lsumOf_extend hNlt hNlt ⟨bsuccU, bsuccU_inj⟩ (fun n => d.v (a, n.down + 1))
  rw [hvtel]

/-- **Finite telescoping across a rectangle of blocks.**

Summing the two braiding equations over the levels `0, …, K` of finitely many `ω`-chains, the
`v`-terms cancel pairwise — `v (a, 0) = 0` shifts the two ranges onto each other — and only
`v (a, K+1)` survives:

    Σ_{a ∈ A} Σ_{k ≤ K} Σ_{J (a,k)} y = Σ_{a ∈ A} Σ_{k ≤ K} Σ_{I (a,k)} x + Σ_{a ∈ A} v (a, K+1).

This is the `λ = ℵ₀` counterpart of `block_lsumOf_eq`, which sums a whole chain at once and so
needs `λ` uncountable.  Lemma 5.2(4) uses it with `A` and `K` chosen to cover the finitely many
slots that carry the generator being tracked. -/
theorem BraidingData.telescope {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X]
    {ι : Type u} {x y : ι → X} (d : BraidingData lam x y) {A : Set ι} (hA : A.Finite) (K : ℕ) :
    (∑ᶠ a ∈ A, ∑ k ∈ Finset.range (K + 1),
        lsumOf (lam := lam) (d.J_small (a, k)) (fun j : d.J (a, k) => y j))
      = (∑ᶠ a ∈ A, ∑ k ∈ Finset.range (K + 1),
          lsumOf (lam := lam) (d.I_small (a, k)) (fun i : d.I (a, k) => x i))
        + ∑ᶠ a ∈ A, d.v (a, K + 1) := by
  have hchain : ∀ a : ι,
      (∑ k ∈ Finset.range (K + 1),
          lsumOf (lam := lam) (d.J_small (a, k)) (fun j : d.J (a, k) => y j))
        = (∑ k ∈ Finset.range (K + 1),
            lsumOf (lam := lam) (d.I_small (a, k)) (fun i : d.I (a, k) => x i))
          + d.v (a, K + 1) := by
    intro a
    have hI' : ∀ k : ℕ, lsumOf (lam := lam) (d.I_small (a, k)) (fun i : d.I (a, k) => x i)
        = d.v (a, k) + d.u (a, k) := fun k => d.hI (a, k)
    have hJ' : ∀ k : ℕ, lsumOf (lam := lam) (d.J_small (a, k)) (fun j : d.J (a, k) => y j)
        = d.v (a, k + 1) + d.u (a, k) := fun k => d.hJ (a, k)
    -- the shift of the `v`-range, by induction on `K`
    have hv : ∀ N : ℕ, (∑ k ∈ Finset.range (N + 1), d.v (a, k + 1))
        = (∑ k ∈ Finset.range (N + 1), d.v (a, k)) + d.v (a, N + 1) := by
      intro N
      induction N with
      | zero => simp [d.v_limit a]
      | succ P hP =>
        rw [Finset.sum_range_succ (fun k => d.v (a, k + 1)) (P + 1),
          Finset.sum_range_succ (fun k => d.v (a, k)) (P + 1), hP]
    rw [Finset.sum_congr rfl (fun k _ => hJ' k), Finset.sum_congr rfl (fun k _ => hI' k),
      Finset.sum_add_distrib, Finset.sum_add_distrib, hv K]
    abel
  rw [finsum_mem_congr rfl (fun a _ => hchain a), finsum_mem_add_distrib hA]

/-- Forward implication of Lemma 3.4(4) (uncountable-`λ` collapse of braiding data), used in
`isBraided_iff_of_ne_aleph0`. -/
theorem exists_partition_of_isBraided_of_ne_aleph0 {lam : Cardinal.{u}} {X : Type v}
    [LMonoid lam X] {ι : Type u} (hlam : lam ≠ ℵ₀) (x y : ι → X) :
    IsBraided lam x y →
      ∃ (I J : ι × ℕ → Set ι) (hI : ∀ p, #(I p) < lam) (hJ : ∀ p, #(J p) < lam),
        (∀ p q, p ≠ q → Disjoint (I p) (I q)) ∧ (∀ p q, p ≠ q → Disjoint (J p) (J q)) ∧
        (⋃ p, I p) = Set.univ ∧ (⋃ p, J p) = Set.univ ∧
        ∀ p, lsumOf (lam := lam) (hI p) (fun i : I p => x i)
            = lsumOf (lam := lam) (hJ p) (fun j : J p => y j) := by
  rintro ⟨d⟩
  have hlam0 : ℵ₀ < lam := lt_of_le_of_ne (LMonoid.aleph0_le (lam := lam) (X := X)) (Ne.symm hlam)
  classical
  set N := ULift.{u} ℕ with hNdef
  have hNlt : #N < lam := by
    rw [hNdef, Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact hlam0
  -- The new partition: at limit slots `(a, 0)` put the whole `ω`-block of `a`; all
  -- non-limit slots `(a, m+1)` are empty.
  set I : ι × ℕ → Set ι := fun p => if p.2 = 0 then ⋃ n : N, d.I (p.1, n.down) else ∅ with hIdef
  set J : ι × ℕ → Set ι := fun p => if p.2 = 0 then ⋃ n : N, d.J (p.1, n.down) else ∅ with hJdef
  have hIzero : ∀ a : ι, I (a, 0) = ⋃ n : N, d.I (a, n.down) := fun _ => rfl
  have hJzero : ∀ a : ι, J (a, 0) = ⋃ n : N, d.J (a, n.down) := fun _ => rfl
  have hInz : ∀ (a : ι) (m : ℕ), I (a, m + 1) = ∅ := fun _ _ => rfl
  have hJnz : ∀ (a : ι) (m : ℕ), J (a, m + 1) = ∅ := fun _ _ => rfl
  have hIsmall : ∀ p, #(I p) < lam := by
    rintro ⟨a, n⟩
    rcases n with _ | m
    · rw [hIzero a]
      exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular
        (‹LMonoid lam X›.isRegular) hNlt).mpr (fun n => d.I_small (a, n.down))
    · rw [hInz a m, Cardinal.mk_eq_zero]
      exact Cardinal.aleph0_pos.trans_le hlam0.le
  have hJsmall : ∀ p, #(J p) < lam := by
    rintro ⟨a, n⟩
    rcases n with _ | m
    · rw [hJzero a]
      exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular
        (‹LMonoid lam X›.isRegular) hNlt).mpr (fun n => d.J_small (a, n.down))
    · rw [hJnz a m, Cardinal.mk_eq_zero]
      exact Cardinal.aleph0_pos.trans_le hlam0.le
  have hIdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ hpq
    rcases n with _ | n <;> rcases m with _ | m
    · rw [hIzero a, hIzero b]
      have hab : a ≠ b := fun h => hpq (by rw [h])
      refine Set.disjoint_iUnion_left.mpr (fun n' => Set.disjoint_iUnion_right.mpr (fun m' => ?_))
      exact d.I_disjoint (a, n'.down) (b, m'.down) (fun h => hab (congrArg Prod.fst h))
    · rw [hIzero a, hInz b m]; simp
    · rw [hInz a n, hIzero b]; simp
    · rw [hInz a n, hInz b m]; simp
  have hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q) := by
    rintro ⟨a, n⟩ ⟨b, m⟩ hpq
    rcases n with _ | n <;> rcases m with _ | m
    · rw [hJzero a, hJzero b]
      have hab : a ≠ b := fun h => hpq (by rw [h])
      refine Set.disjoint_iUnion_left.mpr (fun n' => Set.disjoint_iUnion_right.mpr (fun m' => ?_))
      exact d.J_disjoint (a, n'.down) (b, m'.down) (fun h => hab (congrArg Prod.fst h))
    · rw [hJzero a, hJnz b m]; simp
    · rw [hJnz a n, hJzero b]; simp
    · rw [hJnz a n, hJnz b m]; simp
  have hIcover : (⋃ p, I p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    have hi : i ∈ (⋃ r, d.I r) := d.I_cover ▸ Set.mem_univ i
    obtain ⟨⟨a, n⟩, hia⟩ := Set.mem_iUnion.mp hi
    refine Set.mem_iUnion.mpr ⟨(a, 0), ?_⟩
    rw [hIzero a]
    exact Set.mem_iUnion.mpr ⟨ULift.up n, hia⟩
  have hJcover : (⋃ p, J p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    have hi : i ∈ (⋃ r, d.J r) := d.J_cover ▸ Set.mem_univ i
    obtain ⟨⟨a, n⟩, hia⟩ := Set.mem_iUnion.mp hi
    refine Set.mem_iUnion.mpr ⟨(a, 0), ?_⟩
    rw [hJzero a]
    exact Set.mem_iUnion.mpr ⟨ULift.up n, hia⟩
  refine ⟨I, J, hIsmall, hJsmall, hIdisj, hJdisj, hIcover, hJcover, ?_⟩
  rintro ⟨a, n⟩
  rcases n with _ | m
  · exact d.block_lsumOf_eq hlam0 a (hIsmall (a, 0)) (hJsmall (a, 0))
  · rw [LMonoid.lsumOf_eq_zero (hIsmall (a, m + 1)) x
        (fun i hi => by rw [hInz a m] at hi; exact hi.elim),
      LMonoid.lsumOf_eq_zero (hJsmall (a, m + 1)) y
        (fun j hj => by rw [hJnz a m] at hj; exact hj.elim)]

/-- Lemma 3.4(4): for uncountable `λ` the braiding relation collapses to the much simpler
condition that the two families admit partitions into pieces of size `< λ` with equal
partial sums. -/
theorem isBraided_iff_of_ne_aleph0 (hlam : lam ≠ ℵ₀) (x y : ι → X) :
    IsBraided lam x y ↔
      ∃ (I J : ι × ℕ → Set ι) (hI : ∀ p, #(I p) < lam) (hJ : ∀ p, #(J p) < lam),
        (∀ p q, p ≠ q → Disjoint (I p) (I q)) ∧ (∀ p q, p ≠ q → Disjoint (J p) (J q)) ∧
        (⋃ p, I p) = Set.univ ∧ (⋃ p, J p) = Set.univ ∧
        ∀ p, lsumOf (lam := lam) (hI p) (fun i : I p => x i)
            = lsumOf (lam := lam) (hJ p) (fun j : J p => y j) := by
  constructor
  · intro hxy
    -- This is Lemma 3.4(4), whose proof in the paper uses transitivity and alignment.
    exact exists_partition_of_isBraided_of_ne_aleph0 hlam x y hxy
  · rintro ⟨I, J, hI, hJ, hIdisj, hJdisj, hIcov, hJcov, heq⟩
    exact IsBraided.of_partition I J hIdisj hJdisj hIcov hJcov hI hJ heq

/-! ### Braiding partitions cut out by intervals of `ℕ`

Two generic facts used whenever a braiding is built by alternately growing intervals along two
families indexed by `ℕ` (Examples 3.3(1) for `ℕ₀`, Examples 3.3(2) for `ℝ≥0`). -/

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

/-! ### The converse of Lemma 3.4(1): braidedness preserves smallness of support

Reducedness makes a vanishing sum vanish termwise, and that turns the braiding equations into a
bound on the support of one family in terms of the support of the other.  This is what makes
"finite support" and "infinite support" incompatible under `ℵ₀⁻`-braiding, which the paper uses
repeatedly in Examples 3.3. -/

/-- In a reduced `λ⁻`-monoid a vanishing sum has vanishing terms: split off the term. -/
theorem eq_zero_of_lsumOf_eq_zero (hcon : IsConical X) {S : Set ι} (hS : #S < lam) (f : ι → X)
    (h : lsumOf (lam := lam) hS (fun i : S => f i) = 0) {i : ι} (hi : i ∈ S) : f i = 0 := by
  classical
  have hset : ({i} : Set ι) ∪ (S \ {i}) = S := by
    ext j
    by_cases hj : j = i <;> simp [hj, hi]
  have h1 : #({i} : Set ι) < lam :=
    LMonoid.mk_lt_finite (X := X) _
  have hT : #(↥(S \ {i})) < lam :=
    lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset Set.diff_subset) hS
  have hST : #(↥(({i} : Set ι) ∪ (S \ {i}))) < lam := by rw [hset]; exact hS
  have hcollapse : lsumOf (lam := lam) hST (fun j : ↥(({i} : Set ι) ∪ (S \ {i})) => f j)
      = lsumOf (lam := lam) hS (fun j : S => f j) :=
    LMonoid.lsumOf_of_subset hST hS (le_of_eq hset.symm) f fun j hj hnj =>
      absurd (hset ▸ hj) hnj
  have hsplit := LMonoid.lsumOf_union ({i} : Set ι) (S \ {i})
    (Set.disjoint_iff_inter_eq_empty.mpr (by simp)) h1 hT hST f
  rw [hcollapse, h] at hsplit
  haveI : Unique ({i} : Set ι) := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.2⟩
  have hdef : ((default : ({i} : Set ι)) : ι) = i := (default : ({i} : Set ι)).2
  have hsingle : lsumOf (lam := lam) h1 (fun j : ({i} : Set ι) => f j) = f i := by
    rw [LMonoid.lsumOf_unique h1 (fun j : ({i} : Set ι) => f j), hdef]
  rw [hsingle] at hsplit
  exact (hcon _ _ hsplit.symm).1

/-- **The converse of Lemma 3.4(1)**: in a reduced `λ⁻`-monoid, if `x` and `y` are `λ⁻`-braided
and the support of `x` has size `< λ`, then so does the support of `y`.

Proof: call a piece `I p` *active* if it meets the support of `x`; there are fewer than `λ` of
them, since the pieces are disjoint.  If a block `a` has no active piece from level `n` on, then
`Σ_{I (a,m)} x = 0` for all `m ≥ n`, so reducedness forces `u (a,m) = v (a,m) = 0` there, whence
`Σ_{J (a,n)} y = v (a,n+1) + u (a,n) = 0` and, again by reducedness, `y` vanishes on `J (a,n)`.
So the support of `y` is contained in the union of the `J p` over those `p = (a,n)` that lie at or
below an active level of their own block — fewer than `λ` many pieces, each of size `< λ`. -/
theorem IsBraided.mk_support_lt (hcon : IsConical X) {x y : ι → X} (h : IsBraided lam x y)
    (hx : #(Function.support x) < lam) : #(Function.support y) < lam := by
  classical
  obtain ⟨d⟩ := h
  have hlam : lam.IsRegular := ‹LMonoid lam X›.isRegular
  -- the pieces of the `x`-partition that meet the support of `x`
  set Bad : Set (ι × ℕ) := {p | ∃ i ∈ d.I p, x i ≠ 0} with hBaddef
  have hBad : #Bad < lam := by
    have hinj : ∃ f : Bad → Function.support x, Function.Injective f := by
      have hchoice : ∀ p : Bad, ∃ i : Function.support x, (i : ι) ∈ d.I p := by
        rintro ⟨p, i, hiI, hix⟩
        exact ⟨⟨i, hix⟩, hiI⟩
      choose f hf using hchoice
      refine ⟨f, fun p q hpq => ?_⟩
      by_contra hne
      have hd := Set.disjoint_left.mp (d.I_disjoint p q (fun hc => hne (Subtype.ext hc))) (hf p)
      exact hd (hpq ▸ hf q)
    obtain ⟨f, hf⟩ := hinj
    exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hf) hx
  -- the pairs at or below an active level of their own block
  set Low : Set (ι × ℕ) := {q | ∃ m, q.2 ≤ m ∧ (q.1, m) ∈ Bad} with hLowdef
  have hLow : #Low < lam := by
    have hsub : Low ⊆ ⋃ p : Bad, {q : ι × ℕ | q.1 = (p : ι × ℕ).1 ∧ q.2 ≤ (p : ι × ℕ).2} := by
      rintro ⟨a, n⟩ ⟨m, hnm, hm⟩
      exact Set.mem_iUnion.mpr ⟨⟨(a, m), hm⟩, rfl, hnm⟩
    refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hsub) ?_
    refine lt_of_le_of_lt Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_lt_of_isRegular hlam hBad fun p => ?_)
    -- each such set is finite: it is a copy of an initial segment of `ℕ`
    have hfin : {q : ι × ℕ | q.1 = (p : ι × ℕ).1 ∧ q.2 ≤ (p : ι × ℕ).2}.Finite := by
      refine Set.Finite.subset ((Set.finite_singleton (p : ι × ℕ).1).prod
        (Set.finite_Iic (p : ι × ℕ).2)) ?_
      rintro ⟨a, n⟩ ⟨ha, hn⟩
      exact ⟨ha, hn⟩
    haveI := hfin.to_subtype
    exact LMonoid.mk_lt_finite (X := X) _
  -- outside `Low`, the `y`-pieces carry nothing
  have hzero : ∀ p : ι × ℕ, p ∉ Low → ∀ j ∈ d.J p, y j = 0 := by
    intro p hp j hj
    have hIzero : ∀ m, p.2 ≤ m → lsumOf (lam := lam) (d.I_small (p.1, m))
        (fun i : d.I (p.1, m) => x i) = 0 := by
      intro m hm
      refine LMonoid.lsumOf_eq_zero _ x fun i hi => ?_
      by_contra hne
      exact hp ⟨m, hm, i, hi, hne⟩
    have huv : ∀ m, p.2 ≤ m → d.v (p.1, m) = 0 ∧ d.u (p.1, m) = 0 := by
      intro m hm
      have := (d.hI (p.1, m)).symm.trans (hIzero m hm)
      exact hcon _ _ this
    have hJsum : lsumOf (lam := lam) (d.J_small p) (fun j : d.J p => y j) = 0 := by
      rw [d.hJ p]
      show d.v (p.1, p.2 + 1) + d.u p = 0
      rw [(huv (p.2 + 1) (Nat.le_succ p.2)).1, (huv p.2 le_rfl).2, add_zero]
    exact eq_zero_of_lsumOf_eq_zero hcon (d.J_small p) y hJsum hj
  -- hence the support of `y` sits inside the `Low` pieces
  have hsupp : Function.support y ⊆ ⋃ p : Low, d.J (p : ι × ℕ) := by
    intro j hj
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (d.J_cover ▸ Set.mem_univ j)
    by_cases hpLow : p ∈ Low
    · exact Set.mem_iUnion.mpr ⟨⟨p, hpLow⟩, hp⟩
    · exact absurd (hzero p hpLow j hp) hj
  refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hsupp) ?_
  exact lt_of_le_of_lt Cardinal.mk_iUnion_le_sum_mk
    (Cardinal.sum_lt_of_isRegular hlam hLow fun p => d.J_small _)

end Lemma34

/-! ## Transitivity for uncountable `λ`

For `λ > ℵ₀` the whole alignment machinery of Lemma 3.7 can be bypassed.  As the user's
observation goes: for uncountable `λ` one may take as `λ⁻`-intervals the unions of fewer than `λ`
limit elements *together with all of their successors*, i.e. unions of full `ω`-blocks.  For such
an interval the braiding families telescope away completely (`BraidingData.block_lsumOf_eq`), so
braidedness collapses to the existence of two partitions into `< λ`-sized pieces with equal
partial sums — which is exactly Lemma 3.4(4), `isBraided_iff_of_ne_aleph0`, proved above.  What
remains is the purely combinatorial task of matching up two such partitions of the middle
family, which is done by passing to connected components. -/

section TransUncountable

open IsBraided (blockOf mem_blockOf mem_biUnion_iff)

/-! ## Components of a pair of partitions

For uncountable `λ`, Lemma 3.4(4) (`isBraided_iff_of_ne_aleph0`) already reduces braidedness to
the existence of partitions into `< λ`-sized pieces with equal partial sums.  Transitivity then
only needs a purely combinatorial statement: given two partitions `J`, `J'` of the index set of
the middle family, one can group the pieces of each so that the two groupings *cover the same
sets*.  The groups are the connected components of the relation "lie in a common piece of `J` or
in a common piece of `J'`"; since `λ` is regular and uncountable, each component is again of size
`< λ`, because it is built in countably many steps. -/

section Components

variable {ι : Type u} (J J' : ι × ℕ → Set ι)

/-- The union of all pieces of `J` and of `J'` containing `i`. -/
def nbhd (i : ι) : Set ι :=
  {j | (∃ p, i ∈ J p ∧ j ∈ J p) ∨ (∃ p, i ∈ J' p ∧ j ∈ J' p)}

theorem nbhd_symm {i j : ι} (h : j ∈ nbhd J J' i) : i ∈ nbhd J J' j := by
  rcases h with ⟨p, hi, hj⟩ | ⟨p, hi, hj⟩
  · exact Or.inl ⟨p, hj, hi⟩
  · exact Or.inr ⟨p, hj, hi⟩

theorem nbhd_subset {i : ι} {p q : ι × ℕ} (hp : i ∈ J p) (hq : i ∈ J' q)
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hJ'disj : ∀ p q, p ≠ q → Disjoint (J' p) (J' q)) :
    nbhd J J' i ⊆ J p ∪ J' q := by
  rintro j (⟨p', hi', hj'⟩ | ⟨q', hi', hj'⟩)
  · refine Or.inl ?_
    by_cases hpp : p' = p
    · exact hpp ▸ hj'
    · exact absurd hp (Set.disjoint_left.mp (hJdisj p' p hpp) hi')
  · refine Or.inr ?_
    by_cases hqq : q' = q
    · exact hqq ▸ hj'
    · exact absurd hq (Set.disjoint_left.mp (hJ'disj q' q hqq) hi')

/-- One step of the closure: all neighbours of all elements of `S`. -/
def cstep (S : Set ι) : Set ι := ⋃ i ∈ S, nbhd J J' i

theorem mem_cstep_iff {S : Set ι} {j : ι} : j ∈ cstep J J' S ↔ ∃ i ∈ S, j ∈ nbhd J J' i := by
  simp only [cstep, Set.mem_iUnion, exists_prop]

/-- The connected component of `i` for the relation "lie in a common piece of `J` or of `J'`". -/
def ccomp (i : ι) : Set ι := ⋃ n : ULift.{u} ℕ, (cstep J J')^[n.down] {i}

theorem cstep_iterate_subset_ccomp (n : ℕ) (i : ι) : (cstep J J')^[n] {i} ⊆ ccomp J J' i :=
  fun _ hj => Set.mem_iUnion.mpr ⟨ULift.up n, hj⟩

theorem self_mem_ccomp (i : ι) : i ∈ ccomp J J' i :=
  cstep_iterate_subset_ccomp J J' 0 i rfl

theorem cstep_ccomp_subset (i : ι) : cstep J J' (ccomp J J' i) ⊆ ccomp J J' i := by
  intro w hw
  obtain ⟨j, hj, hwj⟩ := (mem_cstep_iff J J').mp hw
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hj
  refine cstep_iterate_subset_ccomp J J' (n.down + 1) i ?_
  rw [Function.iterate_succ_apply']
  exact (mem_cstep_iff J J').mpr ⟨j, hn, hwj⟩

theorem nbhd_subset_ccomp {i j : ι} (h : j ∈ ccomp J J' i) : nbhd J J' j ⊆ ccomp J J' i :=
  fun _ hw => cstep_ccomp_subset J J' i ((mem_cstep_iff J J').mpr ⟨j, h, hw⟩)

theorem ccomp_subset_of_mem {i j : ι} (h : j ∈ ccomp J J' i) : ccomp J J' j ⊆ ccomp J J' i := by
  have key : ∀ m : ℕ, (cstep J J')^[m] {j} ⊆ ccomp J J' i := by
    intro m
    induction m with
    | zero =>
      intro w hw
      rw [Function.iterate_zero_apply] at hw
      exact (show w = j from hw) ▸ h
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      intro w hw
      obtain ⟨w', hw', hww⟩ := (mem_cstep_iff J J').mp hw
      exact nbhd_subset_ccomp J J' (ih hw') hww
  intro w hw
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
  exact key n.down hn

theorem mem_ccomp_symm_aux : ∀ (n : ℕ) (i j : ι), j ∈ (cstep J J')^[n] {i} → i ∈ ccomp J J' j := by
  intro n
  induction n with
  | zero =>
    intro i j hj
    rw [Function.iterate_zero_apply] at hj
    exact (show j = i from hj) ▸ self_mem_ccomp J J' j
  | succ k ih =>
    intro i j hj
    rw [Function.iterate_succ_apply'] at hj
    obtain ⟨j', hj', hjj⟩ := (mem_cstep_iff J J').mp hj
    have h2 : j' ∈ ccomp J J' j := by
      refine cstep_iterate_subset_ccomp J J' 1 j ?_
      rw [Function.iterate_one]
      exact (mem_cstep_iff J J').mpr ⟨j, rfl, nbhd_symm J J' hjj⟩
    exact ccomp_subset_of_mem J J' h2 (ih i j' hj')

theorem mem_ccomp_symm {i j : ι} (h : j ∈ ccomp J J' i) : i ∈ ccomp J J' j := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
  exact mem_ccomp_symm_aux J J' n.down i j hn

theorem ccomp_eq_of_mem {i j : ι} (h : j ∈ ccomp J J' i) : ccomp J J' j = ccomp J J' i :=
  Set.Subset.antisymm (ccomp_subset_of_mem J J' h)
    (ccomp_subset_of_mem J J' (mem_ccomp_symm J J' h))

/-- Two indices in a common piece of `J` lie in the same component. -/
theorem mem_ccomp_of_mem_same {p : ι × ℕ} {i j : ι} (hi : i ∈ J p) (hj : j ∈ J p) :
    i ∈ ccomp J J' j :=
  nbhd_subset_ccomp J J' (self_mem_ccomp J J' j) (Or.inl ⟨p, hj, hi⟩)

theorem mem_ccomp_of_mem_same' {p : ι × ℕ} {i j : ι} (hi : i ∈ J' p) (hj : j ∈ J' p) :
    i ∈ ccomp J J' j :=
  nbhd_subset_ccomp J J' (self_mem_ccomp J J' j) (Or.inr ⟨p, hj, hi⟩)

variable {lam : Cardinal.{u}}

theorem mk_nbhd_lt (hreg : lam.IsRegular)
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hJ'disj : ∀ p q, p ≠ q → Disjoint (J' p) (J' q))
    (hJcov : (⋃ p, J p) = Set.univ) (hJ'cov : (⋃ p, J' p) = Set.univ)
    (hJsm : ∀ p, #(J p) < lam) (hJ'sm : ∀ p, #(J' p) < lam) (i : ι) :
    #(nbhd J J' i) < lam := by
  refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset (nbhd_subset J J'
    (i := i) (p := blockOf J hJcov i) (q := blockOf J' hJ'cov i)
    (mem_blockOf J hJcov i) (mem_blockOf J' hJ'cov i) hJdisj hJ'disj)) ?_
  exact lt_of_le_of_lt (Cardinal.mk_union_le _ _)
    (Cardinal.add_lt_of_lt hreg.aleph0_le (hJsm _) (hJ'sm _))

theorem mk_cstep_lt (hreg : lam.IsRegular)
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hJ'disj : ∀ p q, p ≠ q → Disjoint (J' p) (J' q))
    (hJcov : (⋃ p, J p) = Set.univ) (hJ'cov : (⋃ p, J' p) = Set.univ)
    (hJsm : ∀ p, #(J p) < lam) (hJ'sm : ∀ p, #(J' p) < lam)
    {S : Set ι} (hS : #S < lam) : #(cstep J J' S) < lam := by
  have heq : cstep J J' S = ⋃ i : S, nbhd J J' (i : ι) := by
    rw [cstep, Set.biUnion_eq_iUnion]
  rw [heq]
  exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hreg hS).mpr
    fun i => mk_nbhd_lt J J' hreg hJdisj hJ'disj hJcov hJ'cov hJsm hJ'sm i

theorem mk_ccomp_lt (hreg : lam.IsRegular) (hlam0 : ℵ₀ < lam)
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hJ'disj : ∀ p q, p ≠ q → Disjoint (J' p) (J' q))
    (hJcov : (⋃ p, J p) = Set.univ) (hJ'cov : (⋃ p, J' p) = Set.univ)
    (hJsm : ∀ p, #(J p) < lam) (hJ'sm : ∀ p, #(J' p) < lam) (i : ι) :
    #(ccomp J J' i) < lam := by
  have hULift : #(ULift.{u} ℕ) < lam := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact hlam0
  have hstep : ∀ n : ℕ, #((cstep J J')^[n] {i}) < lam := by
    intro n
    induction n with
    | zero =>
      rw [Function.iterate_zero_apply, Cardinal.mk_singleton]
      exact lt_of_lt_of_le one_lt_aleph0 hreg.aleph0_le
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact mk_cstep_lt J J' hreg hJdisj hJ'disj hJcov hJ'cov hJsm hJ'sm ih
  rw [ccomp]
  exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hreg hULift).mpr fun n => hstep n.down

/-- A canonical representative of the component of `i`: its `WellOrderingRel`-least element. -/
noncomputable def crep (i : ι) : ι :=
  (IsWellFounded.wf (r := (WellOrderingRel : ι → ι → Prop))).min (ccomp J J' i)
    ⟨i, self_mem_ccomp J J' i⟩

theorem crep_mem (i : ι) : crep J J' i ∈ ccomp J J' i := WellFounded.min_mem _ _ _

theorem crep_eq_of_mem {i j : ι} (h : j ∈ ccomp J J' i) : crep J J' j = crep J J' i := by
  have hgen : ∀ (S T : Set ι) (hS : S.Nonempty) (hT : T.Nonempty), S = T →
      (IsWellFounded.wf (r := (WellOrderingRel : ι → ι → Prop))).min S hS
        = (IsWellFounded.wf (r := (WellOrderingRel : ι → ι → Prop))).min T hT := by
    intro S T hS hT hST
    subst hST
    rfl
  exact hgen _ _ _ _ (ccomp_eq_of_mem J J' h)

theorem mem_ccomp_of_crep_eq {i a : ι} (h : crep J J' i = a) : i ∈ ccomp J J' a :=
  mem_ccomp_symm J J' (h ▸ crep_mem J J' i)

end Components

/-! ## The common regrouping -/

section Regrouping

variable {ι : Type u} {lam : Cardinal.{u}}

theorem nat_split (k : ℕ) : k = 0 ∨ (∃ m, k = 2 * m + 1) ∨ (∃ m, k = 2 * m + 2) := by
  by_cases h0 : k = 0
  · exact Or.inl h0
  · rcases Nat.mod_two_eq_zero_or_one k with h | h
    · exact Or.inr (Or.inr ⟨(k - 2) / 2, by omega⟩)
    · exact Or.inr (Or.inl ⟨(k - 1) / 2, by omega⟩)

/-- The grouping of the pieces of a partition `J` along a map `r` that is constant on pieces: at
the slot `(a, 0)` all nonempty pieces whose `r`-value is `a`, at the slot `(a, 2m + c)` the piece
`(a, m)` if that piece is empty, and nothing elsewhere.

The offset `c` is `1` or `2`; using both values parks the empty pieces of two partitions at
disjoint sets of slots, which is what makes the two groupings of
`exists_common_regrouping` cover the same sets slot by slot. -/
def group (c : ℕ) (J : ι × ℕ → Set ι) (r : ι → ι) (μ : ι × ℕ) : Set (ι × ℕ) :=
  if μ.2 = 0 then {p | (J p).Nonempty ∧ ∀ i ∈ J p, r i = μ.1}
  else if μ.2 % 2 = c % 2 then (if J (μ.1, (μ.2 - c) / 2) = ∅ then {(μ.1, (μ.2 - c) / 2)} else ∅)
  else ∅

variable {c : ℕ} (J : ι × ℕ → Set ι) (r : ι → ι)

theorem group_zero (a : ι) :
    group c J r (a, 0) = {p | (J p).Nonempty ∧ ∀ i ∈ J p, r i = a} := by
  unfold group; rw [if_pos rfl]

theorem group_slot (hc : c = 1 ∨ c = 2) (a : ι) (m : ℕ) :
    group c J r (a, 2 * m + c) = if J (a, m) = ∅ then {(a, m)} else ∅ := by
  unfold group
  rcases hc with rfl | rfl <;>
    rw [if_neg (show ¬ (2 * m + _ : ℕ) = 0 by omega),
      if_pos (show (2 * m + _) % 2 = _ % 2 by omega),
      show (2 * m + _ - _) / 2 = m by omega]

theorem group_other (hc : c = 1 ∨ c = 2) (a : ι) (m : ℕ) :
    group c J r (a, 2 * m + (3 - c)) = ∅ := by
  unfold group
  rcases hc with rfl | rfl <;>
    rw [if_neg (show ¬ (2 * m + _ : ℕ) = 0 by omega),
      if_neg (show ¬ (2 * m + _) % 2 = _ % 2 by omega)]

/-- Every offset is either `0`, a `c`-slot or a `(3 - c)`-slot. -/
theorem nat_split_offset (hc : c = 1 ∨ c = 2) (k : ℕ) :
    k = 0 ∨ (∃ m, k = 2 * m + c) ∨ (∃ m, k = 2 * m + (3 - c)) := by
  rcases hc with rfl | rfl <;> rcases nat_split k with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨m, rfl⟩)
  · exact Or.inr (Or.inr ⟨m, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨m, rfl⟩)
  · exact Or.inr (Or.inl ⟨m, rfl⟩)

/-- The properties of `group c J r` that do not depend on `c`, proved once and used for both
offsets in `exists_common_regrouping`.  Only two things are needed of `r`: it is constant on the
pieces of `J`, and its fibres are small. -/
theorem group_spec (hreg : lam.IsRegular) (hc : c = 1 ∨ c = 2)
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q)) (hJcov : (⋃ p, J p) = Set.univ)
    (hrJ : ∀ (p : ι × ℕ) (i j : ι), i ∈ J p → j ∈ J p → r i = r j)
    (hrfib : ∀ a : ι, #{i | r i = a} < lam) :
    (∀ μ, #(group c J r μ) < lam) ∧ (∀ μ ν, μ ≠ ν → Disjoint (group c J r μ) (group c J r ν)) ∧
      (⋃ μ, group c J r μ) = Set.univ ∧
      (∀ a : ι, (⋃ p ∈ group c J r (a, 0), J p) = {i | r i = a}) ∧
      (∀ (a : ι) (k : ℕ), k ≠ 0 → (⋃ p ∈ group c J r (a, k), J p) = ∅) := by
  classical
  have hone : (1 : Cardinal.{u}) < lam := lt_of_lt_of_le one_lt_aleph0 hreg.aleph0_le
  have hzero : (0 : Cardinal.{u}) < lam := hone.trans_le' zero_le_one
  -- at a `c`-slot the group is a single empty piece, or nothing
  have hslot_empty : ∀ (a : ι) (k : ℕ), k ≠ 0 → ∀ p ∈ group c J r (a, k), J p = ∅ := by
    intro a k hk p hp
    rcases nat_split_offset hc k with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact absurd rfl hk
    · rw [group_slot J r hc a m] at hp
      by_cases hJa : J (a, m) = ∅
      · rw [if_pos hJa] at hp
        rwa [show p = (a, m) from hp]
      · rw [if_neg hJa] at hp; exact absurd hp (Set.notMem_empty p)
    · rw [group_other J r hc a m] at hp
      exact absurd hp (Set.notMem_empty p)
  refine ⟨?_, ?_, ?_, ?_, fun a k hk => ?_⟩
  · -- the groups are small
    rintro ⟨a, k⟩
    rcases nat_split_offset hc k with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [group_zero J r a]
      refine lt_of_le_of_lt (Cardinal.mk_le_of_injective
        (f := fun p : {p | (J p).Nonempty ∧ ∀ i ∈ J p, r i = a} =>
          (⟨p.2.1.some, p.2.2 _ p.2.1.some_mem⟩ : {i | r i = a})) ?_) (hrfib a)
      intro p q hpq
      have hval : p.2.1.some = q.2.1.some := congrArg Subtype.val hpq
      refine Subtype.ext ?_
      by_contra hne
      exact Set.disjoint_left.mp (hJdisj _ _ hne) p.2.1.some_mem (hval ▸ q.2.1.some_mem)
    · rw [group_slot J r hc a m]
      split
      · rw [Cardinal.mk_singleton]; exact hone
      · rw [Cardinal.mk_set_eq_zero_iff.mpr rfl]; exact hzero
    · rw [group_other J r hc a m, Cardinal.mk_set_eq_zero_iff.mpr rfl]; exact hzero
  · -- the groups are pairwise disjoint
    rintro ⟨a, k⟩ ⟨b, l⟩ hne
    rw [Set.disjoint_left]
    intro p hp hq
    -- a piece in a group at a nonzero slot is empty and determines the slot
    have key : ∀ (x : ι) (n : ℕ), n ≠ 0 → p ∈ group c J r (x, n) → x = p.1 ∧ n = 2 * p.2 + c := by
      intro x n hn hmem
      rcases nat_split_offset hc n with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact absurd rfl hn
      · rw [group_slot J r hc x m] at hmem
        by_cases hJx : J (x, m) = ∅
        · rw [if_pos hJx] at hmem
          rw [show p = (x, m) from hmem]
          exact ⟨rfl, rfl⟩
        · rw [if_neg hJx] at hmem; exact absurd hmem (Set.notMem_empty p)
      · rw [group_other J r hc x m] at hmem; exact absurd hmem (Set.notMem_empty p)
    by_cases hk : k = 0
    · subst hk
      by_cases hl : l = 0
      · subst hl
        rw [group_zero J r a] at hp
        rw [group_zero J r b] at hq
        obtain ⟨i, hi⟩ := hp.1
        exact hne (by rw [← hp.2 i hi, ← hq.2 i hi])
      · rw [group_zero J r a] at hp
        obtain ⟨i, hi⟩ := hp.1
        rw [hslot_empty b l hl p hq] at hi
        exact hi
    · obtain ⟨hx, hn⟩ := key a k hk hp
      by_cases hl : l = 0
      · subst hl
        rw [group_zero J r b] at hq
        obtain ⟨i, hi⟩ := hq.1
        rw [hslot_empty a k hk p hp] at hi
        exact hi
      · obtain ⟨hy, hm⟩ := key b l hl hq
        exact hne (by rw [Prod.ext_iff]; exact ⟨hx.trans hy.symm, hn.trans hm.symm⟩)
  · -- every piece lies in some group
    apply Set.eq_univ_of_forall
    rintro ⟨b, m⟩
    rcases Set.eq_empty_or_nonempty (J (b, m)) with hemp | ⟨i, hi⟩
    · refine Set.mem_iUnion.mpr ⟨(b, 2 * m + c), ?_⟩
      rw [group_slot J r hc b m, if_pos hemp]
      rfl
    · refine Set.mem_iUnion.mpr ⟨(r i, 0), ?_⟩
      rw [group_zero J r (r i)]
      exact ⟨⟨i, hi⟩, fun j hj => hrJ _ j i hj hi⟩
  · -- the group at a component slot covers exactly the fibre of `r`
    intro a
    apply Set.Subset.antisymm
    · intro i hi
      obtain ⟨p, hp, hip⟩ := mem_biUnion_iff.mp hi
      rw [group_zero J r a] at hp
      exact hp.2 i hip
    · intro i hi
      refine Set.mem_biUnion (show blockOf J hJcov i ∈ group c J r (a, 0) from ?_)
        (mem_blockOf J hJcov i)
      rw [group_zero J r a]
      exact ⟨⟨i, mem_blockOf J hJcov i⟩,
        fun j hj => (hrJ _ j i hj (mem_blockOf J hJcov i)).trans hi⟩
  · -- the groups at the remaining slots cover nothing
    apply Set.eq_empty_of_forall_notMem
    intro i hi
    obtain ⟨p, hp, hip⟩ := mem_biUnion_iff.mp hi
    rw [hslot_empty a k hk p hp] at hip
    exact hip

/-- The combinatorial core of transitivity for uncountable `λ`: two partitions `J`, `J'` of the
same index type can be grouped — into `< λ`-sized groups of pieces — in such a way that the two
groupings cover exactly the same sets.  The groups are the connected components of the relation
generated by the two partitions, together with one group for each piece that is empty (whose
group covers nothing, but which still has to be placed somewhere). -/
theorem exists_common_regrouping (hreg : lam.IsRegular) (hlam0 : ℵ₀ < lam)
    (J J' : ι × ℕ → Set ι)
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hJ'disj : ∀ p q, p ≠ q → Disjoint (J' p) (J' q))
    (hJcov : (⋃ p, J p) = Set.univ) (hJ'cov : (⋃ p, J' p) = Set.univ)
    (hJsm : ∀ p, #(J p) < lam) (hJ'sm : ∀ p, #(J' p) < lam) :
    ∃ GA GB : ι × ℕ → Set (ι × ℕ),
      (∀ μ, #(GA μ) < lam) ∧ (∀ μ, #(GB μ) < lam) ∧
      (∀ μ ν, μ ≠ ν → Disjoint (GA μ) (GA ν)) ∧ (∀ μ ν, μ ≠ ν → Disjoint (GB μ) (GB ν)) ∧
      (⋃ μ, GA μ) = Set.univ ∧ (⋃ μ, GB μ) = Set.univ ∧
      ∀ μ, (⋃ p ∈ GA μ, J p) = ⋃ p ∈ GB μ, J' p := by
  set r : ι → ι := crep J J' with hrdef
  -- `r` is constant on the pieces of either partition, and its fibres are small
  have hrJ : ∀ (p : ι × ℕ) (i j : ι), i ∈ J p → j ∈ J p → r i = r j := fun p i j hi hj =>
    crep_eq_of_mem J J' (mem_ccomp_of_mem_same J J' hi hj)
  have hrJ' : ∀ (p : ι × ℕ) (i j : ι), i ∈ J' p → j ∈ J' p → r i = r j := fun p i j hi hj =>
    crep_eq_of_mem J J' (mem_ccomp_of_mem_same' J J' hi hj)
  have hrfib : ∀ a : ι, #{i | r i = a} < lam := by
    intro a
    refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset ?_)
      (mk_ccomp_lt J J' hreg hlam0 hJdisj hJ'disj hJcov hJ'cov hJsm hJ'sm a)
    exact fun i hi => mem_ccomp_of_crep_eq J J' hi
  obtain ⟨hAsm, hAdisj, hAcov, hAfib, hAnil⟩ :=
    group_spec J r hreg (Or.inl rfl) hJdisj hJcov hrJ hrfib
  obtain ⟨hBsm, hBdisj, hBcov, hBfib, hBnil⟩ :=
    group_spec J' r hreg (Or.inr rfl) hJ'disj hJ'cov hrJ' hrfib
  refine ⟨group 1 J r, group 2 J' r, hAsm, hBsm, hAdisj, hBdisj, hAcov, hBcov, ?_⟩
  rintro ⟨a, k⟩
  by_cases hk : k = 0
  · subst hk; rw [hAfib a, hBfib a]
  · rw [hAnil a k hk, hBnil a k hk]

end Regrouping

/-! ## Transitivity for uncountable `λ` -/

section TransGeneral

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u}

theorem mk_regroup_lt (hreg : lam.IsRegular) {P : ι × ℕ → Set ι} {G : ι × ℕ → Set (ι × ℕ)}
    (hPsm : ∀ p, #(P p) < lam) {μ : ι × ℕ} (hG : #(G μ) < lam) : #(regroup P G μ) < lam := by
  have heq : regroup P G μ = ⋃ p : G μ, P (p : ι × ℕ) := by
    rw [regroup, Set.biUnion_eq_iUnion]
  rw [heq]
  exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular hreg hG).mpr fun p => hPsm _

/-- A `λ⁻`-sum over a regrouped piece is the sum of the sums over its parts. -/
theorem lsumOf_regroup {P : ι × ℕ → Set ι} {G : ι × ℕ → Set (ι × ℕ)}
    (hPdisj : ∀ p q, p ≠ q → Disjoint (P p) (P q)) (hPsm : ∀ p, #(P p) < lam)
    {μ : ι × ℕ} (hG : #(G μ) < lam) (hR : #(regroup P G μ) < lam) (f : ι → X) :
    lsumOf (lam := lam) hG
        (fun p : G μ => lsumOf (lam := lam) (hPsm (p : ι × ℕ)) (fun i : P (p : ι × ℕ) => f i))
      = lsumOf (lam := lam) hR (fun i : regroup P G μ => f i) := by
  refine LMonoid.lsumOf_biUnion_subset (regroup P G μ) (fun p : G μ => P (p : ι × ℕ))
    (fun p => Set.subset_biUnion_of_mem p.2) ?_ ?_ hG hR (fun p => hPsm _) f
  · intro p q hpq
    exact hPdisj _ _ fun h => hpq (Subtype.ext h)
  · rw [regroup, Set.biUnion_eq_iUnion]

/-- Transitivity of the braiding relation for uncountable `λ`.  By Lemma 3.4(4) both braidings
are given by partitions with equal partial sums; regrouping both along the components of the
two partitions of the middle family (`exists_common_regrouping`) makes the middle sums match up
piece by piece. -/
theorem IsBraided.trans_of_ne_aleph0 (hlam : lam ≠ ℵ₀) {x y z : ι → X}
    (hxy : IsBraided lam x y) (hyz : IsBraided lam y z) : IsBraided lam x z := by
  classical
  have hreg : lam.IsRegular := (‹LMonoid lam X›).isRegular
  have hlam0 : ℵ₀ < lam := lt_of_le_of_ne (LMonoid.aleph0_le (lam := lam) (X := X)) (Ne.symm hlam)
  obtain ⟨I, J, hIsm, hJsm, hIdisj, hJdisj, hIcov, hJcov, heq1⟩ :=
    (isBraided_iff_of_ne_aleph0 hlam x y).mp hxy
  obtain ⟨J', K, hJ'sm, hKsm, hJ'disj, hKdisj, hJ'cov, hKcov, heq2⟩ :=
    (isBraided_iff_of_ne_aleph0 hlam y z).mp hyz
  obtain ⟨GA, GB, hGAsm, hGBsm, hGAdisj, hGBdisj, hGAcov, hGBcov, hkey⟩ :=
    exists_common_regrouping hreg hlam0 J J' hJdisj hJ'disj hJcov hJ'cov hJsm hJ'sm
  have hMsm : ∀ μ, #(regroup I GA μ) < lam := fun μ => mk_regroup_lt hreg hIsm (hGAsm μ)
  have hNsm : ∀ μ, #(regroup K GB μ) < lam := fun μ => mk_regroup_lt hreg hKsm (hGBsm μ)
  have hYAsm : ∀ μ, #(regroup J GA μ) < lam := fun μ => mk_regroup_lt hreg hJsm (hGAsm μ)
  have hYBsm : ∀ μ, #(regroup J' GB μ) < lam := fun μ => mk_regroup_lt hreg hJ'sm (hGBsm μ)
  refine IsBraided.of_partition (regroup I GA) (regroup K GB)
    (fun p q h => regroup_disjoint hIdisj hGAdisj h)
    (fun p q h => regroup_disjoint hKdisj hGBdisj h)
    (regroup_cover hIcov hGAcov) (regroup_cover hKcov hGBcov) hMsm hNsm ?_
  intro μ
  have hmid : ∀ (S T : Set ι) (hS : #S < lam) (hT : #T < lam), S = T →
      lsumOf (lam := lam) hS (fun i : S => y i) = lsumOf (lam := lam) hT (fun i : T => y i) := by
    intro S T hS hT hST
    subst hST
    rfl
  calc lsumOf (lam := lam) (hMsm μ) (fun i : regroup I GA μ => x i)
      = lsumOf (lam := lam) (hGAsm μ)
          (fun p : GA μ => lsumOf (lam := lam) (hIsm _) (fun i : I (p : ι × ℕ) => x i)) :=
        (lsumOf_regroup hIdisj hIsm (hGAsm μ) (hMsm μ) x).symm
    _ = lsumOf (lam := lam) (hGAsm μ)
          (fun p : GA μ => lsumOf (lam := lam) (hJsm _) (fun j : J (p : ι × ℕ) => y j)) := by
        congr 1
        exact funext fun p => heq1 _
    _ = lsumOf (lam := lam) (hYAsm μ) (fun j : regroup J GA μ => y j) :=
        lsumOf_regroup hJdisj hJsm (hGAsm μ) (hYAsm μ) y
    _ = lsumOf (lam := lam) (hYBsm μ) (fun j : regroup J' GB μ => y j) :=
        hmid _ _ _ _ (hkey μ)
    _ = lsumOf (lam := lam) (hGBsm μ)
          (fun p : GB μ => lsumOf (lam := lam) (hJ'sm _) (fun j : J' (p : ι × ℕ) => y j)) :=
        (lsumOf_regroup hJ'disj hJ'sm (hGBsm μ) (hYBsm μ) y).symm
    _ = lsumOf (lam := lam) (hGBsm μ)
          (fun p : GB μ => lsumOf (lam := lam) (hKsm _) (fun k : K (p : ι × ℕ) => z k)) := by
        congr 1
        exact funext fun p => heq2 _
    _ = lsumOf (lam := lam) (hNsm μ) (fun k : regroup K GB μ => z k) :=
        lsumOf_regroup hKdisj hKsm (hGBsm μ) (hNsm μ) z

end TransGeneral

namespace IsBraided

/-- Combinatorial core of Lemma 3.8 (transitivity).  For `λ = ℵ₀` this is the alignment
construction of Lemma 3.7 followed by the merge of Lemma 3.8; for uncountable `λ` the much
shorter argument through Lemma 3.4(4) and connected components applies. -/
theorem trans_core {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u}
    {x y z : ι → X} : IsBraided lam x y → IsBraided lam y z → IsBraided lam x z := by
  intro hxy hyz
  by_cases hlam : lam = ℵ₀
  · subst hlam
    exact trans_aleph0 hxy hyz
  · exact IsBraided.trans_of_ne_aleph0 hlam hxy hyz

/-- Lemma 3.8, transitivity. -/
@[trans] theorem trans {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u}
    {x y z : ι → X} (hxy : IsBraided lam x y) (hyz : IsBraided lam y z) : IsBraided lam x z :=
  trans_core hxy hyz

end IsBraided

end TransUncountable

/-- Lemma 3.8: `λ⁻`-braidedness is an equivalence relation on `κ`-indexed families. -/
def braidingSetoid (lam κ : Cardinal.{u}) (X : Type v) [LMonoid lam X] :
    Setoid (Idx κ → X) where
  r := IsBraided lam
  iseqv := ⟨IsBraided.refl, IsBraided.symm, IsBraided.trans⟩

/-! ## Definition 3.1(2): `λ⁻`-braided extensions -/

/-- Definition 3.1(2): the `κ`-monoid `H` is `λ⁻`-braided over the `λ⁻`-monoid `X`,
embedded by `f`.  We ask that

* `f` is an injective `λ⁻`-homomorphism (so that `X` is a `λ⁻`-submonoid of `H`);
* `H` is generated by the image of `f` as a `κ`-monoid;
* any two `κ`-indexed families in `X` with equal `κ`-sum in `H` are `λ⁻`-braided. -/
structure IsBraidedOver (lam κ : Cardinal.{u}) (X : Type v) (H : Type w)
    [LMonoid lam X] [KMonoid κ H] (hlk : lam ≤ κ) (f : X → H) : Prop where
  isLHom : IsLHom hlk f
  injective : Function.Injective f
  generates : ∀ h : H, ∃ x : Idx κ → X, h = ksum (κ := κ) fun i => f (x i)
  braided : ∀ x y : Idx κ → X,
    (ksum (κ := κ) fun i => f (x i)) = (ksum (κ := κ) fun i => f (y i)) → IsBraided lam x y

end KappaMonoid
