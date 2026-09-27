/-
**Lemma 3.8** for uncountable `λ`, where the countable recursion is replaced by the common
regrouping of the components of a pair of partitions.
-/
import KappaMonoid.Braiding.Sums

universe u v w

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid


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

/-- **Remark 3.9**: for a regular *uncountable* `λ`, two partitions of `ι` into pieces of
cardinality `< λ` admit a **common coarsening** which is again a partition into pieces of
cardinality `< λ`.

This is the observation the remark makes.  Consider the graph on `ι` joining two indices when they
lie in a common piece of either partition; its connected components are `ccomp J J'`, they are the
pieces of the common coarsening, and regularity of the uncountable `λ` keeps them small
(`mk_ccomp_lt`), each being built in countably many steps out of pieces of size `< λ`.

It is what makes transitivity easy for `λ > ℵ₀` (`IsBraided.trans_of_ne_aleph0`): by Lemma 3.4(4)
(`isBraided_iff_of_ne_aleph0`) both braidings are given by partitions with equal partial sums, and
passing to the common coarsening of the two partitions of the middle family makes those sums match
up.  For `λ = ℵ₀` the argument breaks down — a component can be countably infinite — which is why
the countable case needs the alignment recursion of Lemma 3.7. -/
theorem exists_common_coarsening (hreg : lam.IsRegular) (hlam0 : ℵ₀ < lam)
    (J J' : ι × ℕ → Set ι)
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hJ'disj : ∀ p q, p ≠ q → Disjoint (J' p) (J' q))
    (hJcov : (⋃ p, J p) = Set.univ) (hJ'cov : (⋃ p, J' p) = Set.univ)
    (hJsm : ∀ p, #(J p) < lam) (hJ'sm : ∀ p, #(J' p) < lam) :
    ∃ P : ι × ℕ → Set ι,
      (∀ μ, #(P μ) < lam) ∧ (∀ μ ν, μ ≠ ν → Disjoint (P μ) (P ν)) ∧
      (⋃ μ, P μ) = Set.univ ∧
      (∀ p, ∃ μ, J p ⊆ P μ) ∧ (∀ p, ∃ μ, J' p ⊆ P μ) := by
  obtain ⟨GA, GB, hGAsm, hGBsm, hGAdisj, hGBdisj, hGAcov, hGBcov, hkey⟩ :=
    exists_common_regrouping hreg hlam0 J J' hJdisj hJ'disj hJcov hJ'cov hJsm hJ'sm
  refine ⟨regroup J GA, fun μ => mk_regroup_lt hreg hJsm (hGAsm μ),
    fun μ ν h => regroup_disjoint hJdisj hGAdisj h, regroup_cover hJcov hGAcov, ?_, ?_⟩
  · intro p
    obtain ⟨μ, hμ⟩ := Set.mem_iUnion.mp (hGAcov ▸ Set.mem_univ p)
    exact ⟨μ, Set.subset_biUnion_of_mem hμ⟩
  · intro p
    obtain ⟨μ, hμ⟩ := Set.mem_iUnion.mp (hGBcov ▸ Set.mem_univ p)
    refine ⟨μ, ?_⟩
    rw [show regroup J GA μ = regroup J' GB μ from hkey μ]
    exact Set.subset_biUnion_of_mem hμ

/-- A `λ⁻`-sum over a regrouped piece is the sum of the sums over its parts. -/

theorem lsumOf_regroup {P : ι × ℕ → Set ι} {G : ι × ℕ → Set (ι × ℕ)}
    (hPdisj : ∀ p q, p ≠ q → Disjoint (P p) (P q)) (hPsm : ∀ p, #(P p) < lam)
    {μ : ι × ℕ} (hG : #(G μ) < lam) (hR : #(regroup P G μ) < lam) (f : ι → X) :
    ∑[lam] p ∈ G μ, ∑[lam] i ∈ P (p : ι × ℕ), f i
      = lsumOf (lam := lam) hR (fun i : regroup P G μ => f i) := by
  refine LMonoid.lsumOf_biUnion_subset (hJ := ⟨hG⟩) (hS := ⟨hR⟩)
      (hI := fun _ => ⟨hPsm _⟩) (regroup P G μ) (fun p : G μ => P (p : ι × ℕ)) ?_ ?_ f
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
      ∑[lam] i ∈ S, y i = ∑[lam] i ∈ T, y i := by
    intro S T hS hT hST
    subst hST
    rfl
  calc ∑[lam] i ∈ regroup I GA μ, x i
      = ∑[lam] p ∈ GA μ, ∑[lam] i ∈ I (p : ι × ℕ), x i :=
        (lsumOf_regroup hIdisj hIsm (hGAsm μ) (hMsm μ) x).symm
    _ = ∑[lam] p ∈ GA μ, ∑[lam] j ∈ J (p : ι × ℕ), y j := by
        congr 1
        exact funext fun p => heq1 _
    _ = ∑[lam] j ∈ regroup J GA μ, y j :=
        lsumOf_regroup hJdisj hJsm (hGAsm μ) (hYAsm μ) y
    _ = lsumOf (lam := lam) (hYBsm μ) (fun j : regroup J' GB μ => y j) :=
        hmid _ _ _ _ (hkey μ)
    _ = ∑[lam] p ∈ GB μ, ∑[lam] j ∈ J' (p : ι × ℕ), y j :=
        (lsumOf_regroup hJ'disj hJ'sm (hGBsm μ) (hYBsm μ) y).symm
    _ = ∑[lam] p ∈ GB μ, ∑[lam] k ∈ K (p : ι × ℕ), z k := by
        congr 1
        exact funext fun p => heq2 _
    _ = lsumOf (lam := lam) (hNsm μ) (fun k : regroup K GB μ => z k) :=
        lsumOf_regroup hKdisj hKsm (hGBsm μ) (hNsm μ) z

namespace IsBraided

/-! ## Lemma 3.7 for every `λ`

For uncountable `λ` the regrouping above proves more than the paper's Lemma 3.7 asks for: the two
braidings can be chosen with *equal* partitions of the middle family, so the two cumulative unions
coincide instead of merely sandwiching one another.  Together with the `λ = ℵ₀` case
(`IsBraided.exists_aligned`, which really does need the alignment recursion) this gives Lemma 3.7
at every `λ`. -/

/-- **Lemma 3.7** for uncountable `λ`, in the sharp form: two braidings sharing the middle family
`y` can be replaced by braidings whose partitions of `y` are *equal*. -/
theorem exists_aligned_eq_of_ne_aleph0 (hlam : lam ≠ ℵ₀) {x y z : ι → X}
    (hxy : IsBraided lam x y) (hyz : IsBraided lam y z) :
    ∃ (e₁ : BraidingData lam x y) (e₂ : BraidingData lam y z), ∀ p, e₁.J p = e₂.I p := by
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
  -- the two regrouped braidings
  refine ⟨BraidingData.ofPartition (regroup I GA) (regroup J GA)
      (fun p q h => regroup_disjoint hIdisj hGAdisj h)
      (fun p q h => regroup_disjoint hJdisj hGAdisj h)
      (regroup_cover hIcov hGAcov) (regroup_cover hJcov hGAcov) hMsm hYAsm (fun μ => ?_),
    BraidingData.ofPartition (regroup J' GB) (regroup K GB)
      (fun p q h => regroup_disjoint hJ'disj hGBdisj h)
      (fun p q h => regroup_disjoint hKdisj hGBdisj h)
      (regroup_cover hJ'cov hGBcov) (regroup_cover hKcov hGBcov) hYBsm hNsm (fun μ => ?_),
    fun μ => hkey μ⟩
  · calc ∑[lam] i ∈ regroup I GA μ, x i
        = ∑[lam] p ∈ GA μ, ∑[lam] i ∈ I (p : ι × ℕ), x i :=
          (lsumOf_regroup hIdisj hIsm (hGAsm μ) (hMsm μ) x).symm
      _ = ∑[lam] p ∈ GA μ, ∑[lam] j ∈ J (p : ι × ℕ), y j := by
          congr 1
          exact funext fun p => heq1 _
      _ = ∑[lam] j ∈ regroup J GA μ, y j :=
          lsumOf_regroup hJdisj hJsm (hGAsm μ) (hYAsm μ) y
  · calc lsumOf (lam := lam) (hYBsm μ) (fun j : regroup J' GB μ => y j)
        = ∑[lam] p ∈ GB μ, ∑[lam] j ∈ J' (p : ι × ℕ), y j :=
          (lsumOf_regroup hJ'disj hJ'sm (hGBsm μ) (hYBsm μ) y).symm
      _ = lsumOf (lam := lam) (hGBsm μ)
            (fun p : GB μ => lsumOf (lam := lam) (hKsm _) (fun k : K (p : ι × ℕ) => z k)) := by
          congr 1
          exact funext fun p => heq2 _
      _ = lsumOf (lam := lam) (hNsm μ) (fun k : regroup K GB μ => z k) :=
          lsumOf_regroup hKdisj hKsm (hGBsm μ) (hNsm μ) z

/-- **Lemma 3.7**, at every `λ`, in the block-by-block form: two braidings sharing the middle
family `y` can be replaced by braidings whose partitions of `y` interleave block by block.  For
`λ = ℵ₀` this is `IsBraided.exists_aligned`, the paper's transfinite recursion; for uncountable
`λ` the partitions can even be taken equal. -/
theorem exists_aligned_of_data {x y z : ι → X}
    (d₁ : BraidingData lam x y) (d₂ : BraidingData lam y z) :
    ∃ (e₁ : BraidingData lam x y) (e₂ : BraidingData lam y z),
      (∀ p, e₂.I p ⊆ e₁.J p ∪ e₁.J (bsucc p)) ∧
      (∀ p, e₁.J (bsucc p) ⊆ e₂.I p ∪ e₂.I (bsucc p)) ∧
      (∀ a : ι, e₁.J (a, 0) ⊆ e₂.I (a, 0)) := by
  by_cases hlam : lam = ℵ₀
  · subst hlam
    exact exists_aligned d₁ d₂
  · obtain ⟨e₁, e₂, he⟩ := exists_aligned_eq_of_ne_aleph0 hlam ⟨d₁⟩ ⟨d₂⟩
    exact ⟨e₁, e₂, fun p => by rw [← he p]; exact Set.subset_union_left,
      fun p => by rw [he (bsucc p)]; exact Set.subset_union_right,
      fun a => by rw [he (a, 0)]⟩

/-- `bsucc` is strictly monotone for the limit well-order on `ι × ℕ`. -/
theorem kOrd_bsucc_mono {ν μ : ι × ℕ} (h : kOrd ι ν μ) : kOrd ι (bsucc ν) (bsucc μ) := by
  rw [kOrd_iff] at h ⊢
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, by simpa [bsucc] using h2⟩

/-- **Lemma 3.7**, for the normal-form limit well-order: with `(J_μ)` the partition of `y` in the first
braiding and `(J'_μ)` the one in the second,

    ⋃_{ν ≤ μ} J_ν ⊆ ⋃_{ν ≤ μ} J'_ν ⊆ ⋃_{ν ≤ μ+1} J_ν   for all μ.

Here the limit well-order is the lexicographic order `kOrd` on `ι × ℕ` (order type `ω · #ι`), whose
limit elements are the pairs `(a, 0)` and whose successor is `bsucc`.  This is the paper's statement
for that one order.  Lemma 3.5 (`Braiding/WellOrder.lean`) says that *whether* two families are
braided does not depend on the limit well-order; it does not transfer these particular aligned
partitions to another order, so the statement for an arbitrary limit well-order is not derived
from this one. -/
theorem exists_aligned_cumulative {x y z : ι → X}
    (d₁ : BraidingData lam x y) (d₂ : BraidingData lam y z) :
    ∃ (e₁ : BraidingData lam x y) (e₂ : BraidingData lam y z), ∀ μ : ι × ℕ,
      (⋃ ν ∈ {ν : ι × ℕ | kOrd ι ν μ ∨ ν = μ}, e₁.J ν)
          ⊆ (⋃ ν ∈ {ν : ι × ℕ | kOrd ι ν μ ∨ ν = μ}, e₂.I ν) ∧
        (⋃ ν ∈ {ν : ι × ℕ | kOrd ι ν μ ∨ ν = μ}, e₂.I ν)
          ⊆ ⋃ ν ∈ {ν : ι × ℕ | kOrd ι ν (bsucc μ) ∨ ν = bsucc μ}, e₁.J ν := by
  obtain ⟨e₁, e₂, h1, h2, h3⟩ := exists_aligned_of_data d₁ d₂
  refine ⟨e₁, e₂, fun μ => ⟨?_, ?_⟩⟩
  · -- `J_ν ⊆ J'_ν` at a limit `ν`, and `J_{ρ+1} ⊆ J'_ρ ∪ J'_{ρ+1}` at a successor
    intro i hi
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hi ⊢
    obtain ⟨ν, hνμ, hi⟩ := hi
    obtain ⟨a, (_ | n)⟩ := ν
    · exact ⟨(a, 0), hνμ, h3 a hi⟩
    · rcases h2 (a, n) (by simpa [bsucc] using hi) with h | h
      · exact ⟨(a, n), Or.inl (by
          rcases hνμ with hν | hν
          · exact kOrd_trans (kOrd_bsucc (a, n)) hν
          · exact hν ▸ kOrd_bsucc (a, n)), h⟩
      · exact ⟨(a, n + 1), hνμ, h⟩
  · -- `J'_ν ⊆ J_ν ∪ J_{ν+1}`, and both indices are `≤ μ+1`
    intro i hi
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hi ⊢
    obtain ⟨ν, hνμ, hi⟩ := hi
    have hνs : kOrd ι ν (bsucc μ) := by
      rcases hνμ with hν | hν
      · exact kOrd_trans hν (kOrd_bsucc μ)
      · exact hν ▸ kOrd_bsucc μ
    rcases h1 ν hi with h | h
    · exact ⟨ν, Or.inl hνs, h⟩
    · refine ⟨bsucc ν, ?_, h⟩
      rcases hνμ with hν | hν
      · exact Or.inl (kOrd_bsucc_mono hν)
      · exact Or.inr (by rw [hν])

end IsBraided

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

end KappaMonoid
