/-
**Remark 3.9**: the common coarsening of two small partitions *is* the partition into the
connected components of the graph they generate.
-/
import KappaMonoid.Braiding.TransUncountable

universe u

open Cardinal Function Set

namespace KappaMonoid

/-! ## Remark 3.9: the components of a pair of partitions

`exists_common_coarsening` (Braiding/TransUncountable.lean) records only that a common coarsening
into pieces of size `< λ` *exists*.  The remark says more: consider the graph on the index set
joining `i` and `j` when `{i, j}` lies in a piece of `J` or of `J'`; the sets of the common
coarsening are the connected components of that graph.  This file states that version.

* `mem_ccomp_iff_reflTransGen`: `ccomp J J' i`, the closure of `{i}` under countably many
  neighbourhood steps, is the connected component of `i` in the paper's graph.
* `ccomp_subset_of_coarsening`: every partition coarsening both `J` and `J'` coarsens the
  components, so they form the *finest* common coarsening — which is what "the common coarsening"
  of the remark refers to.
* `remark_3_9`: for regular uncountable `λ` the components form a partition of the index set into
  pieces of size `< λ`, indexed by `ι × ℕ` as the braiding machinery expects; its nonempty pieces
  are exactly the components.

The indexing is the one of `exists_common_regrouping`: the component with canonical
representative `a` (`crep`) sits at slot `(a, 0)`, and every other slot is empty. -/

section Components

variable {ι : Type u} (J J' : ι × ℕ → Set ι)

/-- The edge relation of the graph of Remark 3.9: `i` and `j` lie in a common piece of `J` or of
`J'`. -/
def PartAdj (i j : ι) : Prop :=
  (∃ p, i ∈ J p ∧ j ∈ J p) ∨ (∃ p, i ∈ J' p ∧ j ∈ J' p)

/-- **Remark 3.9**: `ccomp J J' i` is the connected component of `i` in the graph joining two
indices that lie in a common piece of `J` or of `J'`. -/
theorem mem_ccomp_iff_reflTransGen {i j : ι} :
    j ∈ ccomp J J' i ↔ Relation.ReflTransGen (PartAdj J J') i j := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    -- every element reached in `n` steps is reachable in the graph
    have key : ∀ m : ℕ, ∀ w ∈ (cstep J J')^[m] {i}, Relation.ReflTransGen (PartAdj J J') i w := by
      intro m
      induction m with
      | zero =>
        intro w hw
        rw [Function.iterate_zero_apply] at hw
        rw [show w = i from hw]
      | succ k ih =>
        intro w hw
        rw [Function.iterate_succ_apply'] at hw
        obtain ⟨w', hw', hww⟩ := (mem_cstep_iff J J').mp hw
        exact (ih w' hw').tail hww
    exact key n.down j hn
  · intro h
    induction h with
    | refl => exact self_mem_ccomp J J' i
    | tail _ hbc ih => exact nbhd_subset_ccomp J J' ih hbc

/-- The components are the finest common coarsening: if every piece of `J` and of `J'` lies inside
a piece of a partition `Q`, then so does every component. -/
theorem ccomp_subset_of_coarsening {κ' : Type*} (Q : κ' → Set ι)
    (hQdisj : ∀ μ ν, μ ≠ ν → Disjoint (Q μ) (Q ν)) (hQcov : (⋃ μ, Q μ) = Set.univ)
    (hJQ : ∀ p, ∃ μ, J p ⊆ Q μ) (hJ'Q : ∀ p, ∃ μ, J' p ⊆ Q μ) (i : ι) :
    ∃ μ, ccomp J J' i ⊆ Q μ := by
  obtain ⟨μ, hμ⟩ := Set.mem_iUnion.mp (hQcov ▸ Set.mem_univ i)
  refine ⟨μ, fun j hj => ?_⟩
  -- an edge never leaves a piece of `Q`
  have hstep : ∀ a b, PartAdj J J' a b → a ∈ Q μ → b ∈ Q μ := by
    rintro a b (⟨p, ha, hb⟩ | ⟨p, ha, hb⟩) haQ
    · obtain ⟨ν, hν⟩ := hJQ p
      by_cases hνμ : ν = μ
      · exact hνμ ▸ hν hb
      · exact absurd haQ (Set.disjoint_left.mp (hQdisj ν μ hνμ) (hν ha))
    · obtain ⟨ν, hν⟩ := hJ'Q p
      by_cases hνμ : ν = μ
      · exact hνμ ▸ hν hb
      · exact absurd haQ (Set.disjoint_left.mp (hQdisj ν μ hνμ) (hν ha))
  have hrt := (mem_ccomp_iff_reflTransGen J J').mp hj
  clear hj
  induction hrt with
  | refl => exact hμ
  | tail _ hbc ih => exact hstep _ _ hbc ih

/-- The partition into components, indexed as the braiding machinery expects: the component with
canonical representative `a` sits at slot `(a, 0)`, and every other slot is empty. -/
def ccompPart (μ : ι × ℕ) : Set ι :=
  if μ.2 = 0 then {i | crep J J' i = μ.1} else ∅

theorem ccompPart_zero (a : ι) : ccompPart J J' (a, 0) = {i | crep J J' i = a} := by
  unfold ccompPart; rw [if_pos rfl]

theorem ccompPart_succ (a : ι) (k : ℕ) : ccompPart J J' (a, k + 1) = ∅ := by
  unfold ccompPart; rw [if_neg (Nat.succ_ne_zero k)]

/-- The fibre of `crep` through `i` is the component of `i`. -/
theorem setOf_crep_eq (i : ι) : {j | crep J J' j = crep J J' i} = ccomp J J' i := by
  ext j
  refine ⟨fun h => ?_, fun h => crep_eq_of_mem J J' h⟩
  rw [← ccomp_eq_of_mem J J' (crep_mem J J' i)]
  exact mem_ccomp_of_crep_eq J J' h

/-- Every nonempty piece of `ccompPart` is a component. -/
theorem ccompPart_eq_ccomp {μ : ι × ℕ} {i : ι} (hi : i ∈ ccompPart J J' μ) :
    ccompPart J J' μ = ccomp J J' i := by
  obtain ⟨a, k⟩ := μ
  cases k with
  | zero =>
    rw [ccompPart_zero] at hi ⊢
    rw [← setOf_crep_eq, show crep J J' i = a from hi]
  | succ k => rw [ccompPart_succ] at hi; exact absurd hi (Set.notMem_empty i)

/-- Every component is a piece of `ccompPart`. -/
theorem ccompPart_crep (i : ι) : ccompPart J J' (crep J J' i, 0) = ccomp J J' i := by
  rw [ccompPart_zero, setOf_crep_eq]

/-- **Remark 3.9**, with the components made explicit: for a regular *uncountable* `λ`, two
partitions `J`, `J'` of `ι` into pieces of cardinality `< λ` have a common coarsening `P` which is
again a partition into pieces of cardinality `< λ`, and the sets of `P` are *the connected
components* of the graph joining two indices lying in a common piece of `J` or of `J'`
(`mem_ccomp_iff_reflTransGen`): each nonempty piece of `P` is a component, and each component is a
piece of `P`.  By `ccomp_subset_of_coarsening` this is the finest common coarsening.

Paper proof: the components are closed under both partitions, so they coarsen both; each is the
union of the countably many iterates of "all neighbours of", every step taking a union of fewer
than `λ` pieces of size `< λ`, so regularity of the uncountable `λ` keeps it of size `< λ`
(`mk_ccomp_lt`).

This strengthens `exists_common_coarsening`, which only asserts that some such `P` exists. -/
theorem remark_3_9 {lam : Cardinal.{u}} (hreg : lam.IsRegular) (hlam0 : ℵ₀ < lam)
    (hJdisj : ∀ p q, p ≠ q → Disjoint (J p) (J q))
    (hJ'disj : ∀ p q, p ≠ q → Disjoint (J' p) (J' q))
    (hJcov : (⋃ p, J p) = Set.univ) (hJ'cov : (⋃ p, J' p) = Set.univ)
    (hJsm : ∀ p, #(J p) < lam) (hJ'sm : ∀ p, #(J' p) < lam) :
    ∃ P : ι × ℕ → Set ι,
      (∀ μ, #(P μ) < lam) ∧ (∀ μ ν, μ ≠ ν → Disjoint (P μ) (P ν)) ∧
      (⋃ μ, P μ) = Set.univ ∧
      (∀ p, ∃ μ, J p ⊆ P μ) ∧ (∀ p, ∃ μ, J' p ⊆ P μ) ∧
      (∀ μ, ∀ i ∈ P μ, P μ = ccomp J J' i) ∧ (∀ i, ∃ μ, P μ = ccomp J J' i) := by
  -- a piece of either partition lies in the component of any of its elements
  have hpiece : ∀ (K : ι × ℕ → Set ι),
      (∀ (p : ι × ℕ) (i j : ι), i ∈ K p → j ∈ K p → j ∈ ccomp J J' i) →
      ∀ p, ∃ μ, K p ⊆ ccompPart J J' μ := by
    intro K hK p
    rcases Set.eq_empty_or_nonempty (K p) with hemp | ⟨i, hi⟩
    · exact ⟨p, by rw [hemp]; exact Set.empty_subset _⟩
    · refine ⟨(crep J J' i, 0), ?_⟩
      rw [ccompPart_crep]
      exact fun j hj => hK p i j hi hj
  refine ⟨ccompPart J J', ?_, ?_, ?_,
    hpiece J fun p i j hi hj => mem_ccomp_of_mem_same J J' hj hi,
    hpiece J' fun p i j hi hj => mem_ccomp_of_mem_same' J J' hj hi,
    fun μ i hi => ccompPart_eq_ccomp J J' hi, fun i => ⟨_, ccompPart_crep J J' i⟩⟩
  · -- the pieces are small: each is empty or a component
    intro μ
    rcases Set.eq_empty_or_nonempty (ccompPart J J' μ) with hemp | ⟨i, hi⟩
    · rw [hemp, Cardinal.mk_set_eq_zero_iff.mpr rfl]
      exact lt_of_lt_of_le Cardinal.aleph0_pos hreg.aleph0_le
    · rw [ccompPart_eq_ccomp J J' hi]
      exact mk_ccomp_lt J J' hreg hlam0 hJdisj hJ'disj hJcov hJ'cov hJsm hJ'sm i
  · -- distinct slots carry disjoint pieces: distinct fibres of `crep`, or an empty slot
    intro μ ν hne
    rw [Set.disjoint_left]
    intro i hμ hν
    obtain ⟨a, k⟩ := μ
    obtain ⟨b, l⟩ := ν
    cases k with
    | succ k => rw [ccompPart_succ] at hμ; exact hμ
    | zero =>
      cases l with
      | succ l => rw [ccompPart_succ] at hν; exact hν
      | zero =>
        rw [ccompPart_zero] at hμ hν
        exact hne (by rw [← show crep J J' i = a from hμ, ← show crep J J' i = b from hν])
  · -- every index lies in the piece of its own representative
    exact Set.eq_univ_of_forall fun i =>
      Set.mem_iUnion.mpr ⟨(crep J J' i, 0), by rw [ccompPart_zero]; rfl⟩

end Components

end KappaMonoid
