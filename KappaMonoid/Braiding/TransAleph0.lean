/-
**Lemma 3.7** (repartition) and **Lemma 3.8** (transitivity) for `λ = ℵ₀`: the well-order
scaffolding, the left-saturation closure, and the transfinite recursion the paper's proof runs.
-/
import KappaMonoid.Braiding.Defs

universe u v w

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid

namespace IsBraided

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u}

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

end KappaMonoid
