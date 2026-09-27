/-
**Lemma 3.5**: `λ⁻`-braidedness does not depend on the chosen limit well-order.

Definition 3.1(1) fixes a limit well-order on `κ` and indexes braiding partitions and braiding
families by `κ`, speaking of `μ + 1` and of limit elements.  `BraidingData` instead uses the
normal form `ι × ℕ`, with successor `(a, n) ↦ (a, n + 1)` and limit elements `(a, 0)`.  This file
shows the two agree, which is what licenses the normal form.

The bridge is `LimitSucc M`: the combinatorial content of a limit well-order on `M` — an injective
successor function whose image is exactly the set of non-limit elements, and whose iterates from
the limit elements exhaust `M`.  Every limit well-order gives one (`LimitSucc.ofWellOrder`), and
`ι × ℕ` carries the normal-form one (`LimitSucc.prodNat`).  `BraidingDataOn W x y` is
Definition 3.1(1) verbatim over such an index structure, and `BraidingData` is the case
`W = LimitSucc.prodNat ι`.

Everything then rests on one construction, `BraidingDataOn.comap`: braiding data may be pushed
along any map `Φ` of index structures that commutes with the successor, reflects limit elements
and has finite fibres, by taking unions and sums over the fibres.  Both directions of Lemma 3.5
are instances of it, and — unlike the paper's proof — neither needs to split on whether `λ` is
countable.
-/
import KappaMonoid.Braiding.Defs

universe u v

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid

/-! ## The index structure of Definition 3.1

A limit well-order is determined, as far as Definition 3.1 is concerned, by its successor function
and its set of limit elements. -/

/-- The combinatorial content of a **limit well-order** on `M`: a successor function `succ` whose
image is exactly the set of non-limit elements, injectively, and whose iterates starting from the
limit elements exhaust `M`.

This is all that Definition 3.1(1) uses of the well-order, and `LimitSucc.ofWellOrder` shows every
limit well-order — a well-order in which every element has a successor — provides it. -/
structure LimitSucc (M : Type u) where
  /-- The successor `μ ↦ μ + 1`. -/
  succ : M → M
  /-- The limit elements: those that are not successors (the minimum among them). -/
  IsLimit : M → Prop
  succ_injective : Function.Injective succ
  not_isLimit_succ : ∀ p, ¬ IsLimit (succ p)
  exists_pred : ∀ p, ¬ IsLimit p → ∃ q, succ q = p
  /-- Every element lies in the `ω`-block of a limit element. -/
  exists_isLimit_iterate : ∀ p, ∃ (l : M) (n : ℕ), IsLimit l ∧ succ^[n] l = p

namespace LimitSucc

variable {M : Type u} (W : LimitSucc M)

/-- The limit elements of `W`, as a type: the blocks of the `ω`-block decomposition. -/
abbrev Lim : Type u := {l : M // W.IsLimit l}

theorem iterate_injective (n : ℕ) : Function.Injective (W.succ^[n]) :=
  Function.Injective.iterate W.succ_injective n

theorem not_isLimit_iterate_succ (l : M) (n : ℕ) : ¬ W.IsLimit (W.succ^[n + 1] l) := by
  rw [Function.iterate_succ_apply']
  exact W.not_isLimit_succ _

/-- The `ω`-block decomposition is unique: an element determines its block and its offset. -/
theorem iterate_inj {l l' : M} {n n' : ℕ} (hl : W.IsLimit l) (hl' : W.IsLimit l')
    (h : W.succ^[n] l = W.succ^[n'] l') : l = l' ∧ n = n' := by
  -- reduce to the case `n ≤ n'` and peel off `n` successors
  suffices hkey : ∀ (m m' : ℕ) {a a' : M}, W.IsLimit a → W.IsLimit a' → m ≤ m' →
      W.succ^[m] a = W.succ^[m'] a' → a = a' ∧ m = m' by
    rcases le_total n n' with hle | hle
    · exact hkey n n' hl hl' hle h
    · obtain ⟨h1, h2⟩ := hkey n' n hl' hl hle h.symm
      exact ⟨h1.symm, h2.symm⟩
  intro m m' a a' ha ha' hmm hEq
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmm
  rw [Function.iterate_add_apply] at hEq
  have ha'' : a = W.succ^[d] a' := W.iterate_injective m hEq
  rcases d with _ | d
  · exact ⟨ha'', rfl⟩
  · exact absurd (ha'' ▸ ha) (W.not_isLimit_iterate_succ a' d)

/-- The `ω`-block decomposition of a limit well-order: every element is uniquely `l + n` for a
limit element `l` and a natural number `n`. -/
noncomputable def blockEquiv : W.Lim × ℕ ≃ M where
  toFun p := W.succ^[p.2] (p.1 : M)
  invFun p := ⟨⟨(W.exists_isLimit_iterate p).choose,
      (W.exists_isLimit_iterate p).choose_spec.choose_spec.1⟩,
    (W.exists_isLimit_iterate p).choose_spec.choose⟩
  left_inv := by
    rintro ⟨⟨l, hl⟩, n⟩
    obtain ⟨h1, h2⟩ := W.iterate_inj
      (W.exists_isLimit_iterate (W.succ^[n] l)).choose_spec.choose_spec.1 hl
      (W.exists_isLimit_iterate (W.succ^[n] l)).choose_spec.choose_spec.2
    exact Prod.ext (Subtype.ext h1) h2
  right_inv p := (W.exists_isLimit_iterate p).choose_spec.choose_spec.2

@[simp] theorem blockEquiv_apply (l : W.Lim) (n : ℕ) :
    W.blockEquiv (l, n) = W.succ^[n] (l : M) := rfl

theorem blockEquiv_succ (p : W.Lim × ℕ) :
    W.blockEquiv (p.1, p.2 + 1) = W.succ (W.blockEquiv p) :=
  Function.iterate_succ_apply' W.succ p.2 (p.1 : M)

theorem isLimit_blockEquiv_zero (l : W.Lim) : W.IsLimit (W.blockEquiv (l, 0)) := l.2

theorem blockEquiv_symm_snd_eq_zero {p : M} (hp : W.IsLimit p) :
    (W.blockEquiv.symm p).2 = 0 := by
  have h : W.succ^[(W.blockEquiv.symm p).2] ((W.blockEquiv.symm p).1 : M) = W.succ^[0] p := by
    rw [Function.iterate_zero_apply]
    exact W.blockEquiv.apply_symm_apply p
  exact (W.iterate_inj (W.blockEquiv.symm p).1.2 hp h).2

end LimitSucc

/-! ### Limit well-orders give index structures

A **limit well-order** on `ι` is a well-order in which every element has a successor, that is, one
with no maximum.  The successor of `a` is the least element above it, and the limit elements are
those that are not successors — the minimum among them, as the paper stipulates. -/

section WellOrder

variable {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] [NoMaxOrder ι]

/-- The successor in a limit well-order: the least element strictly above `a`. -/
noncomputable def wsucc (a : ι) : ι :=
  (IsWellFounded.wf (r := ((· < ·) : ι → ι → Prop))).min {b | a < b} (exists_gt a)

theorem lt_wsucc (a : ι) : a < wsucc a :=
  (IsWellFounded.wf (r := ((· < ·) : ι → ι → Prop))).min_mem {b | a < b} (exists_gt a)

theorem wsucc_le {a b : ι} (h : a < b) : wsucc a ≤ b :=
  not_lt.mp ((IsWellFounded.wf (r := ((· < ·) : ι → ι → Prop))).not_lt_min {c | a < c} h)

theorem wsucc_lt_wsucc {a b : ι} (h : a < b) : wsucc a < wsucc b :=
  lt_of_le_of_lt (wsucc_le h) (lt_wsucc b)

theorem wsucc_injective : Function.Injective (wsucc : ι → ι) := by
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (wsucc_lt_wsucc h).ne
  · exact h
  · exact absurd hab.symm (wsucc_lt_wsucc h).ne

/-- The limit elements of a limit well-order: those that are not successors.  The minimum is one,
since nothing lies below it. -/
def IsLimitElt (a : ι) : Prop := ∀ b, wsucc b ≠ a

theorem exists_limitElt_iterate (a : ι) :
    ∃ (l : ι) (n : ℕ), IsLimitElt l ∧ wsucc^[n] l = a := by
  refine (IsWellFounded.wf (r := ((· < ·) : ι → ι → Prop))).induction
    (C := fun a => ∃ (l : ι) (n : ℕ), IsLimitElt l ∧ wsucc^[n] l = a) a ?_
  intro a ih
  by_cases h : ∃ b, wsucc b = a
  · obtain ⟨b, rfl⟩ := h
    obtain ⟨l, n, hl, hn⟩ := ih b (lt_wsucc b)
    exact ⟨l, n + 1, hl, by rw [Function.iterate_succ_apply', hn]⟩
  · exact ⟨a, 0, not_exists.mp h, rfl⟩

/-- **Every limit well-order carries the index structure of Definition 3.1.** -/
noncomputable def LimitSucc.ofWellOrder (ι : Type u) [LinearOrder ι] [WellFoundedLT ι]
    [NoMaxOrder ι] : LimitSucc ι where
  succ := wsucc
  IsLimit := IsLimitElt
  succ_injective := wsucc_injective
  not_isLimit_succ p hp := hp p rfl
  exists_pred p hp := by
    simp only [IsLimitElt, not_forall, not_not] at hp
    exact hp
  exists_isLimit_iterate := exists_limitElt_iterate

end WellOrder


/-! ### Sanity check: `ℕ` under its usual order

`ℕ` is a limit well-order with a single block, so `wsucc` had better be `n + 1` and `0` had better
be its only limit element. -/

example : wsucc (3 : ℕ) = 4 := le_antisymm (wsucc_le (by norm_num)) (lt_wsucc 3)

example : IsLimitElt (0 : ℕ) := fun b h => absurd (h ▸ lt_wsucc b) (Nat.not_lt_zero b)

example : ¬ IsLimitElt (1 : ℕ) := fun h =>
  h 0 (le_antisymm (wsucc_le (by norm_num)) (lt_wsucc 0))


/-! ### The normal form `ι × ℕ` -/

theorem bsucc_iterate {ι : Type u} (a : ι) (n : ℕ) : bsucc^[n] (a, 0) = (a, n) := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- The index structure `BraidingData` is built on: `ι × ℕ` with successor `(a, n) ↦ (a, n + 1)`
and limit elements `(a, 0)`.  Every `ω`-block is a copy of `ℕ`, and there are `#ι` of them. -/
def LimitSucc.prodNat (ι : Type u) : LimitSucc (ι × ℕ) where
  succ := bsucc
  IsLimit p := p.2 = 0
  succ_injective := bsucc_injective
  not_isLimit_succ p := Nat.succ_ne_zero p.2
  exists_pred p hp := ⟨(p.1, p.2 - 1), by
    obtain ⟨a, n⟩ := p
    cases n with
    | zero => exact absurd rfl hp
    | succ m => rfl⟩
  exists_isLimit_iterate p := ⟨(p.1, 0), p.2, rfl, bsucc_iterate p.1 p.2⟩

/-! ## Definition 3.1(1) over an arbitrary index structure -/

/-- **Definition 3.1(1)**, with the index structure of the partitions taken as a parameter:
indexed partitions `I`, `J` of the index set into pieces of size `< λ`, and braiding families
`u`, `v` with `v` vanishing at the limit elements, such that

  `Σ_{i ∈ I μ} x i = v μ + u μ`   and   `Σ_{j ∈ J μ} y j = v (μ + 1) + u μ`.

`BraidingData` is the case `W = LimitSucc.prodNat ι` (`BraidingData.toOn`), and the paper's own
reading — partitions indexed by `κ` itself under a limit well-order — is the case
`W = LimitSucc.ofWellOrder ι`.  `isBraidedOn_iff_isBraided` (Lemma 3.5) says the two agree. -/
structure BraidingDataOn (lam : Cardinal.{u}) {X : Type v} [LMonoid lam X] {ι : Type u}
    {M : Type u} (W : LimitSucc M) (x y : ι → X) where
  I : M → Set ι
  J : M → Set ι
  I_disjoint : ∀ p q, p ≠ q → Disjoint (I p) (I q)
  J_disjoint : ∀ p q, p ≠ q → Disjoint (J p) (J q)
  I_cover : (⋃ p, I p) = Set.univ
  J_cover : (⋃ p, J p) = Set.univ
  I_small : ∀ p, #(I p) < lam
  J_small : ∀ p, #(J p) < lam
  u : M → X
  v : M → X
  /-- `v` vanishes at the limit elements of the well-order. -/
  v_limit : ∀ p, W.IsLimit p → v p = 0
  hI : ∀ p, ∑[lam] i ∈ I p, x i = v p + u p
  hJ : ∀ p, ∑[lam] j ∈ J p, y j = v (W.succ p) + u p

attribute [lam_small_rule] BraidingDataOn.I_small BraidingDataOn.J_small

/-- `x` and `y` are `λ⁻`-braided with respect to the index structure `W`. -/
def IsBraidedOn (lam : Cardinal.{u}) {X : Type v} [LMonoid lam X] {ι : Type u}
    {M : Type u} (W : LimitSucc M) (x y : ι → X) : Prop :=
  Nonempty (BraidingDataOn lam W x y)

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u} {x y : ι → X}

/-- `BraidingData` is `BraidingDataOn` over the normal form `ι × ℕ`. -/
def BraidingData.toOn (d : BraidingData lam x y) :
    BraidingDataOn lam (LimitSucc.prodNat ι) x y where
  I := d.I
  J := d.J
  I_disjoint := d.I_disjoint
  J_disjoint := d.J_disjoint
  I_cover := d.I_cover
  J_cover := d.J_cover
  I_small := d.I_small
  J_small := d.J_small
  u := d.u
  v := d.v
  v_limit := by rintro ⟨a, n⟩ hp; subst hp; exact d.v_limit a
  hI := d.hI
  hJ := d.hJ

/-- … and conversely. -/
def BraidingDataOn.toBraidingData (d : BraidingDataOn lam (LimitSucc.prodNat ι) x y) :
    BraidingData lam x y where
  I := d.I
  J := d.J
  I_disjoint := d.I_disjoint
  J_disjoint := d.J_disjoint
  I_cover := d.I_cover
  J_cover := d.J_cover
  I_small := d.I_small
  J_small := d.J_small
  u := d.u
  v := d.v
  v_limit a := d.v_limit (a, 0) rfl
  hI := d.hI
  hJ := d.hJ

/-- Braidedness in the sense of `BraidingData` is braidedness over the normal form. -/
theorem isBraided_iff_isBraidedOn_prodNat :
    IsBraided lam x y ↔ IsBraidedOn lam (LimitSucc.prodNat ι) x y :=
  ⟨fun ⟨d⟩ => ⟨d.toOn⟩, fun ⟨d⟩ => ⟨d.toBraidingData⟩⟩

/-! ## Pushing braiding data along a map of index structures

The one construction both halves of Lemma 3.5 rest on.  Given braiding data indexed by `M` and a
map `Φ : M → M'` that commutes with the successor, reflects limit elements and has finite fibres,
the unions and sums of the data over the fibres of `Φ` are braiding data indexed by `M'`.

The only delicate point is the `J`-equation.  Summing `Σ_{j ∈ J p} y j = v (p + 1) + u p` over the
fibre of `q` produces `Σ_{p ∈ Φ⁻¹ q} v (p + 1)`, whereas the new `v` at `q + 1` is
`Σ_{r ∈ Φ⁻¹ (q + 1)} v r`.  The successor maps `Φ⁻¹ q` into `Φ⁻¹ (q + 1)` injectively, and the
elements of `Φ⁻¹ (q + 1)` it misses are precisely limit elements, where `v` vanishes — this is the
paper's "keeping in mind `v_{l_i} = 0`". -/

namespace BraidingDataOn

variable {M M' : Type u} {W : LimitSucc M} {W' : LimitSucc M'}

/-- **Pushing braiding data along `Φ`.**  See the section docstring. -/
noncomputable def comap (d : BraidingDataOn lam W x y) (Φ : M → M')
    (hfin : ∀ q : M', (Φ ⁻¹' {q} : Set M).Finite)
    (hsucc : ∀ p, Φ (W.succ p) = W'.succ (Φ p))
    (hlim : ∀ p, W'.IsLimit (Φ p) → W.IsLimit p) :
    BraidingDataOn lam W' x y :=
  have hFlt : ∀ q : M', #(Φ ⁻¹' {q} : Set M) < lam := fun q =>
    lt_of_lt_of_le (Cardinal.lt_aleph0_iff_set_finite.mpr (hfin q)) (LMonoid.aleph0_le (X := X))
  have hIsmall : ∀ q : M', #(⋃ p : (Φ ⁻¹' {q} : Set M), d.I (p : M)) < lam := fun q =>
    (Cardinal.card_iUnion_lt_iff_forall_of_isRegular (LMonoid.isRegular' (X := X))
      (hFlt q)).mpr fun p => d.I_small (p : M)
  have hJsmall : ∀ q : M', #(⋃ p : (Φ ⁻¹' {q} : Set M), d.J (p : M)) < lam := fun q =>
    (Cardinal.card_iUnion_lt_iff_forall_of_isRegular (LMonoid.isRegular' (X := X))
      (hFlt q)).mpr fun p => d.J_small (p : M)
  -- distinct fibres consist of distinct positions, so the unions stay disjoint
  have hfibne : ∀ {q q' : M'}, q ≠ q' → ∀ (p : (Φ ⁻¹' {q} : Set M))
      (p' : (Φ ⁻¹' {q'} : Set M)), (p : M) ≠ (p' : M) := by
    intro q q' hqq' p p' hp
    exact hqq' (by rw [← p.2, hp]; exact p'.2)
  have hIdisj : ∀ q q' : M', q ≠ q' →
      Disjoint (⋃ p : (Φ ⁻¹' {q} : Set M), d.I (p : M))
        (⋃ p : (Φ ⁻¹' {q'} : Set M), d.I (p : M)) := by
    intro q q' hqq'
    exact Set.disjoint_iUnion_left.mpr fun p => Set.disjoint_iUnion_right.mpr fun p' =>
      d.I_disjoint _ _ (hfibne hqq' p p')
  have hJdisj : ∀ q q' : M', q ≠ q' →
      Disjoint (⋃ p : (Φ ⁻¹' {q} : Set M), d.J (p : M))
        (⋃ p : (Φ ⁻¹' {q'} : Set M), d.J (p : M)) := by
    intro q q' hqq'
    exact Set.disjoint_iUnion_left.mpr fun p => Set.disjoint_iUnion_right.mpr fun p' =>
      d.J_disjoint _ _ (hfibne hqq' p p')
  have hIcover : (⋃ q : M', ⋃ p : (Φ ⁻¹' {q} : Set M), d.I (p : M)) = Set.univ := by
    refine Set.eq_univ_of_forall fun i => ?_
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (d.I_cover ▸ Set.mem_univ i)
    exact Set.mem_iUnion.mpr ⟨Φ p, Set.mem_iUnion.mpr ⟨⟨p, rfl⟩, hp⟩⟩
  have hJcover : (⋃ q : M', ⋃ p : (Φ ⁻¹' {q} : Set M), d.J (p : M)) = Set.univ := by
    refine Set.eq_univ_of_forall fun i => ?_
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (d.J_cover ▸ Set.mem_univ i)
    exact Set.mem_iUnion.mpr ⟨Φ p, Set.mem_iUnion.mpr ⟨⟨p, rfl⟩, hp⟩⟩
  -- a fibre over a limit element consists of limit elements, where `v` vanishes
  have hvlim : ∀ q : M', W'.IsLimit q →
      lsumOf (lam := lam) (hFlt q) (fun p : (Φ ⁻¹' {q} : Set M) => d.v (p : M)) = 0 := by
    intro q hq
    refine LMonoid.lsumOf_eq_zero_of_forall _ fun p => ?_
    exact d.v_limit (p : M) (hlim _ (by rw [p.2]; exact hq))
  have hIeq : ∀ q : M',
      lsumOf (lam := lam) (hIsmall q)
          (fun i : (⋃ p : (Φ ⁻¹' {q} : Set M), d.I (p : M)) => x i)
        = lsumOf (lam := lam) (hFlt q) (fun p : (Φ ⁻¹' {q} : Set M) => d.v (p : M))
          + lsumOf (lam := lam) (hFlt q) (fun p : (Φ ⁻¹' {q} : Set M) => d.u (p : M)) := by
    intro q
    calc lsumOf (lam := lam) (hIsmall q)
            (fun i : (⋃ p : (Φ ⁻¹' {q} : Set M), d.I (p : M)) => x i)
        = lsumOf (lam := lam) (hFlt q) (fun p : (Φ ⁻¹' {q} : Set M) =>
            ∑[lam] i ∈ d.I (p : M), x i) :=
          (LMonoid.lsumOf_biUnion_subset _ _
            (fun p p' hpp' => d.I_disjoint _ _ fun h => hpp' (Subtype.ext h)) rfl
            (hFlt q) (hIsmall q) (fun p => d.I_small (p : M)) x).symm
      _ = lsumOf (lam := lam) (hFlt q)
            (fun p : (Φ ⁻¹' {q} : Set M) => d.v (p : M) + d.u (p : M)) := by
          exact congrArg _ (funext fun p => d.hI (p : M))
      _ = _ := LMonoid.lsumOf_add _ _ _
  have hJeq : ∀ q : M',
      lsumOf (lam := lam) (hJsmall q)
          (fun j : (⋃ p : (Φ ⁻¹' {q} : Set M), d.J (p : M)) => y j)
        = lsumOf (lam := lam) (hFlt (W'.succ q))
            (fun r : (Φ ⁻¹' {W'.succ q} : Set M) => d.v (r : M))
          + lsumOf (lam := lam) (hFlt q) (fun p : (Φ ⁻¹' {q} : Set M) => d.u (p : M)) := by
    intro q
    classical
    -- the successor embeds the fibre over `q` into the fibre over `q + 1`
    have hmem : ∀ p : (Φ ⁻¹' {q} : Set M), W.succ (p : M) ∈ (Φ ⁻¹' {W'.succ q} : Set M) := by
      intro p
      show Φ (W.succ (p : M)) = W'.succ q
      rw [hsucc, p.2]
    have hembinj : Function.Injective
        (fun p : (Φ ⁻¹' {q} : Set M) => (⟨W.succ (p : M), hmem p⟩ : (Φ ⁻¹' {W'.succ q} : Set M))) :=
      fun p p' h => Subtype.ext (W.succ_injective (congrArg Subtype.val h))
    set e : (Φ ⁻¹' {q} : Set M) ↪ (Φ ⁻¹' {W'.succ q} : Set M) :=
      ⟨fun p => ⟨W.succ (p : M), hmem p⟩, hembinj⟩ with hedef
    -- and the positions it misses are limit elements, where `v` vanishes
    have hext : Function.extend (⇑e)
          (fun p : (Φ ⁻¹' {q} : Set M) => d.v (W.succ (p : M))) 0
        = fun r : (Φ ⁻¹' {W'.succ q} : Set M) => d.v (r : M) := by
      funext r
      by_cases hr : ∃ p, e p = r
      · obtain ⟨p, rfl⟩ := hr
        rw [e.injective.extend_apply]
        rfl
      · rw [Function.extend_apply' _ _ _ hr]
        show (0 : X) = d.v (r : M)
        refine (d.v_limit (r : M) ?_).symm
        by_contra hnl
        obtain ⟨p₀, hp₀⟩ := W.exists_pred (r : M) hnl
        have hq0 : Φ p₀ = q := by
          have hr2 : Φ (W.succ p₀) = W'.succ q := by rw [hp₀]; exact r.2
          rw [hsucc] at hr2
          exact W'.succ_injective hr2
        exact hr ⟨⟨p₀, hq0⟩, Subtype.ext hp₀⟩
    have hkey : lsumOf (lam := lam) (hFlt (W'.succ q))
          (fun r : (Φ ⁻¹' {W'.succ q} : Set M) => d.v (r : M))
        = lsumOf (lam := lam) (hFlt q)
            (fun p : (Φ ⁻¹' {q} : Set M) => d.v (W.succ (p : M))) := by
      rw [← hext]
      exact LMonoid.lsumOf_extend (hFlt q) (hFlt (W'.succ q)) e _
    calc lsumOf (lam := lam) (hJsmall q)
            (fun j : (⋃ p : (Φ ⁻¹' {q} : Set M), d.J (p : M)) => y j)
        = lsumOf (lam := lam) (hFlt q) (fun p : (Φ ⁻¹' {q} : Set M) =>
            ∑[lam] j ∈ d.J (p : M), y j) :=
          (LMonoid.lsumOf_biUnion_subset _ _
            (fun p p' hpp' => d.J_disjoint _ _ fun h => hpp' (Subtype.ext h)) rfl
            (hFlt q) (hJsmall q) (fun p => d.J_small (p : M)) y).symm
      _ = lsumOf (lam := lam) (hFlt q)
            (fun p : (Φ ⁻¹' {q} : Set M) => d.v (W.succ (p : M)) + d.u (p : M)) := by
          exact congrArg _ (funext fun p => d.hJ (p : M))
      _ = lsumOf (lam := lam) (hFlt q)
            (fun p : (Φ ⁻¹' {q} : Set M) => d.v (W.succ (p : M)))
          + lsumOf (lam := lam) (hFlt q) (fun p : (Φ ⁻¹' {q} : Set M) => d.u (p : M)) :=
          LMonoid.lsumOf_add _ _ _
      _ = _ := by rw [hkey]
  { I := fun q => ⋃ p : (Φ ⁻¹' {q} : Set M), d.I (p : M)
    J := fun q => ⋃ p : (Φ ⁻¹' {q} : Set M), d.J (p : M)
    I_disjoint := hIdisj
    J_disjoint := hJdisj
    I_cover := hIcover
    J_cover := hJcover
    I_small := hIsmall
    J_small := hJsmall
    u := fun q => lsumOf (lam := lam) (hFlt q) (fun p : (Φ ⁻¹' {q} : Set M) => d.u (p : M))
    v := fun q => lsumOf (lam := lam) (hFlt q) (fun p : (Φ ⁻¹' {q} : Set M) => d.v (p : M))
    v_limit := hvlim
    hI := hIeq
    hJ := hJeq }

/-- `comap`, at the level of the braiding relation. -/
theorem _root_.KappaMonoid.IsBraidedOn.comap (h : IsBraidedOn lam W x y) (Φ : M → M')
    (hfin : ∀ q : M', (Φ ⁻¹' {q} : Set M).Finite)
    (hsucc : ∀ p, Φ (W.succ p) = W'.succ (Φ p))
    (hlim : ∀ p, W'.IsLimit (Φ p) → W.IsLimit p) :
    IsBraidedOn lam W' x y :=
  ⟨h.some.comap Φ hfin hsucc hlim⟩

end BraidingDataOn

/-! ## Lemma 3.4(2)(3): a braiding is a disjoint union of `ω`-block braidings

Part (2) restricts a braiding to one `ω`-block of the well-order; part (3) assembles a braiding
from a family of them, one per piece of a pair of indexed partitions of the index set.  Together
they say that a braiding *is* a disjoint union of countable braidings, which is the shape the
`ι × ℕ` normal form of `BraidingData` records.

The paper indexes the restricted families by the blocks `I(l)`, `J(l)` themselves, and so has to
require `|I(l)| = |J(l)|` infinite for Definition 3.1 to apply to them; here they are padded by
zeroes to the ambient index set — which is what the paper's "padded by zeroes to an index set of
cardinality `κ`" asks for in (2) — so (3) is the exact converse of (2) and needs no such
hypothesis. -/

section Blocks

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {ι : Type u} {x y : ι → X}

/-- The part of the index set that the `ω`-block of the limit element `(a, 0)` covers on the
`x`-side: `I(a) = ⋃ₘ I (a, m)`. -/
def BraidingData.blockI (d : BraidingData lam x y) (a : ι) : Set ι := ⋃ m : ℕ, d.I (a, m)

/-- The same on the `y`-side: `J(a) = ⋃ₘ J (a, m)`. -/
def BraidingData.blockJ (d : BraidingData lam x y) (a : ι) : Set ι := ⋃ m : ℕ, d.J (a, m)

theorem BraidingData.subset_blockI (d : BraidingData lam x y) (p : ι × ℕ) :
    d.I p ⊆ d.blockI p.1 := fun _ hi => Set.mem_iUnion.mpr ⟨p.2, hi⟩

theorem BraidingData.subset_blockJ (d : BraidingData lam x y) (p : ι × ℕ) :
    d.J p ⊆ d.blockJ p.1 := fun _ hj => Set.mem_iUnion.mpr ⟨p.2, hj⟩

theorem BraidingData.notMem_blockI (d : BraidingData lam x y) {a : ι} {p : ι × ℕ}
    (hp : p.1 ≠ a) {i : ι} (hi : i ∈ d.I p) : i ∉ d.blockI a := by
  rintro hmem
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hmem
  exact Set.disjoint_left.mp (d.I_disjoint p (a, m) (fun h => hp (congrArg Prod.fst h))) hi hm

theorem BraidingData.notMem_blockJ (d : BraidingData lam x y) {a : ι} {p : ι × ℕ}
    (hp : p.1 ≠ a) {j : ι} (hj : j ∈ d.J p) : j ∉ d.blockJ a := by
  rintro hmem
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hmem
  exact Set.disjoint_left.mp (d.J_disjoint p (a, m) (fun h => hp (congrArg Prod.fst h))) hj hm

/-- **Lemma 3.4(2)**: the restriction of a braiding to one `ω`-block of the well-order is again a
braiding.  Concretely, if `x` and `y` are `λ⁻`-braided by `d`, then for every limit element
`(a, 0)` the subfamilies supported on `I(a)` and `J(a)` — padded by zeroes to the whole index set —
are `λ⁻`-braided.

The braiding is `d`'s own: keep the partitions, and zero the braiding families off the block.  Off
the block both padded families vanish, so every equation there reads `0 = 0 + 0`. -/
theorem BraidingData.isBraided_block (d : BraidingData lam x y) (a : ι) :
    IsBraided lam (Set.indicator (d.blockI a) x) (Set.indicator (d.blockJ a) y) := by
  classical
  refine ⟨{ I := d.I, J := d.J, I_disjoint := d.I_disjoint, J_disjoint := d.J_disjoint
            I_cover := d.I_cover, J_cover := d.J_cover
            I_small := d.I_small, J_small := d.J_small
            u := fun p => if p.1 = a then d.u p else 0
            v := fun p => if p.1 = a then d.v p else 0
            v_limit := ?_, hI := ?_, hJ := ?_ }⟩
  · intro b
    by_cases hb : b = a
    · subst hb
      simpa using d.v_limit b
    · simp [hb]
  · intro p
    by_cases hp : p.1 = a
    · have hx : ∀ i : d.I p, Set.indicator (d.blockI a) x (i : ι) = x i := fun i =>
        Set.indicator_of_mem (hp ▸ d.subset_blockI p i.2) x
      rw [show (fun i : d.I p => Set.indicator (d.blockI a) x (i : ι))
          = (fun i : d.I p => x (i : ι)) from funext hx, if_pos hp, if_pos hp]
      exact d.hI p
    · rw [LMonoid.lsumOf_eq_zero_of_forall (d.I_small p)
        (fun i => Set.indicator_of_notMem (d.notMem_blockI hp i.2) x), if_neg hp, if_neg hp,
        add_zero]
  · intro p
    by_cases hp : p.1 = a
    · have hy : ∀ j : d.J p, Set.indicator (d.blockJ a) y (j : ι) = y j := fun j =>
        Set.indicator_of_mem (hp ▸ d.subset_blockJ p j.2) y
      have hbs : (bsucc p).1 = a := hp
      rw [show (fun j : d.J p => Set.indicator (d.blockJ a) y (j : ι))
          = (fun j : d.J p => y (j : ι)) from funext hy, if_pos hbs, if_pos hp]
      exact d.hJ p
    · have hbs : ¬ ((bsucc p).1 = a) := hp
      rw [LMonoid.lsumOf_eq_zero_of_forall (d.J_small p)
        (fun j => Set.indicator_of_notMem (d.notMem_blockJ hp j.2) y), if_neg hbs, if_neg hp,
        add_zero]

/-- **Lemma 3.4(3)**, the converse: a family of block braidings assembles into one braiding.

Given indexed partitions `(A l)` and `(B l)` of the index set such that, for every `l`, the
families `x` and `y` cut down to `A l` and `B l` are `λ⁻`-braided, `x` and `y` are `λ⁻`-braided.

The well-order the paper produces is the lexicographic one on the pairs `(l, μ)`; here that is the
index structure with block set `ι × ι`, and Lemma 3.5 (via `comap` along an injection
`ι × ι ↪ ι`, which exists because `ι` is infinite) turns it back into the normal form.  So the
conclusion, plain `IsBraided`, is the paper's *"there exists a limit well-order on `κ` such that
…"*.  The paper's side condition that `|I(l)| = |J(l)|` be infinite is not used, so the statement
here is the stronger one. -/
theorem isBraided_of_blocks [Infinite ι] {A B : ι → Set ι}
    (hAdisj : ∀ l l', l ≠ l' → Disjoint (A l) (A l'))
    (hBdisj : ∀ l l', l ≠ l' → Disjoint (B l) (B l'))
    (hAcov : (⋃ l, A l) = Set.univ) (hBcov : (⋃ l, B l) = Set.univ)
    (h : ∀ l, IsBraided lam (Set.indicator (A l) x) (Set.indicator (B l) y)) :
    IsBraided lam x y := by
  classical
  have d : ∀ l, BraidingData lam (Set.indicator (A l) x) (Set.indicator (B l) y) :=
    fun l => (h l).some
  -- the braiding with block set `ι × ι`: block `(l, b)` is block `b` of the `l`-th braiding,
  -- cut down to `A l`
  have hIsmall : ∀ p : (ι × ι) × ℕ, #((d p.1.1).I (p.1.2, p.2) ∩ A p.1.1 : Set ι) < lam :=
    fun p => lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset Set.inter_subset_left)
      ((d p.1.1).I_small (p.1.2, p.2))
  have hJsmall : ∀ p : (ι × ι) × ℕ, #((d p.1.1).J (p.1.2, p.2) ∩ B p.1.1 : Set ι) < lam :=
    fun p => lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset Set.inter_subset_left)
      ((d p.1.1).J_small (p.1.2, p.2))
  -- on `A l` the `l`-th padded family is `x`, and off it the padded family vanishes
  have hIsum : ∀ p : (ι × ι) × ℕ,
      lsumOf (lam := lam) (hIsmall p)
          (fun i : ((d p.1.1).I (p.1.2, p.2) ∩ A p.1.1 : Set ι) => x (i : ι))
        = (d p.1.1).v (p.1.2, p.2) + (d p.1.1).u (p.1.2, p.2) := by
    rintro ⟨⟨l, b⟩, m⟩
    rw [show (fun i : ((d l).I (b, m) ∩ A l : Set ι) => x (i : ι))
        = (fun i : ((d l).I (b, m) ∩ A l : Set ι) => Set.indicator (A l) x (i : ι)) from
      funext fun i => (Set.indicator_of_mem i.2.2 x).symm,
      ← LMonoid.lsumOf_of_subset ((d l).I_small (b, m)) (hIsmall ⟨(l, b), m⟩)
        Set.inter_subset_left _
        (fun i hi hni => Set.indicator_of_notMem (fun hA => hni ⟨hi, hA⟩) x)]
    exact (d l).hI (b, m)
  have hJsum : ∀ p : (ι × ι) × ℕ,
      lsumOf (lam := lam) (hJsmall p)
          (fun j : ((d p.1.1).J (p.1.2, p.2) ∩ B p.1.1 : Set ι) => y (j : ι))
        = (d p.1.1).v (p.1.2, p.2 + 1) + (d p.1.1).u (p.1.2, p.2) := by
    rintro ⟨⟨l, b⟩, m⟩
    rw [show (fun j : ((d l).J (b, m) ∩ B l : Set ι) => y (j : ι))
        = (fun j : ((d l).J (b, m) ∩ B l : Set ι) => Set.indicator (B l) y (j : ι)) from
      funext fun j => (Set.indicator_of_mem j.2.2 y).symm,
      ← LMonoid.lsumOf_of_subset ((d l).J_small (b, m)) (hJsmall ⟨(l, b), m⟩)
        Set.inter_subset_left _
        (fun j hj hnj => Set.indicator_of_notMem (fun hB => hnj ⟨hj, hB⟩) y)]
    exact (d l).hJ (b, m)
  have hdisj : ∀ {S : ι → ι × ℕ → Set ι} {C : ι → Set ι},
      (∀ l, ∀ p q : ι × ℕ, p ≠ q → Disjoint (S l p) (S l q)) →
      (∀ l l', l ≠ l' → Disjoint (C l) (C l')) →
      ∀ p q : (ι × ι) × ℕ, p ≠ q →
        Disjoint (S p.1.1 (p.1.2, p.2) ∩ C p.1.1) (S q.1.1 (q.1.2, q.2) ∩ C q.1.1) := by
    rintro S C hS hC ⟨⟨l, b⟩, m⟩ ⟨⟨l', b'⟩, m'⟩ hne
    by_cases hll : l = l'
    · subst hll
      refine Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hS l (b, m) (b', m') ?_)
      intro hbm
      have hb : b = b' := congrArg Prod.fst hbm
      have hm : m = m' := congrArg Prod.snd hbm
      exact hne (by rw [hb, hm])
    · exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hC l l' hll)
  have hcov : ∀ {S : ι → ι × ℕ → Set ι} {C : ι → Set ι},
      (∀ l, (⋃ p, S l p) = Set.univ) → ((⋃ l, C l) = Set.univ) →
      (⋃ p : (ι × ι) × ℕ, S p.1.1 (p.1.2, p.2) ∩ C p.1.1) = Set.univ := by
    intro S C hS hC
    refine Set.eq_univ_of_forall fun i => ?_
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hC ▸ Set.mem_univ i)
    obtain ⟨⟨b, m⟩, hbm⟩ := Set.mem_iUnion.mp ((hS l) ▸ Set.mem_univ i)
    exact Set.mem_iUnion.mpr ⟨((l, b), m), hbm, hl⟩
  -- assemble, then move back to the normal form along an injection `ι × ι ↪ ι`
  let e : BraidingDataOn lam (LimitSucc.prodNat (ι × ι)) x y :=
    { I := fun p => (d p.1.1).I (p.1.2, p.2) ∩ A p.1.1
      J := fun p => (d p.1.1).J (p.1.2, p.2) ∩ B p.1.1
      I_disjoint := hdisj (fun l => (d l).I_disjoint) hAdisj
      J_disjoint := hdisj (fun l => (d l).J_disjoint) hBdisj
      I_cover := hcov (fun l => (d l).I_cover) hAcov
      J_cover := hcov (fun l => (d l).J_cover) hBcov
      I_small := hIsmall
      J_small := hJsmall
      u := fun p => (d p.1.1).u (p.1.2, p.2)
      v := fun p => (d p.1.1).v (p.1.2, p.2)
      v_limit := by rintro ⟨⟨l, b⟩, m⟩ hm; subst hm; exact (d l).v_limit b
      hI := hIsum
      hJ := hJsum }
  obtain ⟨f⟩ : Nonempty (ι × ι ↪ ι) := by
    rw [← Cardinal.le_def]
    have hinf : ℵ₀ ≤ #ι := Cardinal.infinite_iff.mp ‹Infinite ι›
    exact le_of_eq (by simp [Cardinal.mk_prod, Cardinal.mul_eq_self hinf])
  refine isBraided_iff_isBraidedOn_prodNat.mpr
    (IsBraidedOn.comap ⟨e⟩ (fun p => (f p.1, p.2)) ?_ (fun _ => rfl) (fun _ hp => hp))
  have hinj : Function.Injective (fun p : (ι × ι) × ℕ => (f p.1, p.2)) := by
    intro p p' hpp
    simp only [Prod.mk.injEq] at hpp
    exact Prod.ext (f.injective hpp.1) hpp.2
  exact fun q => Set.Subsingleton.finite fun p hp p' hp' => hinj (hp.trans hp'.symm)

end Blocks

/-! ## Lemma 3.5

Both directions are `comap` along a map between the two index structures, read off the `ω`-block
decompositions.  The maps are built in `exists_toProdNat` and `exists_ofProdNat`. -/

namespace LimitSucc

variable {M : Type u} (W : LimitSucc M)

theorem blockEquiv_symm_succ (p : M) :
    W.blockEquiv.symm (W.succ p) =
      ((W.blockEquiv.symm p).1, (W.blockEquiv.symm p).2 + 1) := by
  refine W.blockEquiv.symm_apply_eq.mpr ?_
  rw [W.blockEquiv_succ (W.blockEquiv.symm p), W.blockEquiv.apply_symm_apply]

theorem isLimit_of_blockEquiv_symm_snd {p : M} (h : (W.blockEquiv.symm p).2 = 0) :
    W.IsLimit p := by
  have hp : W.blockEquiv (W.blockEquiv.symm p) = p := W.blockEquiv.apply_symm_apply p
  rw [show W.blockEquiv.symm p = ((W.blockEquiv.symm p).1, 0) from Prod.ext rfl h] at hp
  exact hp ▸ (W.blockEquiv.symm p).1.2

theorem mk_eq_mul_aleph0 : #M = #W.Lim * ℵ₀ := by
  rw [← Cardinal.mk_congr W.blockEquiv, Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_nat,
    Cardinal.lift_aleph0]

/-- If a limit well-order has infinitely many blocks, it has exactly as many blocks as
elements. -/
theorem mk_lim_eq_of_infinite (h : ℵ₀ ≤ #W.Lim) : #W.Lim = #M := by
  rw [W.mk_eq_mul_aleph0, Cardinal.mul_aleph0_eq h]

/-- If a limit well-order has finitely many blocks, it is countable. -/
theorem countable_of_lim_finite (h : #W.Lim < ℵ₀) : #M ≤ ℵ₀ := by
  rw [W.mk_eq_mul_aleph0]
  exact Cardinal.mul_le_max_of_aleph0_le_right le_rfl |>.trans (by simp [h.le])

/-- With no blocks there are no elements. -/
theorem isEmpty_of_lim_isEmpty (h : IsEmpty W.Lim) : IsEmpty M :=
  ⟨fun p => h.elim (W.blockEquiv.symm p).1⟩

end LimitSucc

namespace LimitSucc

variable {M : Type u} (W : LimitSucc M)

/-- The blocks inject into the elements: a block is its own least element. -/
theorem mk_lim_le : #W.Lim ≤ #M :=
  Cardinal.mk_le_of_injective (f := fun l => W.blockEquiv (l, 0))
    fun _ _ h => (Prod.ext_iff.mp (W.blockEquiv.injective h)).1

/-- **The map for the forward half of Lemma 3.5.**  Send `μ` to its block — named in `ι` by an
injection `f` of the blocks into the index set — together with its offset in that block.  It is
injective, commutes with the successor by construction, and sends a limit element to one. -/
theorem exists_map_toProdNat (f : W.Lim ↪ ι) :
    ∃ Φ : M → ι × ℕ, (∀ q, (Φ ⁻¹' {q} : Set M).Finite)
      ∧ (∀ p, Φ (W.succ p) = (LimitSucc.prodNat ι).succ (Φ p))
      ∧ (∀ p, (LimitSucc.prodNat ι).IsLimit (Φ p) → W.IsLimit p) := by
  refine ⟨fun p => (f (W.blockEquiv.symm p).1, (W.blockEquiv.symm p).2), ?_, ?_, ?_⟩
  · have hinj : Function.Injective
        (fun p : M => (f (W.blockEquiv.symm p).1, (W.blockEquiv.symm p).2)) := by
      intro p p' h
      simp only [Prod.mk.injEq] at h
      exact W.blockEquiv.symm.injective (Prod.ext (f.injective h.1) h.2)
    exact fun q => Set.Subsingleton.finite fun p hp p' hp' => hinj (hp.trans hp'.symm)
  · intro p
    show (f (W.blockEquiv.symm (W.succ p)).1, (W.blockEquiv.symm (W.succ p)).2)
        = bsucc (f (W.blockEquiv.symm p).1, (W.blockEquiv.symm p).2)
    rw [W.blockEquiv_symm_succ]
    rfl
  · exact fun p hp => W.isLimit_of_blockEquiv_symm_snd hp

/-- **The map for the backward half of Lemma 3.5.**  If the blocks are infinite there are as many
of them as there are indices, and the normal form is relabelled one block at a time.  If there are
finitely many blocks the index set is countable, and the whole of `ι × ℕ` is folded into a single
`ω`-block along the anti-diagonal `(a, n) ↦ e a + n + 1` — the paper's diagonal argument.  Its
fibres are finite, which is all `comap` needs; that the offset lands at `≥ 1` is what makes `v`
still vanish at the limit element of that block. -/
theorem exists_map_ofProdNat (hmk : #ι = #M) :
    ∃ Ψ : ι × ℕ → M, (∀ q, (Ψ ⁻¹' {q} : Set (ι × ℕ)).Finite)
      ∧ (∀ p, Ψ ((LimitSucc.prodNat ι).succ p) = W.succ (Ψ p))
      ∧ (∀ p, W.IsLimit (Ψ p) → (LimitSucc.prodNat ι).IsLimit p) := by
  classical
  rcases isEmpty_or_nonempty W.Lim with hLe | hLne
  · -- no blocks: no elements, and `ι` is empty too
    have hM : IsEmpty M := W.isEmpty_of_lim_isEmpty hLe
    have hι : IsEmpty ι := by
      rw [← Cardinal.mk_eq_zero_iff, hmk, Cardinal.mk_eq_zero_iff]
      exact hM
    exact ⟨fun p => (hι.elim p.1 : M), fun q => Set.toFinite _,
      fun p => (hι.elim p.1 : _), fun p => (hι.elim p.1 : _)⟩
  rcases lt_or_ge (#W.Lim) ℵ₀ with hfin | hinf
  · -- finitely many blocks: fold everything into the block of `l₀`
    obtain ⟨l₀⟩ := hLne
    have hcount : #ι ≤ ℵ₀ := hmk ▸ W.countable_of_lim_finite hfin
    have hctble : Countable ι := Cardinal.mk_le_aleph0_iff.mp hcount
    obtain ⟨e⟩ : Nonempty (ι ↪ ℕ) := nonempty_embedding_nat ι
    have hanti : ∀ m : ℕ, {p : ι × ℕ | e p.1 + p.2 + 1 = m}.Finite := by
      intro m
      have hsub : {p : ι × ℕ | e p.1 + p.2 + 1 = m}
          ⊆ (fun p : ι × ℕ => (e p.1, p.2)) ⁻¹' (Set.Iio m ×ˢ Set.Iio m) := by
        rintro ⟨a, n⟩ h
        have h' : e a + n + 1 = m := h
        exact ⟨by simp only [Set.mem_Iio]; omega, by simp only [Set.mem_Iio]; omega⟩
      refine Set.Finite.subset (Set.Finite.preimage ?_ ?_) hsub
      · refine Set.injOn_of_injective fun p p' h => ?_
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (e.injective h.1) h.2
      · exact (Set.finite_Iio m).prod (Set.finite_Iio m)
    refine ⟨fun p => W.blockEquiv (l₀, e p.1 + p.2 + 1), ?_, ?_, ?_⟩
    · intro q
      refine Set.Finite.subset (hanti (W.blockEquiv.symm q).2) ?_
      rintro ⟨a, n⟩ hp
      have h1 : W.blockEquiv (l₀, e a + n + 1) = q := hp
      have h2 := congrArg (fun z => (W.blockEquiv.symm z).2) h1
      rw [W.blockEquiv.symm_apply_apply] at h2
      exact h2
    · rintro ⟨a, n⟩
      show W.blockEquiv (l₀, e a + (n + 1) + 1) = W.succ (W.blockEquiv (l₀, e a + n + 1))
      rw [← W.blockEquiv_succ (l₀, e a + n + 1)]
      exact congrArg _ (Prod.ext rfl (by omega))
    · rintro ⟨a, n⟩ hp
      have h := W.blockEquiv_symm_snd_eq_zero hp
      rw [W.blockEquiv.symm_apply_apply] at h
      exact absurd h (Nat.succ_ne_zero _)
  · -- infinitely many blocks: there are `#ι` of them, so relabel block by block
    obtain ⟨g⟩ : Nonempty (ι ↪ W.Lim) := by
      rw [← Cardinal.le_def]
      exact hmk.le.trans (W.mk_lim_eq_of_infinite hinf).ge
    refine ⟨fun p => W.blockEquiv (g p.1, p.2), ?_, ?_, ?_⟩
    · have hinj : Function.Injective (fun p : ι × ℕ => W.blockEquiv (g p.1, p.2)) := by
        intro p p' h
        have h' := W.blockEquiv.injective h
        simp only [Prod.mk.injEq] at h'
        exact Prod.ext (g.injective h'.1) h'.2
      exact fun q => Set.Subsingleton.finite fun p hp p' hp' => hinj (hp.trans hp'.symm)
    · rintro ⟨a, n⟩
      exact (W.blockEquiv_succ (g a, n)).symm ▸ rfl
    · rintro ⟨a, n⟩ hp
      have h := W.blockEquiv_symm_snd_eq_zero hp
      rwa [W.blockEquiv.symm_apply_apply] at h

end LimitSucc

/-! ### The statement

`isBraidedOn_iff_isBraided` is Lemma 3.5 together with the claim implicit in the normal form of
`BraidingData`: braidedness with respect to *any* index structure on a set of the same size as the
index set of the families — in particular with respect to any limit well-order on `κ`, which is
Definition 3.1(1) as the paper states it — is braidedness in the sense of `BraidingData`. -/

/-- **Lemma 3.5** (and the justification of the `ι × ℕ` normal form).  For any index structure `W`
on a set `M` of the same cardinality as the index set `ι`, braidedness over `W` agrees with
`IsBraided`.

Forward: name each block of `W` by an index and read off block and offset, which embeds `M` into
`ι × ℕ` compatibly with successors and limits.  Backward: if `W` has infinitely many blocks it has
`#ι` of them and `ι × ℕ` is relabelled block by block; if it has finitely many then `ι` is
countable and all of `ι × ℕ` folds into one block along the anti-diagonal.  Both are `comap`. -/
theorem isBraidedOn_iff_isBraided {M : Type u} (W : LimitSucc M) (hmk : #ι = #M) (x y : ι → X) :
    IsBraidedOn lam W x y ↔ IsBraided lam x y := by
  constructor
  · intro h
    obtain ⟨f⟩ : Nonempty (W.Lim ↪ ι) := by
      rw [← Cardinal.le_def]
      exact W.mk_lim_le.trans hmk.ge
    obtain ⟨Φ, hfin, hsucc, hlim⟩ := W.exists_map_toProdNat f
    exact isBraided_iff_isBraidedOn_prodNat.mpr (h.comap Φ hfin hsucc hlim)
  · intro h
    obtain ⟨Ψ, hfin, hsucc, hlim⟩ := W.exists_map_ofProdNat hmk
    exact (isBraided_iff_isBraidedOn_prodNat.mp h).comap Ψ hfin hsucc hlim

/-- **Lemma 3.5** as the paper states it: `λ⁻`-braidedness does not depend on the choice of limit
well-order.  Two limit well-orders on `κ` give two index structures, and the relations they define
coincide. -/
theorem isBraidedOn_congr {M₁ M₂ : Type u} (W₁ : LimitSucc M₁) (W₂ : LimitSucc M₂)
    (h₁ : #ι = #M₁) (h₂ : #ι = #M₂) (x y : ι → X) :
    IsBraidedOn lam W₁ x y ↔ IsBraidedOn lam W₂ x y := by
  rw [isBraidedOn_iff_isBraided W₁ h₁, isBraidedOn_iff_isBraided W₂ h₂]

/-- **Lemma 3.5** for limit well-orders on the index set itself, which is the paper's phrasing:
`κ` carries a well-order in which every element has a successor, and the braiding partitions are
indexed by `κ`. -/
theorem isBraidedOn_ofWellOrder_iff [LinearOrder ι] [WellFoundedLT ι] [NoMaxOrder ι]
    (x y : ι → X) :
    IsBraidedOn lam (LimitSucc.ofWellOrder ι) x y ↔ IsBraided lam x y :=
  isBraidedOn_iff_isBraided _ rfl x y

/-- **Lemma 3.5**, the two-orders form: any two limit well-orders on the index set define the same
braiding relation. -/
theorem isBraidedOn_congr_self (W₁ W₂ : LimitSucc ι) (x y : ι → X) :
    IsBraidedOn lam W₁ x y ↔ IsBraidedOn lam W₂ x y :=
  isBraidedOn_congr W₁ W₂ rfl rfl x y

end KappaMonoid
