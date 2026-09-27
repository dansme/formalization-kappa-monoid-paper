/-
**Lemma 3.2** (telescoping: braided families have equal sums) and **Lemma 3.4**, including the
converse of 3.4(1): braidedness preserves smallness of support.
-/
import KappaMonoid.Braiding.TransAleph0

universe u v w

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid


/-! ## Lemma 3.2 and Lemma 3.4 -/

section Ambient

variable {lam κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]
  (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ)

/-- Lemma 3.2 (telescoping): braided families have equal `κ`-sums.

Note that the braiding is taken with respect to the `λ⁻`-monoid structure that `H` carries
as a `κ`-monoid (`KMonoid.toLMonoid`). -/
theorem sumOf_eq_of_isBraided {ι : Type u} (hι : #ι ≤ κ) (x y : ι → H)
    (h : letI := KMonoid.toLMonoidOfLE H hlam hlk; IsBraided lam x y) :
    sumOf (κ := κ) hι x = sumOf (κ := κ) hι y := by
  let := KMonoid.toLMonoidOfLE H hlam hlk
  obtain ⟨d⟩ := h
  have hκ := KMonoid.aleph0_le (κ := κ) (H := H)
  have hP : #(ι × ℕ) ≤ κ := mk_prod_nat_le hκ hι
  have hIle : ∀ p, #(d.I p) ≤ κ := fun p => le_of_lt_of_le_succ hlk (d.I_lt p)
  have hJle : ∀ p, #(d.J p) ≤ κ := fun p => le_of_lt_of_le_succ hlk (d.J_lt p)
  -- Regroup each side along its braiding partition and use the defining equations.
  have hxsum : sumOf (κ := κ) hι x = sumOf (κ := κ) hP (fun p => d.v p + d.u p) := by
    rw [← sumOf_biUnion d.I d.I_disjoint d.I_cover hP hι hIle x]
    congr 1
    funext p
    exact (KMonoid.toLMonoidOfLE_lsumOf hlam hlk (d.I_lt p)
      (fun i : d.I p => x i)).symm.trans (d.hI p)
  have hysum : sumOf (κ := κ) hι y = sumOf (κ := κ) hP (fun p => d.v (bsucc p) + d.u p) := by
    rw [← sumOf_biUnion d.J d.J_disjoint d.J_cover hP hι hJle y]
    congr 1
    funext p
    exact (KMonoid.toLMonoidOfLE_lsumOf hlam hlk (d.J_lt p)
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
    (h : ∑[lam] i ∈ Function.support x, x i
        = ∑[lam] i ∈ Function.support y, y i) :
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
    ∑[lam] i ∈ (⋃ n : ULift.{u} ℕ, d.I (a, n.down) : Set ι), x i
      = ∑[lam] j ∈ (⋃ n : ULift.{u} ℕ, d.J (a, n.down) : Set ι), y j := by
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
    (fun n : N => d.I (a, n.down))
    hIdisj' rfl hNlt hI (fun n => d.I_lt (a, n.down)) x).symm
  have step2 := (LMonoid.lsumOf_biUnion_subset (⋃ n : N, d.J (a, n.down))
    (fun n : N => d.J (a, n.down))
    hJdisj' rfl hNlt hJ (fun n => d.J_lt (a, n.down)) y).symm
  rw [step1, step2]
  have hIeq : (fun n : N =>
      ∑[lam] i ∈ d.I (a, n.down), x i)
      = fun n : N => d.v (a, n.down) + d.u (a, n.down) := funext fun n => d.hI (a, n.down)
  have hJeq : (fun n : N =>
      ∑[lam] j ∈ d.J (a, n.down), y j)
      = fun n : N => d.v (a, n.down + 1) + d.u (a, n.down) := funext fun n => d.hJ (a, n.down)
  have := CardLT.mk hNlt
  rw [hIeq, hJeq, LMonoid.lsumOf_add (fun n : N => d.v (a, n.down)) (fun n : N => d.u (a, n.down)),
    LMonoid.lsumOf_add (fun n : N => d.v (a, n.down + 1)) (fun n : N => d.u (a, n.down))]
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
  have hvtel : ∑[lam] n : N, d.v (a, n.down)
      = ∑[lam] n : N, d.v (a, n.down + 1) := by
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
        ∑[lam] j ∈ d.J (a, k), y j)
      = (∑ᶠ a ∈ A, ∑ k ∈ Finset.range (K + 1),
          ∑[lam] i ∈ d.I (a, k), x i)
        + ∑ᶠ a ∈ A, d.v (a, K + 1) := by
  have hchain : ∀ a : ι,
      (∑ k ∈ Finset.range (K + 1),
          ∑[lam] j ∈ d.J (a, k), y j)
        = (∑ k ∈ Finset.range (K + 1),
            ∑[lam] i ∈ d.I (a, k), x i)
          + d.v (a, K + 1) := by
    intro a
    have hI' : ∀ k : ℕ, ∑[lam] i ∈ d.I (a, k), x i
        = d.v (a, k) + d.u (a, k) := fun k => d.hI (a, k)
    have hJ' : ∀ k : ℕ, ∑[lam] j ∈ d.J (a, k), y j
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

/-! ### Rectangles of a partition -/

/-- The *rectangle* of the partition `P` over the chains `a ∈ A` up to level `K`: the union of the
pieces `P (a, k)` with `a ∈ A` and `k ≤ K`.  This is what the paper's cut `μ ≤ α` becomes for the
`ι × ℕ` normal form, whose positions form many `ω`-chains instead of one well-order. -/
def rect (P : ι × ℕ → Set ι) (A : Set ι) (K : ℕ) : Set ι :=
  ⋃ a ∈ A, ⋃ k ∈ (Finset.range (K + 1) : Set ℕ), P (a, k)

theorem rect_finite {P : ι × ℕ → Set ι} (hP : ∀ p, #(P p) < ℵ₀) {A : Set ι} (hA : A.Finite)
    (K : ℕ) : (rect P A K).Finite :=
  hA.biUnion fun a _ => (Finset.range (K + 1)).finite_toSet.biUnion
    fun k _ => lt_aleph0_iff_set_finite.mp (hP (a, k))

/-- An element lies in the rectangle as soon as its piece does. -/
theorem mem_rect {P : ι × ℕ → Set ι} {A : Set ι} {K : ℕ} {i : ι} {p : ι × ℕ} (hi : i ∈ P p)
    (hA : p.1 ∈ A) (hK : p.2 ≤ K) : i ∈ rect P A K :=
  mem_biUnion hA (mem_biUnion (by simpa [Nat.lt_succ_iff] using hK) hi)

/-- A sum over a rectangle of a partition is the double sum over its pieces. -/
theorem finsum_rect {X : Type v} [LMonoid ℵ₀ X] {P : ι × ℕ → Set ι}
    (hPd : ∀ p q, p ≠ q → Disjoint (P p) (P q)) (hP : ∀ p, #(P p) < ℵ₀) {A : Set ι}
    (hA : A.Finite) (K : ℕ) (f : ι → X) :
    ∑ᶠ i ∈ rect P A K, f i
      = ∑ᶠ a ∈ A, ∑ k ∈ Finset.range (K + 1),
        ∑[ℵ₀] i ∈ P (a, k), f i := by
  have hfin : ∀ p, (P p).Finite := fun p => lt_aleph0_iff_set_finite.mp (hP p)
  rw [rect, finsum_mem_biUnion _ hA fun a _ => (Finset.range (K + 1)).finite_toSet.biUnion
    fun k _ => hfin (a, k)]
  · refine finsum_mem_congr rfl fun a _ => ?_
    rw [finsum_mem_biUnion _ (Finset.range (K + 1)).finite_toSet fun k _ => hfin (a, k),
      finsum_mem_coe_finset]
    · exact Finset.sum_congr rfl fun k _ => (LMonoid.lsumOf_eq_finsum (hP (a, k)) f).symm
    · exact fun k _ k' _ hkk' => hPd (a, k) (a, k') fun h => hkk' (congrArg Prod.snd h)
  · intro a _ a' _ haa'
    refine Set.disjoint_left.mpr fun i hi hi' => ?_
    obtain ⟨k, -, hk⟩ := mem_iUnion₂.mp hi
    obtain ⟨k', -, hk'⟩ := mem_iUnion₂.mp hi'
    exact Set.disjoint_left.mp (hPd (a, k) (a', k') fun h => haa' (congrArg Prod.fst h)) hk hk'

/-- Forward implication of Lemma 3.4(4) (uncountable-`λ` collapse of braiding data), used in
`isBraided_iff_of_ne_aleph0`. -/
theorem exists_partition_of_isBraided_of_ne_aleph0 {lam : Cardinal.{u}} {X : Type v}
    [LMonoid lam X] {ι : Type u} (hlam : lam ≠ ℵ₀) (x y : ι → X) :
    IsBraided lam x y →
      ∃ (I J : ι × ℕ → Set ι) (hI : ∀ p, #(I p) < lam) (hJ : ∀ p, #(J p) < lam),
        (∀ p q, p ≠ q → Disjoint (I p) (I q)) ∧ (∀ p q, p ≠ q → Disjoint (J p) (J q)) ∧
        (⋃ p, I p) = Set.univ ∧ (⋃ p, J p) = Set.univ ∧
        ∀ p, ∑[lam] i ∈ I p, x i
            = ∑[lam] j ∈ J p, y j := by
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
        (‹LMonoid lam X›.isRegular) hNlt).mpr (fun n => d.I_lt (a, n.down))
    · rw [hInz a m, Cardinal.mk_eq_zero]
      exact Cardinal.aleph0_pos.trans_le hlam0.le
  have hJsmall : ∀ p, #(J p) < lam := by
    rintro ⟨a, n⟩
    rcases n with _ | m
    · rw [hJzero a]
      exact (Cardinal.card_iUnion_lt_iff_forall_of_isRegular
        (‹LMonoid lam X›.isRegular) hNlt).mpr (fun n => d.J_lt (a, n.down))
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
        ∀ p, ∑[lam] i ∈ I p, x i
            = ∑[lam] j ∈ J p, y j := by
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
    (h : ∑[lam] i ∈ S, f i = 0) {i : ι} (hi : i ∈ S) : f i = 0 := by
  classical
  have hset : ({i} : Set ι) ∪ (S \ {i}) = S := by
    ext j
    by_cases hj : j = i <;> simp [hj, hi]
  have h1 : #({i} : Set ι) < lam :=
    LMonoid.mk_lt_finite (X := X) _
  have hT : #(↥(S \ {i})) < lam :=
    lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset Set.sdiff_subset) hS
  have hST : #(↥(({i} : Set ι) ∪ (S \ {i}))) < lam := by rw [hset]; exact hS
  have hcollapse : ∑[lam] j ∈ ({i} : Set ι) ∪ (S \ {i}), f j
      = ∑[lam] j ∈ S, f j :=
    LMonoid.lsumOf_of_subset hST hS (le_of_eq hset.symm) f fun j hj hnj =>
      absurd (hset ▸ hj) hnj
  have hsplit := LMonoid.lsumOf_union ({i} : Set ι) (S \ {i})
    (Set.disjoint_iff_inter_eq_empty.mpr (by simp)) h1 hT f hST
  rw [hcollapse, h] at hsplit
  have : Unique ({i} : Set ι) := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.2⟩
  have hdef : ((default : ({i} : Set ι)) : ι) = i := (default : ({i} : Set ι)).2
  have hsingle : ∑[lam] j ∈ ({i} : Set ι), f j = f i := by
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
    have := hfin.to_subtype
    exact LMonoid.mk_lt_finite (X := X) _
  -- outside `Low`, the `y`-pieces carry nothing
  have hzero : ∀ p : ι × ℕ, p ∉ Low → ∀ j ∈ d.J p, y j = 0 := by
    intro p hp j hj
    have hIzero : ∀ m, p.2 ≤ m → ∑[lam] i ∈ d.I (p.1, m), x i = 0 := by
      intro m hm
      refine LMonoid.lsumOf_eq_zero _ x fun i hi => ?_
      by_contra hne
      exact hp ⟨m, hm, i, hi, hne⟩
    have huv : ∀ m, p.2 ≤ m → d.v (p.1, m) = 0 ∧ d.u (p.1, m) = 0 := by
      intro m hm
      have := (d.hI (p.1, m)).symm.trans (hIzero m hm)
      exact hcon _ _ this
    have hJsum : ∑[lam] j ∈ d.J p, y j = 0 := by
      rw [d.hJ p]
      show d.v (p.1, p.2 + 1) + d.u p = 0
      rw [(huv (p.2 + 1) (Nat.le_succ p.2)).1, (huv p.2 le_rfl).2, add_zero]
    exact eq_zero_of_lsumOf_eq_zero hcon (d.J_lt p) y hJsum hj
  -- hence the support of `y` sits inside the `Low` pieces
  have hsupp : Function.support y ⊆ ⋃ p : Low, d.J (p : ι × ℕ) := by
    intro j hj
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (d.J_cover ▸ Set.mem_univ j)
    by_cases hpLow : p ∈ Low
    · exact Set.mem_iUnion.mpr ⟨⟨p, hpLow⟩, hp⟩
    · exact absurd (hzero p hpLow j hp) hj
  refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hsupp) ?_
  exact lt_of_le_of_lt Cardinal.mk_iUnion_le_sum_mk
    (Cardinal.sum_lt_of_isRegular hlam hLow fun p => d.J_lt _)

end Lemma34

end KappaMonoid
