/-
**Examples 4.8(4)**: the monoid-theoretic content of the example of Dedekind domains — the
universal `κ`-extension of `D = {(n, g) ∈ ℕ₀ × G : n ≥ 1 or g = 0}` is
`E_κ = {(α, g) ∈ F_κ × G : 1 ≤ α < ℵ₀ or g = 0}`, for every infinite `κ` and every abelian group
`G`, and two families in `D` are braided iff they have the same finite sum or both have infinite
support and the same rank sum.

For a Dedekind domain `R` with `G = Pic R`, Steinitz's theorem identifies `V(R)` with `D`; that
identification, and hence `V^κ(R) ≅ E_κ`, is module theory and is *not* formalised here.
-/
import KappaMonoid.Examples.NatBraiding
import KappaMonoid.ForMathlib.CardinalSum
import KappaMonoid.ForMathlib.Finprod
import KappaMonoid.Braiding.WellOrder
import KappaMonoid.Braiding.UnivAux
import KappaMonoid.Braiding.Prop310

universe u v w t

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid

namespace Dedekind


/-! ## The monoid `D`

`V(R)` of a Dedekind domain `R` with class group `G = Pic R` is, by Steinitz's theorem, the monoid
`D = {0} ∪ (ℕ_{≥1} × G)`; its elements are the pairs `(rank, class)`.  Steinitz's theorem is
classical module theory and is *not* formalised here: this file works with `D` directly. -/

variable {G : Type w} [AddCommGroup G]

/-- **Examples 4.8(4)**: the monoid `D = {(n, g) ∈ ℕ₀ × G : n ≥ 1 or g = 0}`, which is `V(R)` for
a Dedekind domain `R` with `Pic R = G` by Steinitz's theorem (not formalised). -/
def dedMonoid (G : Type w) [AddCommGroup G] : AddSubmonoid (ℕ × G) where
  carrier := {p | 1 ≤ p.1 ∨ p.2 = 0}
  add_mem' := by
    rintro ⟨a, g⟩ ⟨b, h⟩ ha hb
    simp only [Set.mem_ofPred_eq, Prod.mk_add_mk] at ha hb ⊢
    rcases ha with ha | ha
    · exact Or.inl (by omega)
    · rcases hb with hb | hb
      · exact Or.inl (by omega)
      · exact Or.inr (by rw [ha, hb, add_zero])
  zero_mem' := Or.inr rfl

/-- The rank `D → ℕ₀`. -/
def rk : dedMonoid G →+ ℕ := (AddMonoidHom.fst ℕ G).comp (dedMonoid G).subtype

/-- The class `D → G`. -/
def gp : dedMonoid G →+ G := (AddMonoidHom.snd ℕ G).comp (dedMonoid G).subtype

theorem rk_apply (d : dedMonoid G) : rk d = (d : ℕ × G).1 := rfl

theorem gp_apply (d : dedMonoid G) : gp d = (d : ℕ × G).2 := rfl

theorem one_le_rk_or (d : dedMonoid G) : 1 ≤ rk d ∨ gp d = 0 := d.2

theorem dedMonoid_ext {d e : dedMonoid G} (h1 : rk d = rk e) (h2 : gp d = gp e) : d = e :=
  Subtype.ext (Prod.ext h1 h2)

/-- `D` is reduced in the strong sense that an element of rank `0` is `0`. -/
theorem rk_eq_zero_iff {d : dedMonoid G} : rk d = 0 ↔ d = 0 := by
  refine ⟨fun h => dedMonoid_ext (h.trans (map_zero rk).symm) ?_, fun h => h ▸ map_zero rk⟩
  rcases one_le_rk_or d with hd | hd
  · omega
  · exact hd.trans (map_zero gp).symm

theorem support_rk {ι : Type u} (x : ι → dedMonoid G) :
    support (fun i => rk (x i)) = support x := by
  ext i
  simp only [Function.mem_support, ne_eq, rk_eq_zero_iff]

/-! ## Examples 4.8(4)(a): braiding in `D` -/

/-- Two finitely supported families in `D` with the same sum are braided. -/
theorem isBraided_of_finite_support {ι : Type u} (x y : ι → dedMonoid G)
    (hx : (support x).Finite) (hy : (support y).Finite) (hsum : ∑ᶠ i, x i = ∑ᶠ i, y i) :
    letI : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
    IsBraided ℵ₀ x y := by
  let : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
  have hx' : #(support x) < ℵ₀ := Cardinal.lt_aleph0_iff_set_finite.mpr hx
  have hy' : #(support y) < ℵ₀ := Cardinal.lt_aleph0_iff_set_finite.mpr hy
  refine isBraided_of_small_support x y hx' hy' ?_
  rw [LMonoid.lsumOf_eq_finsum hx' x, LMonoid.lsumOf_eq_finsum hy' y,
    finsum_mem_support, finsum_mem_support]
  exact hsum

/-! ### The countable case

The construction is the one for `ℕ₀` (`isBraided_nat_of_infinite_support`) run on the ranks,
with the class group along for the ride.  The observation that makes it work is the paper's:
`(n, g)` is a summand of `(m, h)` whenever `1 ≤ n < m`, the complement being `(m - n, h - g)`.
So a finite interval of one family whose rank sum *exceeds* the rank of the deficit carried over
from the other family absorbs that deficit, whatever its class, and leaves a deficit of rank
`≥ 1` — which is again a legitimate element of `D`. -/

/-- The complement of `v` in `a`, when `rk v < rk a` (and `0` otherwise, a junk value). -/
noncomputable def dsub (a v : dedMonoid G) : dedMonoid G :=
  if h : rk v < rk a then
    ⟨((a : ℕ × G).1 - (v : ℕ × G).1, (a : ℕ × G).2 - (v : ℕ × G).2),
      Or.inl (by rw [rk_apply, rk_apply] at h; omega)⟩
  else 0

theorem dsub_spec {a v : dedMonoid G} (h : rk v < rk a) : v + dsub a v = a := by
  rw [dsub, dif_pos h]
  rw [rk_apply, rk_apply] at h
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show (v : ℕ × G).1 + ((a : ℕ × G).1 - (v : ℕ × G).1) = (a : ℕ × G).1
    omega
  · show (v : ℕ × G).2 + ((a : ℕ × G).2 - (v : ℕ × G).2) = (a : ℕ × G).2
    abel

theorem one_le_rk_of_mem_support {x : ℕ → dedMonoid G} {i : ℕ} (hi : i ∈ support x) :
    1 ≤ rk (x i) :=
  Nat.one_le_iff_ne_zero.mpr fun h => hi (rk_eq_zero_iff.mp h)

/-- The recursive state `(bI, bJ, v)` of the construction: the right-hand ends of the intervals
built so far along `x` and along `y`, and the deficit carried over to the next interval of `x`. -/
noncomputable def braidState (x y : ℕ → dedMonoid G) (hx : (support x).Infinite)
    (hy : (support y).Infinite) : ℕ → ℕ × ℕ × dedMonoid G
  | 0 => (0, 0, 0)
  | (k + 1) =>
      let s := braidState x y hx hy k
      let bI' := (exists_ico_dominates hx (fun i => rk (x i))
        (fun _ hi => one_le_rk_of_mem_support hi) s.1 (rk s.2.2 + 1)).choose
      let u := dsub (∑ i ∈ Finset.Ico s.1 bI', x i) s.2.2
      let bJ' := (exists_ico_dominates hy (fun i => rk (y i))
        (fun _ hi => one_le_rk_of_mem_support hi) s.2.1 (rk u + 1)).choose
      (bI', bJ', dsub (∑ i ∈ Finset.Ico s.2.1 bJ', y i) u)

section State

variable (x y : ℕ → dedMonoid G) (hx : (support x).Infinite) (hy : (support y).Infinite)

/-- The `x`-boundaries. -/
noncomputable def bI (k : ℕ) : ℕ := (braidState x y hx hy k).1

/-- The `y`-boundaries. -/
noncomputable def bJ (k : ℕ) : ℕ := (braidState x y hx hy k).2.1

/-- The deficits carried from `y` to `x`: the braiding family `v`. -/
noncomputable def bv (k : ℕ) : dedMonoid G := (braidState x y hx hy k).2.2

/-- The deficits carried from `x` to `y`: the braiding family `u`. -/
noncomputable def bu (k : ℕ) : dedMonoid G :=
  dsub (∑ i ∈ Finset.Ico (bI x y hx hy k) (bI x y hx hy (k + 1)), x i) (bv x y hx hy k)

theorem bI_succ_spec (k : ℕ) :
    bI x y hx hy k < bI x y hx hy (k + 1) ∧
      rk (bv x y hx hy k) + 1 ≤
        ∑ i ∈ Finset.Ico (bI x y hx hy k) (bI x y hx hy (k + 1)), rk (x i) :=
  (exists_ico_dominates hx (fun i => rk (x i)) (fun _ hi => one_le_rk_of_mem_support hi)
    (bI x y hx hy k) (rk (bv x y hx hy k) + 1)).choose_spec

theorem bJ_succ_spec (k : ℕ) :
    bJ x y hx hy k < bJ x y hx hy (k + 1) ∧
      rk (bu x y hx hy k) + 1 ≤
        ∑ i ∈ Finset.Ico (bJ x y hx hy k) (bJ x y hx hy (k + 1)), rk (y i) :=
  (exists_ico_dominates hy (fun i => rk (y i)) (fun _ hi => one_le_rk_of_mem_support hi)
    (bJ x y hx hy k) (rk (bu x y hx hy k) + 1)).choose_spec

theorem bI_sum_eq (k : ℕ) :
    ∑ i ∈ Finset.Ico (bI x y hx hy k) (bI x y hx hy (k + 1)), x i =
      bv x y hx hy k + bu x y hx hy k := by
  refine Eq.symm (dsub_spec ?_)
  rw [map_sum]
  have := (bI_succ_spec x y hx hy k).2
  omega

theorem bJ_sum_eq (k : ℕ) :
    ∑ i ∈ Finset.Ico (bJ x y hx hy k) (bJ x y hx hy (k + 1)), y i =
      bv x y hx hy (k + 1) + bu x y hx hy k := by
  have hv : bv x y hx hy (k + 1) =
      dsub (∑ i ∈ Finset.Ico (bJ x y hx hy k) (bJ x y hx hy (k + 1)), y i) (bu x y hx hy k) :=
    rfl
  rw [hv, add_comm (dsub _ _)]
  refine Eq.symm (dsub_spec ?_)
  rw [map_sum]
  have := (bJ_succ_spec x y hx hy k).2
  omega

end State

/-- **Examples 4.8(4)**, the countable case: two families in `D` with infinite support, indexed
by a countable type, are braided. -/
theorem isBraided_of_infinite_support_countable {ι : Type u} (hι : #ι ≤ ℵ₀)
    (x y : ι → dedMonoid G) (hx : (support x).Infinite) (hy : (support y).Infinite) :
    letI : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
    IsBraided ℵ₀ x y := by
  let : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
  classical
  have hιInf : Infinite ι := by
    rcases finite_or_infinite ι with hfin | hinf
    · exact absurd (Set.toFinite (support x)) hx
    · exact hinf
  obtain ⟨φ⟩ := Cardinal.nonempty_equiv_nat_of_le_aleph0 hι hιInf
  have hsupp : ∀ z : ι → dedMonoid G, (support z).Infinite → (support (z ∘ φ)).Infinite := by
    intro z hz hfin
    rw [Function.support_comp_eq_preimage] at hfin
    apply hz
    rw [← Set.image_preimage_eq (support z) φ.surjective]
    exact hfin.image _
  have hx3 := hsupp x hx
  have hy3 := hsupp y hy
  exact IsBraided.of_nat_blocks φ (bI _ _ hx3 hy3) (bJ _ _ hx3 hy3)
    (strictMono_nat_of_lt_succ fun k => (bI_succ_spec _ _ hx3 hy3 k).1)
    (strictMono_nat_of_lt_succ fun k => (bJ_succ_spec _ _ hx3 hy3 k).1)
    rfl rfl (bu _ _ hx3 hy3) (bv _ _ hx3 hy3) rfl
    (bI_sum_eq _ _ hx3 hy3) (bJ_sum_eq _ _ hx3 hy3)

/-- The countable case inside an arbitrary index type: two families in `D` with countably
infinite supports are braided.  Pad the countable braiding by zeros (`isBraided_of_subtype`). -/
theorem isBraided_of_countable_support {ι : Type u} (x y : ι → dedMonoid G)
    (hxc : #(support x) ≤ ℵ₀) (hyc : #(support y) ≤ ℵ₀)
    (hx : (support x).Infinite) (hy : (support y).Infinite) :
    letI : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
    IsBraided ℵ₀ x y := by
  let : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
  set C : Set ι := support x ∪ support y with hCdef
  have hC : #C ≤ ℵ₀ :=
    (Cardinal.mk_union_le _ _).trans ((add_le_add hxc hyc).trans Cardinal.aleph0_add_aleph0.le)
  refine isBraided_of_subtype C (fun i hi => ?_) (fun i hi => ?_) ?_
  · by_contra h
    exact hi (Or.inl h)
  · by_contra h
    exact hi (Or.inr h)
  · have hinf : ∀ z : ι → dedMonoid G, support z ⊆ C → (support z).Infinite →
        (support fun c : C => z c).Infinite := by
      intro z hzC hz hfin
      apply hz
      refine (hfin.image Subtype.val).subset fun i hi => ⟨⟨i, hzC hi⟩, hi, rfl⟩
    exact isBraided_of_infinite_support_countable hC _ _
      (hinf x Set.subset_union_left hx) (hinf y Set.subset_union_right hy)

/-! ### The general case: a disjoint union of countable braidings -/

open scoped Classical in
/-- The block map attached to `τ : S × ℕ ≃ Q`: an element of `Q` goes to the name, in `S`, of its
block; any other index to itself. -/
noncomputable def blockMap {ι : Type u} {S Q : Set ι} (τ : S × ULift.{u} ℕ ≃ Q) (j : ι) : ι :=
  if h : j ∈ Q then ((τ.symm ⟨j, h⟩).1 : ι) else j

theorem blockMap_preimage_inter_of_mem {ι : Type u} {S Q : Set ι} (τ : S × ULift.{u} ℕ ≃ Q)
    {l : ι} (hl : l ∈ S) :
    blockMap τ ⁻¹' {l} ∩ Q = Set.range (fun n : ULift.{u} ℕ => (τ (⟨l, hl⟩, n) : ι)) := by
  ext j
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro ⟨hj, hjQ⟩
    rw [blockMap, dif_pos hjQ] at hj
    refine ⟨(τ.symm ⟨j, hjQ⟩).2, ?_⟩
    have he : ((⟨l, hl⟩ : S), (τ.symm ⟨j, hjQ⟩).2) = τ.symm ⟨j, hjQ⟩ :=
      Prod.ext (Subtype.ext hj.symm) rfl
    rw [he, Equiv.apply_symm_apply]
  · rintro ⟨n, rfl⟩
    refine ⟨?_, (τ (⟨l, hl⟩, n)).2⟩
    rw [blockMap, dif_pos (τ (⟨l, hl⟩, n)).2, Subtype.coe_eta, Equiv.symm_apply_apply]

theorem blockMap_preimage_inter_of_notMem {ι : Type u} {S Q : Set ι} (τ : S × ULift.{u} ℕ ≃ Q)
    {l : ι} (hl : l ∉ S) : blockMap τ ⁻¹' {l} ∩ Q = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun j ⟨hj, hjQ⟩ => hl ?_
  have hj' : blockMap τ j = l := hj
  rw [blockMap, dif_pos hjQ] at hj'
  exact hj' ▸ (τ.symm ⟨j, hjQ⟩).1.2

/-- **Examples 4.8(4)**, the substantive half of (a): two families in `D` with infinite supports
of the same cardinality are braided, over any index type.

Paper proof: "this follows inductively from the observation that `(n, g)` is always a summand of
`(m, h)` if `1 ≤ n < m`".  Here: cut both supports into the same number `#supp x = #supp y` of
countably infinite blocks, braid corresponding blocks by the countable construction, and assemble
the block braidings by Lemma 3.4(3) (`isBraided_of_blocks`). -/
theorem isBraided_of_infinite_support {ι : Type u} (x y : ι → dedMonoid G)
    (hx : (support x).Infinite) (hxy : #(support x) = #(support y)) :
    letI : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
    IsBraided ℵ₀ x y := by
  let : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
  classical
  have hinfS : ℵ₀ ≤ #(support x) := Cardinal.infinite_iff.mp hx.to_subtype
  have : Infinite (support x) := hx.to_subtype
  have : Infinite ι := Infinite.of_injective (Subtype.val : support x → ι) Subtype.val_injective
  have hprod : #(support x × ULift.{u} ℕ) = #(support x) := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_uLift, Cardinal.mk_nat,
      Cardinal.lift_aleph0, Cardinal.mul_aleph0_eq hinfS]
  obtain ⟨σ⟩ := Cardinal.eq.mp hprod
  obtain ⟨τ⟩ := Cardinal.eq.mp (hprod.trans hxy)
  have hdisj : ∀ (f : ι → ι) (l l' : ι), l ≠ l' → Disjoint (f ⁻¹' {l}) (f ⁻¹' {l'}) :=
    fun f l l' hll' => Set.disjoint_left.mpr fun i hi hi' =>
      hll' ((show f i = l from hi).symm.trans hi')
  have hcov : ∀ f : ι → ι, (⋃ l, f ⁻¹' {l}) = Set.univ :=
    fun f => Set.eq_univ_of_forall fun i => Set.mem_iUnion.mpr ⟨f i, rfl⟩
  -- the support of a block
  have hblock : ∀ (z : ι → dedMonoid G) (ρ : support x × ULift.{u} ℕ ≃ support z) (l : ι),
      support (Set.indicator (blockMap ρ ⁻¹' {l}) z) = blockMap ρ ⁻¹' {l} ∩ support z :=
    fun z ρ l => Set.support_indicator
  have hcount : ∀ (z : ι → dedMonoid G) (ρ : support x × ULift.{u} ℕ ≃ support z) (l : ι)
      (hl : l ∈ support x),
      #(support (Set.indicator (blockMap ρ ⁻¹' {l}) z)) = ℵ₀ := by
    intro z ρ l hl
    rw [hblock, blockMap_preimage_inter_of_mem ρ hl, Cardinal.mk_range_eq, Cardinal.mk_uLift,
      Cardinal.mk_nat, Cardinal.lift_aleph0]
    intro a b hab
    have := ρ.injective (Subtype.ext hab)
    exact (Prod.ext_iff.mp this).2
  refine isBraided_of_blocks (A := fun l => blockMap σ ⁻¹' {l}) (B := fun l => blockMap τ ⁻¹' {l})
    (hdisj _) (hdisj _) (hcov _) (hcov _) fun l => ?_
  by_cases hl : l ∈ support x
  · have hσ := hcount x σ l hl
    have hτ := hcount y τ l hl
    exact isBraided_of_countable_support _ _ hσ.le hτ.le
      (Set.infinite_coe_iff.mp (Cardinal.infinite_iff.mpr hσ.ge))
      (Set.infinite_coe_iff.mp (Cardinal.infinite_iff.mpr hτ.ge))
  · have h1 : Set.indicator (blockMap σ ⁻¹' {l}) x = 0 :=
      Function.support_eq_empty_iff.mp (by rw [hblock, blockMap_preimage_inter_of_notMem σ hl])
    have h2 : Set.indicator (blockMap τ ⁻¹' {l}) y = 0 :=
      Function.support_eq_empty_iff.mp (by rw [hblock, blockMap_preimage_inter_of_notMem τ hl])
    rw [h1, h2]

/-! ## The `κ`-monoid `E_κ` -/

variable {κ : Cardinal.{u}}

/-- **Examples 4.8(4)**: `E_κ = {(α, g) ∈ F_κ × G : 1 ≤ α < ℵ₀ or g = 0}`. -/
def dedExt (κ : Cardinal.{u}) (G : Type w) [AddCommGroup G] : Set (Fcard κ × G) :=
  {p | ((1 : Cardinal.{u}) ≤ (p.1 : Cardinal.{u}) ∧ (p.1 : Cardinal.{u}) < ℵ₀) ∨ p.2 = 0}

theorem mem_dedExt {p : Fcard κ × G} :
    p ∈ dedExt κ G ↔
      ((1 : Cardinal.{u}) ≤ (p.1 : Cardinal.{u}) ∧ (p.1 : Cardinal.{u}) < ℵ₀) ∨ p.2 = 0 :=
  Iff.rfl

/-- The rank of an element of `E_κ`, a cardinal `≤ κ`. -/
def erk (a : dedExt κ G) : Cardinal.{u} := ((a : Fcard κ × G).1 : Cardinal.{u})

/-- The class of an element of `E_κ`. -/
def egp (a : dedExt κ G) : G := (a : Fcard κ × G).2

theorem dedExt_ext {a b : dedExt κ G} (h1 : erk a = erk b) (h2 : egp a = egp b) : a = b :=
  Subtype.ext (Prod.ext (Subtype.ext h1) h2)

theorem egp_eq_zero_of_erk_eq_zero {a : dedExt κ G} (h : erk a = 0) : egp a = 0 := by
  rcases mem_dedExt.mp a.2 with h' | h'
  · have h1 : (1 : Cardinal.{u}) ≤ 0 := h ▸ h'.1
    exact absurd h1 (not_le.mpr zero_lt_one)
  · exact h'

theorem egp_eq_zero_of_not_lt {a : dedExt κ G} (h : ¬ erk a < ℵ₀) : egp a = 0 := by
  rcases mem_dedExt.mp a.2 with h' | h'
  · exact absurd h'.2 h
  · exact h'

theorem esum_mem {ι : Type u} (z : ι → dedExt κ G) (c : Fcard κ)
    (hc : (c : Cardinal.{u}) = Cardinal.sum fun i => erk (z i)) :
    (c, if (Cardinal.sum fun i => erk (z i)) < ℵ₀ then ∑ᶠ i, egp (z i) else 0) ∈ dedExt κ G := by
  rw [mem_dedExt]
  split_ifs with hlt
  · by_cases h0 : (Cardinal.sum fun i => erk (z i)) = 0
    · refine Or.inr (finsum_eq_zero_of_forall_eq_zero fun i => egp_eq_zero_of_erk_eq_zero ?_)
      exact nonpos_iff_eq_zero.mp ((Cardinal.le_sum (fun i => erk (z i)) i).trans h0.le)
    · exact Or.inl ⟨hc ▸ Cardinal.one_le_iff_ne_zero.mpr h0, hc ▸ hlt⟩
  · exact Or.inr rfl

/-- The summation of `E_κ`: ranks add as cardinals; classes add when the total rank is finite (the
family then has finite support), and are forgotten otherwise. -/
noncomputable def esum (hκ : ℵ₀ ≤ κ) {ι : Type u} (h : #ι < Order.succ κ) (z : ι → dedExt κ G) :
    dedExt κ G :=
  ⟨(⟨Cardinal.sum fun i => erk (z i),
      Cardinal.sum_lt_of_isRegular (Cardinal.isRegular_succ hκ) h fun i => (z i).1.1.2⟩,
    if (Cardinal.sum fun i => erk (z i)) < ℵ₀ then ∑ᶠ i, egp (z i) else 0), esum_mem z _ rfl⟩

theorem erk_esum (hκ : ℵ₀ ≤ κ) {ι : Type u} (h : #ι < Order.succ κ) (z : ι → dedExt κ G) :
    erk (esum hκ h z) = Cardinal.sum fun i => erk (z i) := rfl

theorem egp_esum (hκ : ℵ₀ ≤ κ) {ι : Type u} (h : #ι < Order.succ κ) (z : ι → dedExt κ G) :
    egp (esum hκ h z) =
      if (Cardinal.sum fun i => erk (z i)) < ℵ₀ then ∑ᶠ i, egp (z i) else 0 := rfl

/-- The summation data of `E_κ`. -/
noncomputable def sumData (hκ : ℵ₀ ≤ κ) : SumData (Order.succ κ) (dedExt κ G) where
  isRegular := Cardinal.isRegular_succ hκ
  sum := esum hκ
  sum_congr h h' e z := by
    have hr : (Cardinal.sum fun i => erk ((z ∘ e) i)) = Cardinal.sum fun i => erk (z i) :=
      csum_congr e (fun i => erk (z i))
    refine dedExt_ext hr ?_
    rw [egp_esum, egp_esum, hr]
    split_ifs
    · exact finsum_comp_equiv e (f := fun i => egp (z i))
    · rfl
  sum_unique h z := by
    have hr : (Cardinal.sum fun i => erk (z i)) = erk (z default) := csum_unique _
    refine dedExt_ext hr ?_
    rw [egp_esum, hr]
    split_ifs with hlt
    · exact finsum_unique _
    · exact (egp_eq_zero_of_not_lt hlt).symm
  sum_sigma {ι ρ} h hρ z hσ := by
    have hr : (Cardinal.sum fun i => erk (esum hκ (hρ i) (z i)))
        = Cardinal.sum fun p : (Σ i, ρ i) => erk (z p.1 p.2) :=
      csum_sigma (fun i j => erk (z i j))
    refine dedExt_ext hr ?_
    rw [egp_esum, egp_esum, hr]
    split_ifs with hlt
    · have hrow : ∀ i, (Cardinal.sum fun j => erk (z i j)) < ℵ₀ := fun i =>
        lt_of_le_of_lt (Cardinal.le_sum (fun i => erk (esum hκ (hρ i) (z i))) i)
          (by rw [hr]; exact hlt)
      have hegp : ∀ i, egp (esum hκ (hρ i) (z i)) = ∑ᶠ j, egp (z i j) := fun i => by
        rw [egp_esum, if_pos (hrow i)]
      rw [finsum_congr hegp]
      have hfin : (support fun p : (Σ i, ρ i) => egp (z p.1 p.2)).Finite := by
        have hsub : (support fun p : (Σ i, ρ i) => egp (z p.1 p.2))
            ⊆ support fun p : (Σ i, ρ i) => erk (z p.1 p.2) :=
          fun p hp h0 => hp (egp_eq_zero_of_erk_eq_zero h0)
        exact (Cardinal.lt_aleph0_iff_set_finite.mp
          ((Cardinal.mk_support_le_sum _).trans_lt hlt)).subset hsub
      exact finsum_sigma_eq (fun p : (Σ i, ρ i) => egp (z p.1 p.2)) hfin
    · rfl

/-- **Examples 4.8(4)**: `E_κ` is a `κ`-monoid, with `Σ (αᵢ, gᵢ) = (Σ αᵢ, Σ gᵢ)` if `Σ αᵢ` is
finite and `(Σ αᵢ, 0)` otherwise.

The paper takes this structure for granted.  The only axiom needing an argument is associativity
(A2): if the total rank is finite, so is every row's, only finitely many entries are nonzero (an
entry of rank `0` is `0`), and the classes add up by `finsum_sigma_eq`; otherwise both sides forget
the class. -/
@[instance_reducible]
noncomputable def instKMonoid (hκ : ℵ₀ ≤ κ) : KMonoid κ (dedExt κ G) where
  toLMonoid := (sumData hκ).toLMonoid
  aleph0_le := hκ

theorem erk_sumOf (hκ : ℵ₀ ≤ κ) {ι : Type u} (h : #ι ≤ κ) (z : ι → dedExt κ G) :
    letI := instKMonoid (G := G) hκ
    erk (KMonoid.sumOf (κ := κ) h z) = Cardinal.sum fun i => erk (z i) := rfl

theorem egp_sumOf (hκ : ℵ₀ ≤ κ) {ι : Type u} (h : #ι ≤ κ) (z : ι → dedExt κ G) :
    letI := instKMonoid (G := G) hκ
    egp (KMonoid.sumOf (κ := κ) h z) =
      if (Cardinal.sum fun i => erk (z i)) < ℵ₀ then ∑ᶠ i, egp (z i) else 0 := rfl

theorem erk_zero (hκ : ℵ₀ ≤ κ) :
    letI := instKMonoid (G := G) hκ
    erk (0 : dedExt κ G) = 0 :=
  csum_isEmpty (fun i : PEmpty.{u + 1} => erk (PEmpty.elim i : dedExt κ G))

theorem egp_zero (hκ : ℵ₀ ≤ κ) :
    letI := instKMonoid (G := G) hκ
    egp (0 : dedExt κ G) = 0 := by
  let := instKMonoid (G := G) hκ
  show (if (Cardinal.sum fun i : PEmpty.{u + 1} => erk (PEmpty.elim i : dedExt κ G)) < ℵ₀ then
      ∑ᶠ i : PEmpty.{u + 1}, egp (PEmpty.elim i : dedExt κ G) else 0) = 0
  split_ifs
  · exact finsum_of_isEmpty _
  · rfl

/-! ## The inclusion `D ↪ E_κ` -/

theorem incl_mem (hκ : ℵ₀ ≤ κ) (d : dedMonoid G) :
    (Fcard.mk ((rk d : ℕ) : Cardinal.{u}) (Cardinal.natCast_lt_aleph0.le.trans hκ), gp d)
      ∈ dedExt κ G := by
  rcases one_le_rk_or d with h | h
  · refine Or.inl ⟨?_, Cardinal.natCast_lt_aleph0⟩
    show (1 : Cardinal.{u}) ≤ ((rk d : ℕ) : Cardinal.{u})
    exact_mod_cast h
  · exact Or.inr h

/-- The inclusion `D ↪ E_κ`, `(n, g) ↦ (n, g)`. -/
def incl (hκ : ℵ₀ ≤ κ) (d : dedMonoid G) : dedExt κ G :=
  ⟨(Fcard.mk ((rk d : ℕ) : Cardinal.{u}) (Cardinal.natCast_lt_aleph0.le.trans hκ), gp d),
    incl_mem hκ d⟩

theorem erk_incl (hκ : ℵ₀ ≤ κ) (d : dedMonoid G) : erk (incl hκ d) = ((rk d : ℕ) : Cardinal.{u}) :=
  rfl

theorem egp_incl (hκ : ℵ₀ ≤ κ) (d : dedMonoid G) : egp (incl hκ d) = gp d := rfl

theorem incl_zero (hκ : ℵ₀ ≤ κ) :
    letI := instKMonoid (G := G) hκ
    incl hκ (0 : dedMonoid G) = 0 := by
  let := instKMonoid (G := G) hκ
  refine dedExt_ext ?_ ?_
  · rw [erk_incl, erk_zero, map_zero, Nat.cast_zero]
  · rw [egp_incl, egp_zero, map_zero]

/-- **Examples 4.8(4)**: the inclusion `D → E_κ` is an `ℵ₀⁻`-homomorphism. -/
theorem isLHom_incl (hκ : ℵ₀ ≤ κ) :
    letI : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
    letI := instKMonoid (G := G) hκ
    LMonoid.IsLHom (hκ.trans (Order.le_succ κ)) (incl (G := G) hκ) := by
  let : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
  let := instKMonoid (G := G) hκ
  refine ⟨incl_zero hκ, fun {ι} h x => ?_⟩
  have : Finite ι := Cardinal.lt_aleph0_iff_finite.mp h
  let : Fintype ι := Fintype.ofFinite ι
  rw [LMonoid.lsumOf_aleph0_eq_finsum h x]
  refine dedExt_ext ?_ ?_
  · show ((rk (∑ i, x i) : ℕ) : Cardinal.{u}) =
      Cardinal.sum fun i => ((rk (x i) : ℕ) : Cardinal.{u})
    rw [map_sum, Cardinal.sum_natCast_fintype]
  · show gp (∑ i, x i) =
      if (Cardinal.sum fun i => ((rk (x i) : ℕ) : Cardinal.{u})) < ℵ₀ then ∑ᶠ i, gp (x i) else 0
    rw [Cardinal.sum_natCast_fintype, if_pos Cardinal.natCast_lt_aleph0, map_sum,
      finsum_eq_sum_of_fintype]

theorem incl_injective (hκ : ℵ₀ ≤ κ) : Function.Injective (incl (G := G) hκ) := by
  intro a b hab
  refine dedMonoid_ext ?_ ?_
  · have h := congrArg erk hab
    rw [erk_incl, erk_incl] at h
    exact_mod_cast h
  · have h := congrArg egp hab
    rwa [egp_incl, egp_incl] at h

/-- Equal sums in `E_κ` of two families in `D`: equal finite sums, or infinite supports and equal
rank sums. -/
theorem cond_of_sumOf_eq (hκ : ℵ₀ ≤ κ) {ι : Type u} (hι : #ι ≤ κ) (x y : ι → dedMonoid G)
    (h : letI := instKMonoid (G := G) hκ
      KMonoid.sumOf (κ := κ) hι (fun i => incl hκ (x i))
        = KMonoid.sumOf (κ := κ) hι (fun i => incl hκ (y i))) :
    ((support x).Finite ∧ (support y).Finite ∧ ∑ᶠ i, x i = ∑ᶠ i, y i) ∨
      ((support x).Infinite ∧ (support y).Infinite ∧
        Cardinal.sum (fun i => ((rk (x i) : ℕ) : Cardinal.{u}))
          = Cardinal.sum (fun i => ((rk (y i) : ℕ) : Cardinal.{u}))) := by
  let := instKMonoid (G := G) hκ
  have hr : Cardinal.sum (fun i => ((rk (x i) : ℕ) : Cardinal.{u}))
      = Cardinal.sum (fun i => ((rk (y i) : ℕ) : Cardinal.{u})) := congrArg erk h
  have hg : (if Cardinal.sum (fun i => ((rk (x i) : ℕ) : Cardinal.{u})) < ℵ₀ then
        ∑ᶠ i, gp (x i) else 0)
      = (if Cardinal.sum (fun i => ((rk (y i) : ℕ) : Cardinal.{u})) < ℵ₀ then
        ∑ᶠ i, gp (y i) else 0) := congrArg egp h
  have hfin : ∀ z : ι → dedMonoid G, (support z).Finite →
      Cardinal.sum (fun i => ((rk (z i) : ℕ) : Cardinal.{u})) = ((∑ᶠ i, rk (z i) : ℕ) : Cardinal) :=
    fun z hz => Cardinal.sum_natCast_of_finite _ (by rwa [support_rk])
  have hinf : ∀ z : ι → dedMonoid G, (support z).Infinite →
      Cardinal.sum (fun i => ((rk (z i) : ℕ) : Cardinal.{u})) = #(support z) := fun z hz => by
    rw [Cardinal.sum_natCast_of_infinite _ (by rwa [support_rk]), support_rk]
  have hbig : ∀ z : ι → dedMonoid G, (support z).Infinite → ℵ₀ ≤ #(support z) :=
    fun z hz => Cardinal.infinite_iff.mp hz.to_subtype
  by_cases hfx : (support x).Finite <;> by_cases hfy : (support y).Finite
  · refine Or.inl ⟨hfx, hfy, ?_⟩
    rw [hfin x hfx, hfin y hfy] at hr hg
    rw [if_pos Cardinal.natCast_lt_aleph0, if_pos Cardinal.natCast_lt_aleph0] at hg
    have hr' : ∑ᶠ i, rk (x i) = ∑ᶠ i, rk (y i) := by exact_mod_cast hr
    refine dedMonoid_ext ?_ ?_
    · rw [map_finsum rk hfx, map_finsum rk hfy]
      exact hr'
    · rw [map_finsum gp hfx, map_finsum gp hfy]
      exact hg
  · exfalso
    rw [hfin x hfx, hinf y hfy] at hr
    exact absurd (hr ▸ Cardinal.natCast_lt_aleph0) (not_lt.mpr (hbig y hfy))
  · exfalso
    rw [hinf x hfx, hfin y hfy] at hr
    exact absurd (hr.symm ▸ Cardinal.natCast_lt_aleph0) (not_lt.mpr (hbig x hfx))
  · exact Or.inr ⟨hfx, hfy, hr⟩

theorem isBraided_of_cond {ι : Type u} (x y : ι → dedMonoid G)
    (h : ((support x).Finite ∧ (support y).Finite ∧ ∑ᶠ i, x i = ∑ᶠ i, y i) ∨
      ((support x).Infinite ∧ (support y).Infinite ∧
        Cardinal.sum (fun i => ((rk (x i) : ℕ) : Cardinal.{u}))
          = Cardinal.sum (fun i => ((rk (y i) : ℕ) : Cardinal.{u})))) :
    letI : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
    IsBraided ℵ₀ x y := by
  rcases h with ⟨hx, hy, hs⟩ | ⟨hx, hy, hs⟩
  · exact isBraided_of_finite_support x y hx hy hs
  · rw [Cardinal.sum_natCast_of_infinite _ (by rwa [support_rk]),
      Cardinal.sum_natCast_of_infinite _ (by rwa [support_rk]), support_rk, support_rk] at hs
    exact isBraided_of_infinite_support x y hx hs

/-- **Examples 4.8(4)(a)**: two families in `D` are braided iff either both have finite support
and the same sum, or both have infinite support and their ranks add up to the same cardinal
(which is then the common cardinality of the supports, `Cardinal.sum_natCast_of_infinite`).  The index type
is arbitrary.

Paper proof: "it is easy to check that two families with infinite support over `V(R)` are braided
if and only if their ranks add up to the same cardinal; this follows inductively from the
observation that `(n, g)` is always a summand of `(m, h)` if `1 ≤ n < m`."  Backwards this is
`isBraided_of_finite_support` and `isBraided_of_infinite_support`; forwards, a braiding is carried
by the `ℵ₀⁻`-homomorphism `D → E_κ` (for any `κ ≥ #ι`) to families with equal `κ`-sums, whose
ranks and classes can be read off. -/
theorem isBraided_iff {ι : Type u} (x y : ι → dedMonoid G) :
    letI : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
    IsBraided ℵ₀ x y ↔
      (((support x).Finite ∧ (support y).Finite ∧ ∑ᶠ i, x i = ∑ᶠ i, y i) ∨
        ((support x).Infinite ∧ (support y).Infinite ∧
          Cardinal.sum (fun i => ((rk (x i) : ℕ) : Cardinal.{u}))
            = Cardinal.sum (fun i => ((rk (y i) : ℕ) : Cardinal.{u})))) := by
  let : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
  refine ⟨fun h => ?_, isBraided_of_cond x y⟩
  have hκ : ℵ₀ ≤ max ℵ₀ #ι := le_max_left _ _
  let := instKMonoid (G := G) hκ
  have hι : #ι ≤ max ℵ₀ #ι := le_max_right _ _
  exact cond_of_sumOf_eq hκ hι x y
    (sumOf_map_eq_of_isBraided (hκ.trans (Order.le_succ _)) (isLHom_incl hκ) hι h)

/-- **Examples 4.8(4)**: `E_κ` is `ℵ₀⁻`-braided over `D`, along `(n, g) ↦ (n, g)`, for every
infinite `κ`.

Paper proof: two families with infinite support over `D` are braided iff their ranks add up to the
same cardinal, which is exactly when their sums in `E_κ` agree; finitely supported families with
equal sums are braided in any case.  Here: the inclusion is an `ℵ₀⁻`-homomorphism
(`isLHom_incl`) and injective; an element `(n, g)` of finite rank is the image of a one-term family,
and `(α, 0)` with `α ≥ ℵ₀` is the `κ`-sum of `α` copies of `(1, 0)`; and equal `κ`-sums in `E_κ`
give the condition of `isBraided_iff` (`cond_of_sumOf_eq`), hence a braiding
(`isBraided_of_cond`). -/
theorem isBraidedOver_dedExt (hκ : ℵ₀ ≤ κ) :
    letI : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
    letI := instKMonoid (G := G) hκ
    IsBraidedOver (ℵ₀ : Cardinal.{u}) κ (dedMonoid G) (dedExt κ G) (hκ.trans (Order.le_succ κ))
      (incl hκ) := by
  let : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
  let := instKMonoid (G := G) hκ
  classical
  refine ⟨isLHom_incl hκ, incl_injective hκ, fun h => ?_, fun x y hxy =>
    isBraided_of_cond x y (cond_of_sumOf_eq hκ (le_of_eq (mk_Idx κ)) x y hxy)⟩
  by_cases hlt : erk h < ℵ₀
  · -- a finite element is a one-term sum
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hlt
    have hmem : ((n, egp h) : ℕ × G) ∈ dedMonoid G := by
      rcases mem_dedExt.mp h.2 with h' | h'
      · refine Or.inl ?_
        have h1 : (1 : Cardinal.{u}) ≤ (n : Cardinal.{u}) := hn ▸ h'.1
        exact_mod_cast h1
      · exact Or.inr h'
    obtain ⟨i₀⟩ := nonempty_Idx hκ
    refine ⟨fun i => if i = i₀ then ⟨(n, egp h), hmem⟩ else 0, ?_⟩
    rw [KMonoid.ksum_single i₀ _ fun i hi => by simp only [if_neg hi]; exact incl_zero hκ]
    show h = incl hκ (if i₀ = i₀ then ⟨(n, egp h), hmem⟩ else 0)
    rw [if_pos rfl]
    exact dedExt_ext hn rfl
  · -- an infinite element is a sum of `erk h` copies of `(1, 0)`
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.mp
      (show erk h ≤ #(Idx κ) from (mk_Idx κ).symm ▸ Fcard.le _)
    let one : dedMonoid G := ⟨(1, 0), Or.inl le_rfl⟩
    have hsupp : support (fun i => rk (if i ∈ s then one else 0)) = s := by
      ext i
      by_cases hi : i ∈ s
      · simp only [Function.mem_support, hi, iff_true, ↓reduceIte]
        exact one_ne_zero
      · simp only [Function.mem_support, hi, iff_false, not_not, ↓reduceIte, map_zero]
    have hsinf : (support fun i => rk (if i ∈ s then one else 0)).Infinite := by
      rw [hsupp]
      exact Set.infinite_coe_iff.mp (Cardinal.infinite_iff.mpr (hs ▸ not_lt.mp hlt))
    have hr : Cardinal.sum (fun i => ((rk (if i ∈ s then one else 0) : ℕ) : Cardinal.{u}))
        = erk h := by
      rw [Cardinal.sum_natCast_of_infinite _ hsinf, hsupp, hs]
    refine ⟨fun i => if i ∈ s then one else 0, dedExt_ext hr.symm ?_⟩
    show egp h = if Cardinal.sum (fun i => ((rk (if i ∈ s then one else 0) : ℕ) : Cardinal.{u}))
        < ℵ₀ then _ else 0
    rw [hr, if_neg hlt]
    exact egp_eq_zero_of_not_lt hlt

/-- **Examples 4.8(4)**: the universal `κ`-extension of `D` is
`E_κ = {(α, g) ∈ F_κ × G : 1 ≤ α < ℵ₀ or g = 0}`, for every infinite `κ`.

Paper proof: `E_κ` is braided over `D` (`isBraidedOver_dedExt`), so Theorem 3.12(2) identifies it
as `D̂`.  For a Dedekind domain `R` with `Pic R = G` the paper concludes
`V^κ(R) = V(R)^ ≅ E_κ`; that step needs Steinitz's theorem (`V(R) ≅ D`) and the fact that
projective modules over a hereditary ring are direct sums of finitely generated ones, and neither
is formalised: this is the monoid-theoretic half only. -/
theorem isUniversalKExtension_dedExt (hκ : ℵ₀ ≤ κ) :
    letI : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
    letI := instKMonoid (G := G) hκ
    IsUniversalKExtension.{u, w, max (u + 1) w, t} (ℵ₀ : Cardinal.{u}) κ (dedMonoid G)
      (dedExt κ G) (hκ.trans (Order.le_succ κ)) (incl hκ) := by
  let : LMonoid (ℵ₀ : Cardinal.{u}) (dedMonoid G) := LMonoid.ofAddCommMonoid _
  let := instKMonoid (G := G) hκ
  exact (isBraidedOver_dedExt hκ).isUniversalKExtension (hκ.trans (Order.le_succ κ))

end Dedekind

end KappaMonoid
