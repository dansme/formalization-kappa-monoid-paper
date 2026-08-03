/-
Examples 2.3 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

The `κ`-monoid `V^κ(C)` of Examples 2.3(4) is built in `KappaMonoid/Modules.lean`; this file
contains the other three examples, none of which is a monoid of modules:

* 2.3(3) `Fcard κ`, the cardinals bounded by `κ`, with cardinal summation.  This is also the
  `κ`-monoid `F_κ` underlying the free `κ`-monoids of §2.1.
* 2.3(1) the *trivial `κ`-extension* `M ⊎ {∞}` of a reduced commutative monoid `M`, where a
  family sums to its finite sum if it has finite support inside `M`, and to `∞` otherwise.
* 2.3(2) `ℝ≥0 ∪ {∞} = ℝ≥0∞`, with `Σ` the sum of the series.
-/
import KappaMonoid.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

universe u v

open Cardinal Function Set
open scoped Classical

namespace KappaMonoid

/-! ## Cardinal summation

Three facts about `Cardinal.sum` matching the three axioms of `SumData`.  `Cardinal.sum f` is by
definition `#(Σ i, (f i).out)`, so each is an isomorphism of sigma types. -/

/-- Cardinal summation is invariant under reindexing. -/
theorem csum_congr {ι ι' : Type u} (e : ι ≃ ι') (f : ι' → Cardinal.{u}) :
    Cardinal.sum (f ∘ e) = Cardinal.sum f :=
  Cardinal.mk_sigma_congr e fun _ => rfl

/-- A cardinal sum over a one-point index type is its unique entry. -/
theorem csum_unique {ι : Type u} [Unique ι] (f : ι → Cardinal.{u}) :
    Cardinal.sum f = f default := by
  rw [show f = (fun _ : ι => f default) from funext fun i => by rw [Unique.eq_default i],
    Cardinal.sum_const' ι (f default), Cardinal.mk_eq_one ι, one_mul]

/-- Cardinal summation is associative over sigma types. -/
theorem csum_sigma {ι : Type u} {ρ : ι → Type u} (x : ∀ i, ρ i → Cardinal.{u}) :
    Cardinal.sum (fun i => Cardinal.sum (x i)) = Cardinal.sum fun p : (i : ι) × ρ i => x p.1 p.2 := by
  have hrow : ∀ i, #((Cardinal.sum (x i)).out) = #((j : ρ i) × (x i j).out) := by
    intro i
    rw [Cardinal.mk_out, Cardinal.mk_sigma]
    exact congrArg _ (funext fun j => (Cardinal.mk_out _).symm)
  calc Cardinal.sum (fun i => Cardinal.sum (x i))
      = #((i : ι) × (j : ρ i) × (x i j).out) := Cardinal.mk_sigma_congrRight hrow
    _ = Cardinal.sum fun p : (i : ι) × ρ i => x p.1 p.2 :=
        Cardinal.mk_congr (Equiv.sigmaAssoc (fun (i : ι) (j : ρ i) => (x i j).out)).symm

/-- A cardinal sum over a two-point index type is a sum of cardinals. -/
theorem csum_pair (α β : Cardinal.{u}) :
    Cardinal.sum (Sum.elim (fun _ : PUnit.{u + 1} => α) (fun _ : PUnit.{u + 1} => β)) = α + β := by
  have h1 : Cardinal.sum (Sum.elim (fun _ : PUnit.{u + 1} => α) (fun _ : PUnit.{u + 1} => β))
      = #((_ : PUnit.{u + 1}) × α.out ⊕ (_ : PUnit.{u + 1}) × β.out) :=
    Cardinal.mk_congr (Equiv.sumSigmaDistrib _)
  rw [h1, Cardinal.mk_sum, Cardinal.mk_sigma, Cardinal.mk_sigma, csum_unique, csum_unique,
    Cardinal.mk_out, Cardinal.mk_out, Cardinal.lift_id, Cardinal.lift_id]

/-- An empty cardinal sum is `0`. -/
theorem csum_isEmpty {ι : Type u} [IsEmpty ι] (f : ι → Cardinal.{u}) : Cardinal.sum f = 0 := by
  have : IsEmpty ((i : ι) × (f i).out) := ⟨fun q => IsEmpty.false q.1⟩
  exact Cardinal.mk_eq_zero _

/-- A `≤ κ`-indexed sum of cardinals `≤ κ` is `≤ κ`. -/
theorem csum_le_of_le {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) {ι : Type u} (hι : #ι ≤ κ)
    {f : ι → Cardinal.{u}} (hf : ∀ i, f i ≤ κ) : Cardinal.sum f ≤ κ :=
  calc Cardinal.sum f ≤ Cardinal.sum (fun _ : ι => κ) := Cardinal.sum_le_sum _ _ hf
    _ = #ι * κ := Cardinal.sum_const' ι κ
    _ ≤ κ * κ := mul_le_mul' hι le_rfl
    _ = κ := Cardinal.mul_eq_self hκ

/-! ## Examples 2.3(3): the cardinals bounded by `κ` -/

/-- `F_κ`, the `κ`-monoid of all cardinals `≤ κ` (Examples 2.3(3)). -/
abbrev Fcard (κ : Cardinal.{u}) : Type (u + 1) := {α : Cardinal.{u} // α ≤ κ}

namespace Fcard

variable {κ : Cardinal.{u}}

instance : Zero (Fcard κ) := ⟨⟨0, zero_le⟩⟩

@[simp] theorem val_zero : ((0 : Fcard κ) : Cardinal.{u}) = 0 := rfl

theorem ext {a b : Fcard κ} (h : (a : Cardinal.{u}) = b) : a = b := Subtype.ext h

/-- The summation data on `F_κ`: cardinal summation, which stays `≤ κ` by `csum_le_of_le`. -/
noncomputable def sumData (hκ : ℵ₀ ≤ κ) : SumData (Order.succ κ) (Fcard κ) where
  isRegular := Cardinal.isRegular_succ hκ
  sum {ι} h x :=
    ⟨Cardinal.sum fun i => (x i : Cardinal.{u}),
      csum_le_of_le hκ (KMonoid.le_of_lt_succ h) fun i => (x i).2⟩
  sum_congr _ _ e x := ext (csum_congr e fun i => (x i : Cardinal.{u}))
  sum_unique _ x := ext (csum_unique fun i => (x i : Cardinal.{u}))
  sum_sigma _ _ x _ := ext (csum_sigma fun i j => (x i j : Cardinal.{u}))

theorem sumData_zero (hκ : ℵ₀ ≤ κ) : (sumData hκ).zero = 0 := ext (csum_isEmpty _)

/-- **Examples 2.3(3)**: the cardinals `≤ κ` form a `κ`-monoid. -/
@[instance_reducible]
noncomputable def instKMonoid (hκ : ℵ₀ ≤ κ) : KMonoid κ (Fcard κ) where
  toLMonoid := (sumData hκ).toLMonoidOfZero (sumData_zero hκ)
  aleph0_le := hκ

/-- The `κ`-sum on `F_κ` is cardinal summation. -/
@[simp] theorem instKMonoid_sumOf (hκ : ℵ₀ ≤ κ) {ι : Type u} (h : #ι ≤ κ) (x : ι → Fcard κ) :
    letI := instKMonoid hκ
    ((KMonoid.sumOf (κ := κ) h x : Fcard κ) : Cardinal.{u})
      = Cardinal.sum fun i => (x i : Cardinal.{u}) := rfl

/-- Addition on `F_κ` is addition of cardinals. -/
theorem instKMonoid_add (hκ : ℵ₀ ≤ κ) (a b : Fcard κ) :
    letI := instKMonoid hκ
    ((a + b : Fcard κ) : Cardinal.{u}) = (a : Cardinal.{u}) + b := by
  letI := instKMonoid hκ
  have hu : #PUnit.{u + 1} ≤ κ := KMonoid.mk_le_of_finite (H := Fcard κ) _
  have hPP : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) ≤ κ := KMonoid.mk_sum_le (H := Fcard κ) hu hu
  rw [LMonoid.add_eq_lsumOf (lam := Order.succ κ) (KMonoid.lt_succ hPP) a b]
  show Cardinal.sum (fun p : PUnit.{u + 1} ⊕ PUnit.{u + 1} =>
      ((Sum.elim (fun _ => a) (fun _ => b) p : Fcard κ) : Cardinal.{u}))
    = (a : Cardinal.{u}) + b
  rw [show (fun p : PUnit.{u + 1} ⊕ PUnit.{u + 1} =>
        ((Sum.elim (fun _ => a) (fun _ => b) p : Fcard κ) : Cardinal.{u}))
      = Sum.elim (fun _ => (a : Cardinal.{u})) (fun _ => (b : Cardinal.{u})) from
    funext fun p => by rcases p with p | p <;> rfl]
  exact csum_pair _ _

end Fcard

/-! ## Examples 2.3(1): the trivial `κ`-extension of a reduced commutative monoid

For a *reduced* commutative monoid `M`, the set `M ⊎ {∞} = WithTop M` becomes a `κ`-monoid for
every infinite `κ`: a family sums to its finite sum if it is finitely supported with all entries
in `M`, and to `∞` otherwise.  Reducedness enters exactly once, in (A2): without it a row of the
double family could have nonzero entries but zero sum, and then the outer family could be
finitely supported while the double family is not. -/

namespace TrivExt

variable {M : Type v} [AddCommMonoid M]

/-- A finite sum in a reduced monoid vanishes only if all its terms do. -/
theorem conical_finset_sum_eq_zero (hM : IsConical M) {ι : Type u} (f : ι → M)
    (s : Finset ι) (h : ∑ i ∈ s, f i = 0) : ∀ i ∈ s, f i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro i hi; exact absurd hi (Finset.notMem_empty i)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha] at h
      obtain ⟨h1, h2⟩ := hM _ _ h
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h1
      · exact ih h2 i hi

theorem conical_finsum_eq_zero (hM : IsConical M) {ι : Type u} {f : ι → M}
    (hfin : (Function.support f).Finite) (h : ∑ᶠ i, f i = 0) (i : ι) : f i = 0 := by
  classical
  by_cases hi : f i = 0
  · exact hi
  · rw [finsum_eq_sum f hfin] at h
    exact conical_finset_sum_eq_zero hM f _ h i (by rw [Set.Finite.mem_toFinset]; exact hi)

/-- Reducedness passes to `M ⊎ {∞}`. -/
theorem isConical_withTop (hM : IsConical M) : IsConical (WithTop M) := by
  intro a b hab
  have ha : a ≠ ⊤ := fun h => by simp [h] at hab
  have hb : b ≠ ⊤ := fun h => by simp [h] at hab
  lift a to M using ha with a'
  lift b to M using hb with b'
  rw [← WithTop.coe_add] at hab
  obtain ⟨h1, h2⟩ := hM a' b' (by exact_mod_cast hab)
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- The underlying family in `M`, with `∞` sent to `0`. -/
noncomputable def down (x : ι → WithTop M) (i : ι) : M := WithTop.untopD 0 (x i)

theorem down_eq_zero_iff {x : ι → WithTop M} {i : ι} (h : x i ≠ ⊤) : down x i = 0 ↔ x i = 0 := by
  lift x i to M using h with a ha
  simp [down, ← ha]

theorem support_down {x : ι → WithTop M} (h : ∀ i, x i ≠ ⊤) :
    Function.support (down x) = Function.support x := by
  ext i
  simp only [Function.mem_support, ne_eq, down_eq_zero_iff (h i)]

/-- The summation of the trivial `κ`-extension. -/
noncomputable def sigma (x : ι → WithTop M) : WithTop M :=
  if (Function.support x).Finite ∧ ∀ i, x i ≠ ⊤ then ((∑ᶠ i, down x i : M) : WithTop M) else ⊤

theorem sigma_of_good {x : ι → WithTop M} (h1 : (Function.support x).Finite)
    (h2 : ∀ i, x i ≠ ⊤) : sigma x = ((∑ᶠ i, down x i : M) : WithTop M) := by
  unfold sigma; rw [if_pos ⟨h1, h2⟩]

theorem sigma_of_bad {x : ι → WithTop M} (h : ¬((Function.support x).Finite ∧ ∀ i, x i ≠ ⊤)) :
    sigma x = ⊤ := by
  unfold sigma; rw [if_neg h]

theorem sigma_ne_top {x : ι → WithTop M} (h1 : (Function.support x).Finite)
    (h2 : ∀ i, x i ≠ ⊤) : sigma x ≠ ⊤ := by
  rw [sigma_of_good h1 h2]; exact WithTop.coe_ne_top

theorem sigma_eq_zero_iff {x : ι → WithTop M} (h1 : (Function.support x).Finite)
    (h2 : ∀ i, x i ≠ ⊤) : sigma x = 0 ↔ (∑ᶠ i, down x i : M) = 0 := by
  rw [sigma_of_good h1 h2]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

theorem coe_down {x : ι → WithTop M} {i : ι} (h : x i ≠ ⊤) :
    ((down x i : M) : WithTop M) = x i := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp h
  rw [down, ← ha, WithTop.untopD_coe]

theorem sigma_comp_equiv {ι ι' : Type u} (e : ι ≃ ι') (x : ι' → WithTop M) :
    sigma (x ∘ e) = sigma x := by
  have hsupp : Function.support (x ∘ e) = e ⁻¹' Function.support x := rfl
  have htop : (∀ i, (x ∘ e) i ≠ ⊤) ↔ ∀ i', x i' ≠ ⊤ :=
    ⟨fun h i' => by rw [← e.apply_symm_apply i']; exact h (e.symm i'), fun h i => h (e i)⟩
  by_cases hgood : (Function.support x).Finite ∧ ∀ i', x i' ≠ ⊤
  · rw [sigma_of_good hgood.1 hgood.2, sigma_of_good (by
      rw [hsupp]; exact hgood.1.preimage e.injective.injOn) (htop.mpr hgood.2)]
    refine congrArg _ ?_
    show (∑ᶠ i, down x (e i)) = ∑ᶠ i', down x i'
    exact finsum_comp_equiv e
  · rw [sigma_of_bad hgood, sigma_of_bad ?_]
    rintro ⟨h1, h2⟩
    refine hgood ⟨?_, htop.mp h2⟩
    rw [hsupp] at h1
    have := h1.image e
    rwa [Set.image_preimage_eq _ e.surjective] at this

theorem sigma_eq_top_of_top {x : ι → WithTop M} {i₀ : ι} (h : x i₀ = ⊤) : sigma x = ⊤ :=
  sigma_of_bad fun hg => hg.2 i₀ h

theorem sigma_eq_top_of_infinite {x : ι → WithTop M} (h : ¬(Function.support x).Finite) :
    sigma x = ⊤ := sigma_of_bad fun hg => h hg.1

/-- (A1) for the trivial `κ`-extension. -/
theorem sigma_single {ι : Type u} (i₀ : ι) (x : ι → WithTop M) (hx : ∀ i, i ≠ i₀ → x i = 0) :
    sigma x = x i₀ := by
  have hsupp : Function.support x ⊆ {i₀} := by
    intro i hi
    by_contra hne
    exact hi (hx i hne)
  have hfin : (Function.support x).Finite := (Set.finite_singleton i₀).subset hsupp
  by_cases htop : x i₀ = ⊤
  · rw [sigma_eq_top_of_top htop, htop]
  · have h2 : ∀ i, x i ≠ ⊤ := by
      intro i
      by_cases hi : i = i₀
      · rw [hi]; exact htop
      · rw [hx i hi]; exact WithTop.coe_ne_top
    rw [sigma_of_good hfin h2,
      finsum_eq_single (down x) i₀ fun i hi => by rw [down, hx i hi]; rfl, coe_down htop]

/-- (A2) for the trivial `κ`-extension.  This is the only place reducedness of `M` is used. -/
theorem sigma_prod (hM : IsConical M) {ι ι' : Type u} (y : ι × ι' → WithTop M) :
    sigma (fun i => sigma fun j => y (i, j)) = sigma y := by
  by_cases htop : ∃ p, y p = ⊤
  · obtain ⟨⟨i, j⟩, hij⟩ := htop
    rw [sigma_eq_top_of_top hij,
      sigma_eq_top_of_top (i₀ := i) (sigma_eq_top_of_top (i₀ := j) hij)]
  · push Not at htop
    by_cases hfin : (Function.support y).Finite
    -- the good case: both sides are the finite sum, by `finsum_curry`
    · have hrowfin : ∀ i, (Function.support fun j => y (i, j)).Finite := by
        intro i
        have : (Function.support fun j => y (i, j)) = (fun j => (i, j)) ⁻¹' Function.support y := rfl
        rw [this]
        exact hfin.preimage (fun a _ b _ h => (Prod.ext_iff.mp h).2)
      have hrow : ∀ i, sigma (fun j => y (i, j))
          = ((∑ᶠ j, down (fun j => y (i, j)) j : M) : WithTop M) :=
        fun i => sigma_of_good (hrowfin i) fun j => htop (i, j)
      have houtfin : (Function.support fun i => sigma fun j => y (i, j)).Finite := by
        refine (hfin.image Prod.fst).subset fun i hi => ?_
        by_contra hni
        refine hi ?_
        have hzero : ∀ j, y (i, j) = 0 := by
          intro j
          by_contra hj
          exact hni ⟨(i, j), hj, rfl⟩
        show sigma (fun j => y (i, j)) = 0
        rw [hrow i, show (fun j => down (fun j => y (i, j)) j) = fun _ => (0 : M) from
          funext fun j => by rw [down, hzero j]; rfl, finsum_zero]
        rfl
      have houttop : ∀ i, (fun i => sigma fun j => y (i, j)) i ≠ ⊤ := by
        intro i
        show sigma (fun j => y (i, j)) ≠ ⊤
        rw [hrow i]
        exact WithTop.coe_ne_top
      rw [sigma_of_good houtfin houttop, sigma_of_good hfin htop]
      refine congrArg _ ?_
      have hfin' : Function.HasFiniteSupport (down y) := by
        show (Function.support (down y)).Finite
        rw [support_down htop]
        exact hfin
      have hdown : ∀ i, down (fun i => sigma fun j => y (i, j)) i = ∑ᶠ j, down y (i, j) := by
        intro i
        show WithTop.untopD 0 (sigma (fun j => y (i, j))) = _
        rw [hrow i, WithTop.untopD_coe]
        rfl
      rw [show (fun i => down (fun i => sigma fun j => y (i, j)) i)
          = fun i => ∑ᶠ j, down y (i, j) from funext hdown]
      exact (finsum_curry (down y) hfin').symm
    -- the bad case: the double family is not finitely supported, so both sides are `⊤`
    · rw [sigma_eq_top_of_infinite hfin]
      by_cases hrow : ∀ i, (Function.support fun j => y (i, j)).Finite
      · -- every row is finite, so infinitely many rows are nonzero; reducedness makes their
        -- sums nonzero, so the outer family is not finitely supported either
        have hrowdown : ∀ i, (Function.support (down fun j => y (i, j))).Finite := fun i => by
          rw [support_down fun j => htop (i, j)]
          exact hrow i
        refine sigma_eq_top_of_infinite fun hout => hfin ?_
        have hcover : Function.support y ⊆
            ⋃ i ∈ Function.support (fun i => sigma fun j => y (i, j)),
              (fun j => (i, j)) '' Function.support (fun j => y (i, j)) := by
          rintro ⟨i, j⟩ hij
          refine Set.mem_biUnion (show i ∈ Function.support _ from ?_) ⟨j, hij, rfl⟩
          have hne : (∑ᶠ j, down (fun j => y (i, j)) j : M) ≠ 0 := by
            intro hsum
            refine hij ?_
            have h0 := conical_finsum_eq_zero hM (hrowdown i) hsum j
            rw [show down (fun j => y (i, j)) j = down y (i, j) from rfl] at h0
            rwa [down_eq_zero_iff (htop (i, j))] at h0
          rw [Function.mem_support, sigma_of_good (hrow i) fun j => htop (i, j)]
          exact fun hc => hne (by exact_mod_cast hc)
        exact (hout.biUnion fun i _ => (hrow i).image _).subset hcover
      · obtain ⟨i, hi⟩ := not_forall.mp hrow
        exact sigma_eq_top_of_top (i₀ := i) (sigma_eq_top_of_infinite hi)

/-- The binary sum: `Σ` of a family supported on two indices. -/
theorem sigma_two {ι : Type u} [DecidableEq ι] (a b : WithTop M) {i₀ i₁ : ι} (hne : i₀ ≠ i₁) :
    sigma (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b := by
  set x : ι → WithTop M := fun i => if i = i₀ then a else if i = i₁ then b else 0 with hxdef
  have hx0 : x i₀ = a := if_pos rfl
  have hx1 : x i₁ = b := by rw [hxdef]; simp [hne.symm]
  have hsupp : Function.support x ⊆ {i₀, i₁} := by
    intro i hi
    by_contra hni
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hni
    exact hi (by rw [hxdef]; simp [hni.1, hni.2])
  have hfin : (Function.support x).Finite :=
    ((Set.finite_singleton i₁).insert i₀).subset hsupp
  by_cases htop : a = ⊤ ∨ b = ⊤
  · rcases htop with h | h
    · rw [sigma_eq_top_of_top (i₀ := i₀) (by rw [hx0, h]), h, WithTop.top_add]
    · rw [sigma_eq_top_of_top (i₀ := i₁) (by rw [hx1, h]), h, WithTop.add_top]
  · push Not at htop
    have h2 : ∀ i, x i ≠ ⊤ := by
      intro i
      by_cases hi0 : i = i₀
      · rw [hi0, hx0]; exact htop.1
      · by_cases hi1 : i = i₁
        · rw [hi1, hx1]; exact htop.2
        · rw [hxdef]; simp only [if_neg hi0, if_neg hi1]; exact WithTop.coe_ne_top
    rw [sigma_of_good hfin h2]
    have hpair : (∑ᶠ i, down x i) = down x i₀ + down x i₁ := by
      have hsupp' : ∀ i ∈ Function.support (down x),
          i ∈ (Set.univ : Set ι) ↔ i ∈ ({i₀, i₁} : Set ι) := by
        intro i hi
        refine ⟨fun _ => ?_, fun _ => Set.mem_univ i⟩
        by_contra hcon
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
        refine hi ?_
        rw [down, hxdef]
        simp only [if_neg hcon.1, if_neg hcon.2]
        rfl
      rw [← finsum_mem_univ (down x),
        finsum_mem_inter_support_eq' (down x) Set.univ {i₀, i₁} hsupp', finsum_mem_pair hne]
    rw [hpair, WithTop.coe_add, coe_down (h2 i₀), coe_down (h2 i₁), hx0, hx1]



/-- **Examples 2.3(1)**: for a reduced commutative monoid `M`, the *trivial `κ`-extension*
`M ⊎ {∞}` is a `κ`-monoid, for every infinite `κ`. -/
@[instance_reducible]
noncomputable def instKMonoid {κ : Cardinal.{u}} (hM : IsConical M) (hκ : ℵ₀ ≤ κ) :
    KMonoid κ (WithTop M) :=
  KMonoid.ofKsum
    { aleph0_le := hκ
      ksum := sigma
      ksum_single := fun i₀ x hx => sigma_single i₀ x hx
      ksum_sigma := fun x π => by
        rw [sigma_prod hM (fun p : Idx κ × Idx κ => x p.1 p.2),
          ← sigma_comp_equiv π.symm (fun p : Idx κ × Idx κ => x p.1 p.2)]
        rfl }
    fun a b i₀ i₁ hne => show sigma _ = a + b from sigma_two a b hne

/-- The `κ`-sum of the trivial extension is the finite sum, or `∞`. -/
@[simp] theorem instKMonoid_ksum {κ : Cardinal.{u}} (hM : IsConical M) (hκ : ℵ₀ ≤ κ)
    (x : Idx κ → WithTop M) :
    letI := instKMonoid hM hκ
    KMonoid.ksum (κ := κ) x = sigma x :=
  KMonoid.ofKsum_ksum _ _ _

/-- The paper's remark that reducedness of `M` is *necessary*: a commutative monoid that embeds
additively into any `κ`-monoid is reduced, so for non-reduced `M` there is no `κ`-monoid structure
on `M ⊎ {∞}` extending the addition of `M`.  (The paper argues directly with an alternating family
`a, -a, a, -a, …`; here it is immediate from Lemma 2.8(1), that every `κ`-monoid is reduced.) -/
theorem isConical_of_injective_kMonoid {κ : Cardinal.{u}} {H : Type w} [KMonoid κ H] (f : M → H)
    (hf : Function.Injective f) (h0 : f 0 = 0) (hadd : ∀ a b, f (a + b) = f a + f b) :
    IsConical M := by
  letI : LMonoid (ℵ₀ : Cardinal.{u}) M := LMonoid.ofAddCommMonoid M
  exact LMonoid.isConical_of_injective (lam := ℵ₀) (κ := κ) f hf h0 hadd

end TrivExt

/-! ## Examples 2.3(2): the extended nonnegative reals

`ℝ≥0∞` is an `ℵ₀`-monoid with `Σ` the sum of the series.  Since every family in `ℝ≥0∞` is
summable, `tsum` satisfies the axioms outright; the additive monoid is the existing one, so this
is built with `SumData.toLMonoid'` rather than `toLMonoidOfZero`. -/

namespace ENNRealExample

open ENNReal

/-- `Σ` on `ℝ≥0∞`: the sum of the family as a series. -/
noncomputable def sumData : SumData (Order.succ ℵ₀) ENNReal where
  isRegular := Cardinal.isRegular_succ le_rfl
  sum _ x := ∑' i, x i
  sum_congr _ _ e x := e.tsum_eq x
  sum_unique := fun {ι} _ _ x => by
    letI : Fintype ι := Unique.fintype
    rw [tsum_fintype]
    exact Fintype.sum_unique x
  sum_sigma _ _ x _ := (ENNReal.tsum_sigma x).symm

theorem sumData_add (h : #(PUnit.{1} ⊕ PUnit.{1}) < Order.succ ℵ₀) (a b : ENNReal) :
    a + b = sumData.sum h (Sum.elim (fun _ => a) (fun _ => b)) := by
  show a + b = ∑' p : PUnit.{1} ⊕ PUnit.{1}, Sum.elim (fun _ => a) (fun _ => b) p
  rw [tsum_fintype, Fintype.sum_sum_type]
  simp

/-- **Examples 2.3(2)**: `ℝ≥0∞` is an `ℵ₀`-monoid, with its usual addition. -/
@[instance_reducible]
noncomputable def instKMonoid : KMonoid ℵ₀ ENNReal where
  toLMonoid := sumData.toLMonoid' sumData_add
  aleph0_le := le_rfl

/-- The `ℵ₀`-sum on `ℝ≥0∞` is the sum of the series. -/
@[simp] theorem instKMonoid_sumOf {ι : Type} (h : #ι ≤ ℵ₀) (x : ι → ENNReal) :
    letI := instKMonoid
    KMonoid.sumOf (κ := ℵ₀) h x = ∑' i, x i := rfl

/-- The operation differs from the trivial `ℵ₀`-extension of `ℝ≥0` (Examples 2.3(1)): a family
with infinite support can have a finite sum. -/
theorem exists_infinite_support_sum_ne_top :
    ∃ x : ℕ → ENNReal, (Function.support x).Infinite ∧ ∑' i, x i ≠ ⊤ := by
  refine ⟨fun n => (2 : ENNReal)⁻¹ ^ n, ?_, ?_⟩
  · have hsupp : Function.support (fun n : ℕ => (2 : ENNReal)⁻¹ ^ n) = Set.univ := by
      ext n
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact pow_ne_zero n (by simp)
    rw [hsupp]
    exact Set.infinite_univ
  · rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (by simp)

end ENNRealExample

end KappaMonoid
