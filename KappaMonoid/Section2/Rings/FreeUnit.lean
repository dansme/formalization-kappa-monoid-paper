/-
Section 2.3 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*,

preparation for Proposition 2.16: the class of `R^{(s)}` in `V^κ(𝓕^κ)` depends only on `#s`,
and — for a nontrivial ring — determines `#s` when that is infinite.  The latter is invariance
of infinite rank (axiom A1) once more, and is what makes `[R]` a *faithful* order-unit.
-/
import KappaMonoid.Section2.Rings.FreeModules
import KappaMonoid.Section2.Rings.ProjOrderUnit

universe u

open Cardinal Function Set DirectSum
open scoped Classical

namespace KappaMonoid

namespace FreeMod

variable {R : Type u} [Ring R]

/-! ## The standard generators of a free module -/

/-- The standard generators span `R^{(ι)}`.  This is `freeMod_span` for an arbitrary index. -/
theorem span_range_lof (ι : Type u) :
    Submodule.span R (Set.range fun i : ι => (lof R ι (fun _ => R) i 1 : ⨁ _ : ι, R)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  rw [← DirectSum.sum_support_of x]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : (of (fun _ : ι => R) k) (x k) = (x k) • (lof R ι (fun _ => R) k 1) := by
    rw [← lof_eq_of R, ← LinearMap.map_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  rw [hk]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-! ## Invariance of infinite rank, for `R^{(ι)}` -/

/-- If `R^{(ι)} ≅ R^{(ι')}` and `ι` is infinite then `#ι ≤ #ι'`: the standard generators of
`R^{(ι')}` map onto a spanning set of `R^{(ι)}`, and axiom A1 bounds the rank by it. -/
theorem mk_le_of_equiv [Nontrivial R] {ι ι' : Type u} [Infinite ι]
    (e : (⨁ _ : ι, R) ≃ₗ[R] (⨁ _ : ι', R)) : #ι ≤ #ι' :=
  le_trans
    (Projective.mk_le_of_surjective R (e.symm : (⨁ _ : ι', R) →ₗ[R] (⨁ _ : ι, R))
      e.symm.surjective (span_range_lof ι'))
    Cardinal.mk_range_le

/-- Free modules of infinite rank determine their rank. -/
theorem mk_eq_of_equiv [Nontrivial R] {ι ι' : Type u} [Infinite ι]
    (e : (⨁ _ : ι, R) ≃ₗ[R] (⨁ _ : ι', R)) : #ι = #ι' := by
  have h1 : #ι ≤ #ι' := mk_le_of_equiv e
  haveI : Infinite ι' :=
    Cardinal.infinite_iff.mpr ((Cardinal.infinite_iff.mp ‹Infinite ι›).trans h1)
  exact le_antisymm h1 (mk_le_of_equiv e.symm)

/-! ## Classes of free modules and their ranks -/

variable {κ : Cardinal.{u}}

/-- The class of `R^{(s)}` depends only on `#s`. -/
theorem mk_eq_mk_of_mk_eq {s t : Set (Idx κ)} (h : #s = #t) : (mk s : Carrier R κ) = mk t :=
  mk_eq_mk.mpr ⟨DirectSum.lequivCongrLeft R (Cardinal.eq.mp h).some⟩

/-- Conversely, for a nontrivial ring an infinite rank is determined by the class. -/
theorem mk_eq_of_mk_eq_mk [Nontrivial R] {s t : Set (Idx κ)} (hs : ℵ₀ ≤ #s)
    (h : (mk s : Carrier R κ) = mk t) : #s = #t := by
  haveI : Infinite ↥s := Cardinal.infinite_iff.mpr hs
  exact mk_eq_of_equiv (mk_eq_mk.mp h).some

theorem mk_le_kappa (s : Set (Idx κ)) : #s ≤ κ :=
  le_of_le_of_eq (Cardinal.mk_le_mk_of_subset (Set.subset_univ _))
    (by rw [Cardinal.mk_univ, mk_Idx])

/-- A subset of `Idx κ` of any prescribed cardinality `≤ κ`. -/
noncomputable def setOfCard {γ : Cardinal.{u}} (hγ : γ ≤ κ) : Set (Idx κ) :=
  Set.range (emb (le_of_eq_of_le (mk_Idx γ) hγ))

@[simp] theorem mk_setOfCard {γ : Cardinal.{u}} (hγ : γ ≤ κ) : #(setOfCard hγ) = γ := by
  rw [setOfCard, Cardinal.mk_range_eq _ (emb (le_of_eq_of_le (mk_Idx γ) hγ)).injective, mk_Idx]

/-! ## `[R]` is a cyclic faithful order-unit

Classes are stated at the type `(freeClass R κ hκ).carrier` rather than at `Carrier R κ`.  The
two are definitionally equal, but `freeClass` is not reducible, and instance search works at
reducible transparency, so it only finds the module structures on `ModuleClass.rep` for the
first form. -/

variable (R κ)

/-- The class of `R^{(s)}`, at the type instance search wants. -/
noncomputable def mkC (hκ : ℵ₀ ≤ κ) (s : Set (Idx κ)) : (freeClass R κ hκ).carrier := mk s

/-- **The class of `R`** in `V^κ(𝓕^κ)`: the free module on one generator. -/
noncomputable def unit (hκ : ℵ₀ ≤ κ) (k : Idx κ) : (freeClass R κ hκ).carrier :=
  mkC R κ hκ ({k} : Set (Idx κ))

variable {R κ}

theorem mkC_eq_mkC_iff (hκ : ℵ₀ ≤ κ) {s t : Set (Idx κ)} :
    mkC R κ hκ s = mkC R κ hκ t ↔ Nonempty (ofSet R κ s ≃ₗ[R] ofSet R κ t) := mk_eq_mk

theorem mkC_eq_mkC_of_mk_eq (hκ : ℵ₀ ≤ κ) {s t : Set (Idx κ)} (h : #s = #t) :
    mkC R κ hκ s = mkC R κ hκ t := mk_eq_mk_of_mk_eq h

theorem mk_eq_of_mkC_eq [Nontrivial R] (hκ : ℵ₀ ≤ κ) {s t : Set (Idx κ)} (hs : ℵ₀ ≤ #s)
    (h : mkC R κ hκ s = mkC R κ hκ t) : #s = #t := mk_eq_of_mk_eq_mk hs h

@[simp] theorem mkC_basis (hκ : ℵ₀ ≤ κ) (a : (freeClass R κ hκ).carrier) :
    mkC R κ hκ (basis a) = a := mk_basis a

/-- The representative of the class of `R^{(s)}` is `R^{(s)}`. -/
theorem rep_mkC (hκ : ℵ₀ ≤ κ) (s : Set (Idx κ)) :
    Nonempty ((freeClass R κ hκ).rep (mkC R κ hκ s) ≃ₗ[R] ⨁ _ : s, R) := basis_mk_equiv s

/-- The representative of `[R]` is `R`. -/
theorem rep_unit (hκ : ℵ₀ ≤ κ) (k : Idx κ) :
    Nonempty ((freeClass R κ hκ).rep (unit R κ hκ k) ≃ₗ[R] R) := by
  letI : Unique ↥({k} : Set (Idx κ)) := Set.uniqueSingleton k
  exact ⟨(rep_mkC hκ ({k} : Set (Idx κ))).some.trans
    (directSumEquivOfSubsingleton R (fun _ : ({k} : Set (Idx κ)) => R)
      ⟨k, Set.mem_singleton k⟩ fun i hi => absurd (Subsingleton.elim i _) hi)⟩

/-- `α` copies of `[R]` is the class of a free module of rank `α`. -/
theorem cmul_unit (hκ : ℵ₀ ≤ κ) (k : Idx κ) {α : Cardinal.{u}} (hα : α ≤ κ) {s : Set (Idx κ)}
    (hs : #s = α) :
    letI := (freeClass R κ hκ).instKMonoid hκ
    KMonoid.cmul (κ := κ) α hα (unit R κ hκ k) = mkC R κ hκ s := by
  letI := (freeClass R κ hκ).instKMonoid hκ
  refine (freeClass R κ hκ).eq_of_iso ?_
  have hL := (freeClass R κ hκ).rep_sumOf hκ (le_of_eq_of_le (mk_Idx α) hα)
    (fun _ : Idx α => unit R κ hκ k)
  have hidx : Nonempty (Idx α ≃ ↥s) := Cardinal.eq.mp ((mk_Idx α).trans hs.symm)
  exact ((hL.some.trans (DirectSum.congrLinearEquiv fun _ => (rep_unit hκ k).some)).trans
    (DirectSum.lequivCongrLeft R hidx.some)).trans (rep_mkC hκ s).some.symm

/-- Every class is a multiple of `[R]`: `V^κ(𝓕^κ)` is cyclic. -/
theorem exists_cmul_unit (hκ : ℵ₀ ≤ κ) (k : Idx κ) (a : (freeClass R κ hκ).carrier) :
    letI := (freeClass R κ hκ).instKMonoid hκ
    ∃ (α : Cardinal.{u}) (hα : α ≤ κ), a = KMonoid.cmul (κ := κ) α hα (unit R κ hκ k) := by
  letI := (freeClass R κ hκ).instKMonoid hκ
  exact ⟨#(basis a), mk_le_kappa _, by rw [cmul_unit hκ k (mk_le_kappa (basis a)) rfl, mkC_basis]⟩

/-- Sums of classes add ranks. -/
theorem mkC_add_mkC (hκ : ℵ₀ ≤ κ) (k : Idx κ) (s t : Set (Idx κ))
    (hst : #s + #t ≤ κ) :
    letI := (freeClass R κ hκ).instKMonoid hκ
    mkC R κ hκ s + mkC R κ hκ t
      = KMonoid.cmul (κ := κ) (#s + #t) hst (unit R κ hκ k) := by
  letI := (freeClass R κ hκ).instKMonoid hκ
  rw [← cmul_unit hκ k (mk_le_kappa s) rfl, ← cmul_unit hκ k (mk_le_kappa t) rfl,
    ← KMonoid.cmul_add (mk_le_kappa s) (mk_le_kappa t)]

theorem add_mk_le (hκ : ℵ₀ ≤ κ) (s t : Set (Idx κ)) : #s + #t ≤ κ :=
  le_trans (add_le_add (mk_le_kappa s) (mk_le_kappa t)) (le_of_eq (Cardinal.add_eq_self hκ))

/-- **`[R]` is an order-unit of `V^κ(𝓕^κ)`**: a generating set and its complement fill `Idx κ`. -/
theorem isOrderUnit_unit (hκ : ℵ₀ ≤ κ) (k : Idx κ) :
    letI := (freeClass R κ hκ).instKMonoid hκ
    KMonoid.IsOrderUnit (κ := κ) (unit R κ hκ k) := by
  letI := (freeClass R κ hκ).instKMonoid hκ
  intro x
  refine ⟨mkC R κ hκ (basis x)ᶜ, ?_⟩
  have h1 := mkC_add_mkC (R := R) hκ k (basis x) (basis x)ᶜ (add_mk_le hκ _ _)
  rw [mkC_basis] at h1
  rw [h1]
  refine KMonoid.cmul_congr ?_ _ le_rfl (unit R κ hκ k)
  rw [Cardinal.mk_sum_compl, mk_Idx]

/-- **`[R]` is a faithful order-unit of `V^κ(𝓕^κ)`**: by invariance of infinite rank, `β·[R]`
is not a summand of `α·[R]` when `α < β` and `β` is infinite. -/
theorem isFaithful_unit [Nontrivial R] (hκ : ℵ₀ ≤ κ) (k : Idx κ) :
    letI := (freeClass R κ hκ).instKMonoid hκ
    KMonoid.IsFaithful (κ := κ) (unit R κ hκ k) := by
  letI := (freeClass R κ hκ).instKMonoid hκ
  refine ⟨isOrderUnit_unit hκ k, ?_⟩
  rintro α β hα hβ hαβ hβ0 ⟨c, hc⟩
  rw [cmul_unit hκ k hβ (mk_setOfCard hβ), ← mkC_basis hκ c,
    mkC_add_mkC hκ k _ _ (add_mk_le hκ _ _), cmul_unit hκ k hα (mk_setOfCard hα),
    cmul_unit hκ k (add_mk_le hκ (setOfCard hβ) (basis c))
      (mk_setOfCard (add_mk_le hκ (setOfCard (κ := κ) hβ) (basis c)))] at hc
  have key := mk_eq_of_mkC_eq hκ
    (show ℵ₀ ≤ #(setOfCard (κ := κ) (add_mk_le hκ (setOfCard hβ) (basis c))) by
      rw [mk_setOfCard, mk_setOfCard]
      exact le_trans hβ0 (self_le_add_right _ _)) hc
  rw [mk_setOfCard, mk_setOfCard, mk_setOfCard] at key
  exact absurd (le_trans (self_le_add_right _ _) (le_of_eq key)) (not_le_of_gt hαβ)

end FreeMod

end KappaMonoid
