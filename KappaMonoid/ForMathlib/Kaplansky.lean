/-
**Kaplansky's theorem**: over an arbitrary ring, every projective module is a direct sum of
countably generated projective modules.
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Order

universe u

open Cardinal DirectSum

/-- A family of submodules indexed by a linear order is independent as soon as each member is
disjoint from a submodule containing all its predecessors.  This is the shape a filtration
produces: `A b` is the sum of the pieces below `b`, and `C b` is a complement of it. -/
theorem iSupIndep_of_disjoint_lt {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [LinearOrder ι] {C A : ι → Submodule R M}
    (hdisj : ∀ b, Disjoint (A b) (C b)) (hle : ∀ {c b : ι}, c < b → C c ≤ A b) :
    iSupIndep C := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro v hv hsum i hi
    have hne : s.Nonempty := ⟨i, hi⟩
    set d := s.max' hne with hd
    have hdmem : d ∈ s := s.max'_mem hne
    have hlt : ∀ j ∈ s.erase d, j < d := fun j hj =>
      lt_of_le_of_ne (s.le_max' j (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)
    have hrest : ∑ j ∈ s.erase d, v j ∈ A d :=
      Submodule.sum_mem _ fun j hj => hle (hlt j hj) (hv j (Finset.mem_of_mem_erase hj))
    have hvd : v d = 0 := by
      rw [← Finset.add_sum_erase _ v hdmem] at hsum
      have hmem : v d ∈ A d := by
        rw [eq_neg_of_add_eq_zero_left hsum]
        exact neg_mem hrest
      exact Submodule.disjoint_def.1 (hdisj d) _ hmem (hv d hdmem)
    have hsum' : ∑ j ∈ s.erase d, v j = 0 := by
      rw [← Finset.add_sum_erase _ v hdmem, hvd, zero_add] at hsum
      exact hsum
    rcases eq_or_ne i d with rfl | hid
    · exact hvd
    · exact ih (s.erase d) (Finset.erase_ssubset hdmem) v
        (fun j hj => hv j (Finset.mem_of_mem_erase hj)) hsum' i (Finset.mem_erase.2 ⟨hid, hi⟩)

namespace Kaplansky

/-! ## Restricting the support of a finitely supported function -/

section Restrict

variable (R : Type u) [Ring R] {B : Type u}

/-- Restriction of `x : B →₀ R` to the coordinates in `S`, as a linear map. -/
noncomputable def restr (S : Set B) : (B →₀ R) →ₗ[R] (B →₀ R) :=
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  { toFun := Finsupp.filter (· ∈ S)
    map_add' := fun _ _ => Finsupp.filter_add
    map_smul' := fun _ _ => Finsupp.filter_smul }

variable {R}

theorem restr_apply_of_mem {S : Set B} {b : B} (h : b ∈ S) (x : B →₀ R) :
    restr R S x b = x b := by
  simp [restr, h]

theorem restr_apply_of_notMem {S : Set B} {b : B} (h : b ∉ S) (x : B →₀ R) :
    restr R S x b = 0 := by
  simp [restr, h]

theorem restr_mem_supported (S : Set B) (x : B →₀ R) :
    restr R S x ∈ Finsupp.supported R R S :=
  (Finsupp.mem_supported' _ _).2 fun _ hb => restr_apply_of_notMem hb x

theorem restr_eq_self {S : Set B} {x : B →₀ R} (hx : x ∈ Finsupp.supported R R S) :
    restr R S x = x := by
  ext b
  by_cases h : b ∈ S
  · exact restr_apply_of_mem h x
  · rw [restr_apply_of_notMem h, (Finsupp.mem_supported' _ _).1 hx b h]

theorem restr_restr (S : Set B) (x : B →₀ R) : restr R S (restr R S x) = restr R S x :=
  restr_eq_self (restr_mem_supported S x)

/-- The part of `x` outside `S` stays inside whatever set supported `x`. -/
theorem sub_restr_mem_supported {S T : Set B} {x : B →₀ R} (hx : x ∈ Finsupp.supported R R T) :
    x - restr R S x ∈ Finsupp.supported R R (T \ S) := by
  refine (Finsupp.mem_supported' _ _).2 fun b hb => ?_
  rw [Finsupp.sub_apply]
  by_cases h : b ∈ S
  · rw [restr_apply_of_mem h, sub_self]
  · rw [restr_apply_of_notMem h, sub_zero,
      (Finsupp.mem_supported' _ _).1 hx b fun hbT => hb ⟨hbT, h⟩]

theorem restr_eq_zero_of_disjoint {S T : Set B} (h : Disjoint T S) {x : B →₀ R}
    (hx : x ∈ Finsupp.supported R R T) : restr R S x = 0 := by
  ext b
  rw [Finsupp.zero_apply]
  by_cases hb : b ∈ S
  · rw [restr_apply_of_mem hb]
    exact (Finsupp.mem_supported' _ _).1 hx b fun hbT => Set.disjoint_left.1 h hbT hb
  · rw [restr_apply_of_notMem hb]

theorem range_restr (S : Set B) :
    LinearMap.range (restr R S) = Finsupp.supported R R S :=
  le_antisymm (LinearMap.range_le_iff_comap.2 (eq_top_iff.2 fun x _ => restr_mem_supported S x))
    fun x hx => ⟨x, restr_eq_self hx⟩

end Restrict

/-! ## Closure under a set-valued step function

`Reach f a b` is the reflexive-transitive reachability relation of `f`, and `cl f S` the smallest
`f`-closed set containing `S`.  Two properties matter: `cl` distributes over unions, so the
closure of a singleton is the basic building block, and the closure of a singleton is countable
whenever `f` has countable values. -/

section Closure

variable {B : Type u}

/-- `Reach f a b`: `b` is reached from `a` by finitely many applications of `f`. -/
inductive Reach (f : B → Set B) : B → B → Prop
  | refl (b : B) : Reach f b b
  | step {a b c : B} : Reach f a b → c ∈ f b → Reach f a c

/-- The smallest set containing `S` and closed under `f`. -/
def cl (f : B → Set B) (S : Set B) : Set B := {c | ∃ b ∈ S, Reach f b c}

theorem subset_cl (f : B → Set B) (S : Set B) : S ⊆ cl f S := fun b hb => ⟨b, hb, .refl b⟩

theorem cl_closed {f : B → Set B} {S : Set B} {b : B} (hb : b ∈ cl f S) : f b ⊆ cl f S := by
  obtain ⟨a, ha, hab⟩ := hb
  exact fun _ hc => ⟨a, ha, hab.step hc⟩

theorem cl_mono {f : B → Set B} {S T : Set B} (h : S ⊆ T) : cl f S ⊆ cl f T :=
  fun _ ⟨b, hb, hbc⟩ => ⟨b, h hb, hbc⟩

theorem cl_union (f : B → Set B) (S T : Set B) : cl f (S ∪ T) = cl f S ∪ cl f T := by
  ext c
  constructor
  · rintro ⟨b, hb | hb, hbc⟩
    exacts [Or.inl ⟨b, hb, hbc⟩, Or.inr ⟨b, hb, hbc⟩]
  · rintro (⟨b, hb, hbc⟩ | ⟨b, hb, hbc⟩)
    exacts [⟨b, Or.inl hb, hbc⟩, ⟨b, Or.inr hb, hbc⟩]

/-- The `n`-fold `f`-image of `b`, used only to see that `cl f {b}` is countable. -/
def iter (f : B → Set B) (b : B) : ℕ → Set B
  | 0 => {b}
  | n + 1 => iter f b n ∪ ⋃ c ∈ iter f b n, f c

theorem countable_iter {f : B → Set B} (hf : ∀ b, (f b).Countable) (b : B) :
    ∀ n, (iter f b n).Countable
  | 0 => Set.countable_singleton b
  | n + 1 => (countable_iter hf b n).union
      ((countable_iter hf b n).biUnion fun c _ => hf c)

theorem cl_singleton_eq_iUnion (f : B → Set B) (b : B) : cl f {b} = ⋃ n, iter f b n := by
  ext c
  constructor
  · rintro ⟨a, rfl, hac⟩
    induction hac with
    | refl => exact Set.mem_iUnion.2 ⟨0, rfl⟩
    | step _ hd ih =>
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 ih
        exact Set.mem_iUnion.2 ⟨n + 1, Or.inr (Set.mem_biUnion hn hd)⟩
  · rintro hc
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hc
    refine ⟨b, rfl, ?_⟩
    clear hc
    induction n generalizing c with
    | zero =>
        obtain rfl : c = b := hn
        exact .refl _
    | succ n ih =>
        rcases hn with hn | hn
        · exact ih c hn
        · obtain ⟨d, hd, hdc⟩ := Set.mem_iUnion₂.1 hn
          exact (ih d hd).step hdc

theorem countable_cl_singleton {f : B → Set B} (hf : ∀ b, (f b).Countable) (b : B) :
    (cl f {b}).Countable := by
  rw [cl_singleton_eq_iUnion]
  exact Set.countable_iUnion fun n => countable_iter hf b n

end Closure

/-! ## The filtration attached to an idempotent endomorphism of a free module

Fix an idempotent `π` on the free module `B →₀ R`.  A set `S` of coordinates is *good* when the
submodule `Finsupp.supported R R S` is `π`-invariant, and that happens exactly when `S` is closed
under `supp π`, the support of the image of a basis vector; so the closure operator of the previous
section produces good sets, and the closure of a *single* coordinate is countable.

Well-ordering `B`, the closures `Jle π b` of the initial segments `Set.Iic b` form a continuous
increasing chain of good sets whose successive differences `Dblock π b` are countable.  On the
`b`-th block, `blockIdem π b` is again idempotent, and `Cpart π b`, its image under `π`, is a
complement of `π (supported R R (Jlt π b))` inside `π (supported R R (Jle π b))`. -/

section Main

variable {R : Type u} [Ring R] {B : Type u}
variable (π : (B →₀ R) →ₗ[R] (B →₀ R))

/-- The coordinates occurring in the image of the `b`-th basis vector. -/
def supp (b : B) : Set B := ↑(π (Finsupp.single b 1)).support

theorem countable_supp (b : B) : (supp π b).Countable :=
  (π (Finsupp.single b 1)).support.countable_toSet

/-- A set of coordinates is *good* when the coordinate subspace it spans is `π`-invariant. -/
def IsGood (S : Set B) : Prop := ∀ b ∈ S, supp π b ⊆ S

theorem map_le_of_isGood {S : Set B} (h : IsGood π S) :
    Submodule.map π (Finsupp.supported R R S) ≤ Finsupp.supported R R S := by
  rw [Submodule.map_le_iff_le_comap]
  conv_lhs => rw [Finsupp.supported_eq_span_single]
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb

theorem map_mem_of_isGood {S : Set B} (h : IsGood π S) {x : B →₀ R}
    (hx : x ∈ Finsupp.supported R R S) : π x ∈ Finsupp.supported R R S :=
  map_le_of_isGood π h ⟨x, hx, rfl⟩

variable [LinearOrder B]

/-- The good set generated by the coordinates strictly below `b`. -/
def Jlt (b : B) : Set B := cl (supp π) (Set.Iio b)

/-- The good set generated by the coordinates up to and including `b`. -/
def Jle (b : B) : Set B := cl (supp π) (Set.Iic b)

/-- The coordinates new at stage `b`; countable, which is where countable generation comes from. -/
def Dblock (b : B) : Set B := Jle π b \ Jlt π b

theorem isGood_Jlt (b : B) : IsGood π (Jlt π b) := fun _ hc => cl_closed hc

theorem isGood_Jle (b : B) : IsGood π (Jle π b) := fun _ hc => cl_closed hc

theorem Jlt_subset_Jle (b : B) : Jlt π b ⊆ Jle π b := cl_mono Set.Iio_subset_Iic_self

theorem Jle_diff_Dblock (b : B) : Jle π b \ Dblock π b = Jlt π b :=
  Set.sdiff_sdiff_cancel_left (Jlt_subset_Jle π b)

theorem disjoint_Jlt_Dblock (b : B) : Disjoint (Jlt π b) (Dblock π b) := Set.disjoint_sdiff_right

theorem Dblock_subset_cl (b : B) : Dblock π b ⊆ cl (supp π) {b} := by
  rintro c ⟨hc, hc'⟩
  rw [Jle, ← Set.Iio_insert, Set.insert_eq, cl_union] at hc
  exact hc.resolve_right hc'

theorem countable_Dblock (b : B) : (Dblock π b).Countable :=
  (countable_cl_singleton (countable_supp π) b).mono (Dblock_subset_cl π b)

theorem Dblock_subset_Jle (b : B) : Dblock π b ⊆ Jle π b := Set.sdiff_subset

theorem restr_mem_Jle (b : B) (x : B →₀ R) :
    restr R (Dblock π b) x ∈ Finsupp.supported R R (Jle π b) :=
  Finsupp.supported_mono (Dblock_subset_Jle π b) (restr_mem_supported _ x)

theorem sub_restr_mem_Jlt {b : B} {x : B →₀ R} (hx : x ∈ Finsupp.supported R R (Jle π b)) :
    x - restr R (Dblock π b) x ∈ Finsupp.supported R R (Jlt π b) := by
  have h := sub_restr_mem_supported (S := Dblock π b) hx
  rwa [Jle_diff_Dblock] at h

theorem mem_Jlt_of_restr_eq_zero {b : B} {x : B →₀ R}
    (hx : x ∈ Finsupp.supported R R (Jle π b)) (h : restr R (Dblock π b) x = 0) :
    x ∈ Finsupp.supported R R (Jlt π b) := by
  have h' := sub_restr_mem_Jlt π hx
  rwa [h, sub_zero] at h'

theorem restr_eq_zero_of_mem_Jlt {b : B} {x : B →₀ R}
    (hx : x ∈ Finsupp.supported R R (Jlt π b)) : restr R (Dblock π b) x = 0 :=
  restr_eq_zero_of_disjoint (disjoint_Jlt_Dblock π b) hx

/-- Restricting to the `b`-th block loses nothing after applying `π`: the part of `y` outside the
block is supported below `b`, and stays there under `π`, so it is invisible to the restriction. -/
theorem restr_map_restr {b : B} {y : B →₀ R} (hy : y ∈ Finsupp.supported R R (Jle π b)) :
    restr R (Dblock π b) (π (restr R (Dblock π b) y)) = restr R (Dblock π b) (π y) := by
  have h := restr_eq_zero_of_mem_Jlt π
    (map_mem_of_isGood π (isGood_Jlt π b) (sub_restr_mem_Jlt π hy))
  rw [map_sub, map_sub] at h
  exact (sub_eq_zero.1 h).symm

/-- The idempotent cutting out the `b`-th block of the image of `π`. -/
noncomputable def blockIdem (b : B) : (B →₀ R) →ₗ[R] (B →₀ R) :=
  restr R (Dblock π b) ∘ₗ π ∘ₗ restr R (Dblock π b)

theorem blockIdem_apply (b : B) (x : B →₀ R) :
    blockIdem π b x = restr R (Dblock π b) (π (restr R (Dblock π b) x)) := rfl

theorem range_blockIdem_le (b : B) :
    LinearMap.range (blockIdem π b) ≤ Finsupp.supported R R (Dblock π b) := by
  rintro _ ⟨x, rfl⟩
  exact restr_mem_supported _ _

theorem blockIdem_idem (hπ : ∀ x, π (π x) = π x) (b : B) (x : B →₀ R) :
    blockIdem π b (blockIdem π b x) = blockIdem π b x := by
  have hy : π (restr R (Dblock π b) x) ∈ Finsupp.supported R R (Jle π b) :=
    map_mem_of_isGood π (isGood_Jle π b) (restr_mem_Jle π b x)
  calc blockIdem π b (blockIdem π b x)
      = restr R (Dblock π b)
          (π (restr R (Dblock π b) (restr R (Dblock π b) (π (restr R (Dblock π b) x))))) := rfl
    _ = restr R (Dblock π b) (π (restr R (Dblock π b) (π (restr R (Dblock π b) x)))) := by
          rw [restr_restr]
    _ = restr R (Dblock π b) (π (π (restr R (Dblock π b) x))) := restr_map_restr π hy
    _ = blockIdem π b x := by rw [blockIdem_apply π b x, hπ]

theorem blockIdem_eq_self (hπ : ∀ x, π (π x) = π x) {b : B} {y : B →₀ R}
    (hy : y ∈ LinearMap.range (blockIdem π b)) : blockIdem π b y = y := by
  obtain ⟨x, rfl⟩ := hy
  exact blockIdem_idem π hπ b x

/-- On the range of `blockIdem π b`, restricting `π` back to the block is the identity.  This is
what makes `π` injective there, and what forces the two summands below to meet in `0`. -/
theorem restr_map_eq_self (hπ : ∀ x, π (π x) = π x) {b : B} {y : B →₀ R}
    (hy : y ∈ LinearMap.range (blockIdem π b)) : restr R (Dblock π b) (π y) = y := by
  have h1 : restr R (Dblock π b) y = y := restr_eq_self (range_blockIdem_le π b hy)
  calc restr R (Dblock π b) (π y)
      = restr R (Dblock π b) (π (restr R (Dblock π b) y)) := by rw [h1]
    _ = blockIdem π b y := rfl
    _ = y := blockIdem_eq_self π hπ hy

/-- The `b`-th summand: the image under `π` of the `b`-th block. -/
noncomputable def Cpart (b : B) : Submodule R (B →₀ R) := Submodule.map π (LinearMap.range (blockIdem π b))

/-- The image under `π` of the coordinates up to `b`. -/
noncomputable def Apart (b : B) : Submodule R (B →₀ R) := Submodule.map π (Finsupp.supported R R (Jle π b))

/-- The image under `π` of the coordinates strictly below `b`. -/
noncomputable def Altpart (b : B) : Submodule R (B →₀ R) := Submodule.map π (Finsupp.supported R R (Jlt π b))

theorem Altpart_le_Apart (b : B) : Altpart π b ≤ Apart π b :=
  Submodule.map_mono (Finsupp.supported_mono (Jlt_subset_Jle π b))

theorem Cpart_le_Apart (b : B) : Cpart π b ≤ Apart π b :=
  Submodule.map_mono
    ((range_blockIdem_le π b).trans (Finsupp.supported_mono (Dblock_subset_Jle π b)))

theorem Apart_le_range (b : B) : Apart π b ≤ LinearMap.range π := by
  rintro _ ⟨x, -, rfl⟩
  exact LinearMap.mem_range_self _ _

theorem disjoint_Altpart_Cpart (hπ : ∀ x, π (π x) = π x) (b : B) :
    Disjoint (Altpart π b) (Cpart π b) := by
  rw [Submodule.disjoint_def]
  rintro _ hx ⟨y, hy, rfl⟩
  obtain ⟨u, hu, hxu⟩ := hx
  have h1 : π y ∈ Finsupp.supported R R (Jlt π b) := hxu ▸ map_mem_of_isGood π (isGood_Jlt π b) hu
  have h2 : restr R (Dblock π b) (π y) = 0 := restr_eq_zero_of_mem_Jlt π h1
  rw [restr_map_eq_self π hπ hy] at h2
  rw [h2, map_zero]

theorem sup_Altpart_Cpart (hπ : ∀ x, π (π x) = π x) (b : B) :
    Altpart π b ⊔ Cpart π b = Apart π b := by
  refine le_antisymm (sup_le (Altpart_le_Apart π b) (Cpart_le_Apart π b)) ?_
  rintro _ ⟨v, hv, rfl⟩
  set w := restr R (Dblock π b) v with hw
  have hwmem : w ∈ Finsupp.supported R R (Dblock π b) := restr_mem_supported _ _
  set z := blockIdem π b w with hz
  have hzmem : z ∈ LinearMap.range (blockIdem π b) := ⟨w, rfl⟩
  -- the part of `v` below `b` contributes to `Altpart`
  have hlow : π (v - w) ∈ Altpart π b := ⟨v - w, sub_restr_mem_Jlt π hv, rfl⟩
  -- and the block part splits as `π (w - z) + π z`
  have hwz : w - z ∈ Finsupp.supported R R (Jle π b) :=
    sub_mem (Finsupp.supported_mono (Dblock_subset_Jle π b) hwmem)
      (Finsupp.supported_mono (Dblock_subset_Jle π b) (range_blockIdem_le π b hzmem))
  have hzw : restr R (Dblock π b) (π w) = z := by
    rw [hz, blockIdem_apply, restr_eq_self hwmem]
  have h5 : restr R (Dblock π b) (π (w - z)) = 0 := by
    rw [map_sub, map_sub, hzw, restr_map_eq_self π hπ hzmem, sub_self]
  have h6 : π (w - z) ∈ Altpart π b :=
    ⟨π (w - z), mem_Jlt_of_restr_eq_zero π (map_mem_of_isGood π (isGood_Jle π b) hwz) h5, hπ _⟩
  have hsplit : π v = (π (v - w) + π (w - z)) + π z := by
    rw [← map_add, ← map_add]; congr 1; abel
  rw [hsplit]
  exact add_mem (add_mem (Submodule.mem_sup_left hlow) (Submodule.mem_sup_left h6))
    (Submodule.mem_sup_right ⟨z, hzmem, rfl⟩)

/-! ### The summands are projective and countably generated -/

theorem projective_range_blockIdem (hπ : ∀ x, π (π x) = π x) (b : B) :
    Module.Projective R (LinearMap.range (blockIdem π b)) :=
  Module.Projective.of_split ((LinearMap.range (blockIdem π b)).subtype)
    (LinearMap.codRestrict _ (blockIdem π b) fun _ => LinearMap.mem_range_self _ _)
    (LinearMap.ext fun y => Subtype.ext (blockIdem_eq_self π hπ y.2))

theorem projective_Cpart (hπ : ∀ x, π (π x) = π x) (b : B) :
    Module.Projective R (Cpart π b) := by
  have := projective_range_blockIdem π hπ b
  have hinj : Function.Injective (π ∘ₗ (LinearMap.range (blockIdem π b)).subtype) := by
    intro y₁ y₂ h
    have h' : π (y₁ : B →₀ R) = π (y₂ : B →₀ R) := h
    refine Subtype.ext ?_
    rw [← restr_map_eq_self π hπ y₁.2, ← restr_map_eq_self π hπ y₂.2, h']
  have hrange : LinearMap.range (π ∘ₗ (LinearMap.range (blockIdem π b)).subtype)
      = Cpart π b := by
    rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
  exact Module.Projective.of_equiv'
    ((LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange))

theorem Cpart_eq_span (b : B) :
    Cpart π b = Submodule.span R
      ((fun c => π (restr R (Dblock π b) (π (Finsupp.single c 1)))) '' Dblock π b) := by
  have h1 : LinearMap.range (blockIdem π b)
      = Submodule.map (restr R (Dblock π b) ∘ₗ π) (Finsupp.supported R R (Dblock π b)) := by
    rw [show blockIdem π b = (restr R (Dblock π b) ∘ₗ π) ∘ₗ restr R (Dblock π b) from rfl,
      LinearMap.range_comp, range_restr]
  rw [Cpart, h1, ← Submodule.map_comp, Finsupp.supported_eq_span_single, Submodule.map_span,
    Set.image_image]
  rfl

/-- A submodule spanned by a countable subset is countably generated in the sense of the
statement below: it has a countable spanning set *of its own elements*. -/
theorem exists_countable_span_top {M : Type u} [AddCommGroup M] [Module R M]
    {C : Submodule R M} {G : Set M} (hGC : G ⊆ (C : Set M)) (hG : G.Countable)
    (hspan : Submodule.span R G = C) :
    ∃ s : Set C, #s ≤ ℵ₀ ∧ Submodule.span R s = ⊤ := by
  refine ⟨C.subtype ⁻¹' G, ?_, ?_⟩
  · exact Cardinal.mk_le_aleph0_iff.2
      (Set.countable_coe_iff.2 (hG.preimage C.injective_subtype))
  · apply Submodule.map_injective_of_injective C.injective_subtype
    have hr : Set.range (C.subtype) = (C : Set M) := by simp
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
      Set.image_preimage_eq_inter_range, hr, Set.inter_eq_self_of_subset_left hGC, hspan]

theorem countablyGenerated_Cpart (b : B) :
    ∃ s : Set (Cpart π b), #s ≤ ℵ₀ ∧ Submodule.span R s = ⊤ := by
  refine exists_countable_span_top (C := Cpart π b) ?_
    (((countable_Dblock π b).image _)) (Cpart_eq_span π b).symm
  rw [Cpart_eq_span π b]
  exact Submodule.subset_span

/-! ### Assembling the decomposition -/

variable [WellFoundedLT B]

omit [WellFoundedLT B] in
theorem Apart_le_Altpart {c b : B} (h : c < b) : Apart π c ≤ Altpart π b :=
  Submodule.map_mono (Finsupp.supported_mono (cl_mono fun _ hd => lt_of_le_of_lt hd h))

theorem Apart_le_iSup (hπ : ∀ x, π (π x) = π x) (b : B) : Apart π b ≤ ⨆ c, Cpart π c := by
  induction b using WellFoundedLT.induction with
  | ind b ih =>
    rw [← sup_Altpart_Cpart π hπ b]
    refine sup_le ?_ (le_iSup _ b)
    have hsub : Finsupp.supported R R (Jlt π b)
        ≤ ⨆ c : Set.Iio b, Finsupp.supported R R (Jle π (c : B)) := by
      rw [← Finsupp.supported_iUnion]
      refine Finsupp.supported_mono ?_
      rintro d ⟨e, he, hed⟩
      exact Set.mem_iUnion.2 ⟨⟨e, he⟩, ⟨e, le_refl e, hed⟩⟩
    calc Altpart π b
        ≤ Submodule.map π (⨆ c : Set.Iio b, Finsupp.supported R R (Jle π (c : B))) :=
          Submodule.map_mono hsub
      _ = ⨆ c : Set.Iio b, Apart π (c : B) := Submodule.map_iSup _ _
      _ ≤ ⨆ c, Cpart π c := iSup_le fun c => ih (c : B) c.2

theorem iSup_Cpart (hπ : ∀ x, π (π x) = π x) :
    ⨆ b, Cpart π b = LinearMap.range π := by
  refine le_antisymm (iSup_le fun b => (Cpart_le_Apart π b).trans (Apart_le_range π b)) ?_
  rw [LinearMap.range_eq_map, ← Finsupp.supported_univ (M := R) (R := R),
    Finsupp.supported_eq_span_single, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
  exact Apart_le_iSup π hπ b
    ⟨Finsupp.single b 1, Finsupp.single_mem_supported R 1 (subset_cl _ _ (le_refl b)), rfl⟩

omit [WellFoundedLT B] in
theorem iSupIndep_Cpart (hπ : ∀ x, π (π x) = π x) : iSupIndep (Cpart π) :=
  iSupIndep_of_disjoint_lt (disjoint_Altpart_Cpart π hπ)
    fun hcb => (Cpart_le_Apart π _).trans (Apart_le_Altpart π hcb)

end Main

/-! ## Kaplansky's theorem -/

/-- The decomposition of the image of an idempotent endomorphism of a free module. -/
theorem exists_decomposition_of_idempotent {R : Type u} [Ring R] {B : Type u}
    (π : (B →₀ R) →ₗ[R] (B →₀ R)) (hπ : ∀ x, π (π x) = π x) :
    ∃ (Q : B → Type u) (_ : ∀ i, AddCommGroup (Q i)) (_ : ∀ i, Module R (Q i)),
      (∀ i, Module.Projective R (Q i)) ∧
        (∀ i, ∃ s : Set (Q i), #s ≤ ℵ₀ ∧ Submodule.span R s = ⊤) ∧
          Nonempty (LinearMap.range π ≃ₗ[R] ⨁ i, Q i) := by
  classical
  obtain ⟨_inst, hwf⟩ := exists_wellFoundedLT B
  have := hwf
  refine ⟨fun b => Cpart π b, fun _ => inferInstance, fun _ => inferInstance,
    fun b => projective_Cpart π hπ b, fun b => countablyGenerated_Cpart π b, ⟨?_⟩⟩
  have hinj : Function.Injective (DirectSum.coeLinearMap fun b => Cpart π b) :=
    (iSupIndep_Cpart π hπ).dfinsupp_lsum_injective
  have hrange : LinearMap.range (DirectSum.coeLinearMap fun b => Cpart π b)
      = LinearMap.range π := by
    rw [DirectSum.range_coeLinearMap, iSup_Cpart π hπ]
  exact (LinearEquiv.ofEq _ _ hrange.symm).trans (LinearEquiv.ofInjective _ hinj).symm

end Kaplansky

/-- **Kaplansky's theorem**: over an arbitrary ring, a projective module is a direct sum of
countably generated projective modules.

Paper proof (Kaplansky 1958, in the form given on Wikipedia).  `P` is a direct summand of a free
module `F = B →₀ R`, say `F = P ⊕ L` with `π : F → F` the idempotent projection onto `P`.  Well-
order `B`, and let `J_{<b}` and `J_{≤b}` be the smallest sets of coordinates containing `Set.Iio b`
resp. `Set.Iic b` and closed under `b ↦ supp (π (single b 1))`; each is countable over its
predecessor because the closure of one coordinate is a countable union of finite sets.  The
coordinate subspaces they span are `π`-invariant, so `π` restricts to an idempotent on each, and
the `b`-th successive quotient is again cut out by an idempotent — `blockIdem` — of the free module
on the countably many new coordinates.  Its image under `π` is a complement of `π(J_{<b})` inside
`π(J_{≤b})`, projective as a summand of a free module and countably generated because the block is;
and these complements are independent and span `π(F) = P`. -/
theorem Module.Projective.exists_directSum_countablyGenerated {R : Type u} [Ring R] (P : Type u)
    [AddCommGroup P] [Module R P] [Module.Projective R P] :
    ∃ (ι : Type u) (Q : ι → Type u) (_ : ∀ i, AddCommGroup (Q i)) (_ : ∀ i, Module R (Q i)),
      (∀ i, Module.Projective R (Q i)) ∧
        (∀ i, ∃ s : Set (Q i), #s ≤ ℵ₀ ∧ Submodule.span R s = ⊤) ∧
          Nonempty (P ≃ₗ[R] ⨁ i, Q i) := by
  classical
  obtain ⟨sec, hsec⟩ := Module.projective_def'.1 ‹Module.Projective R P›
  set t := Finsupp.linearCombination R (id : P → P) with ht
  have hts : ∀ p : P, t (sec p) = p := fun p => congrFun (congrArg DFunLike.coe hsec) p
  set π := sec ∘ₗ t with hπdef
  have hπ : ∀ x, π (π x) = π x := fun x => congrArg sec (hts (t x))
  have hrange : LinearMap.range π = LinearMap.range sec := by
    refine le_antisymm (LinearMap.range_comp_le_range _ _) ?_
    rintro _ ⟨p, rfl⟩
    exact ⟨sec p, congrArg sec (hts p)⟩
  obtain ⟨Q, iAG, iMod, hproj, hgen, ⟨e⟩⟩ := Kaplansky.exists_decomposition_of_idempotent π hπ
  refine ⟨P, Q, iAG, iMod, hproj, hgen, ⟨?_⟩⟩
  have hsecinj : Function.Injective sec := fun p q h => by
    rw [← hts p, ← hts q, h]
  exact ((LinearEquiv.ofInjective sec hsecinj).trans (LinearEquiv.ofEq _ _ hrange.symm)).trans e
