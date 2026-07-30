/-
A Lean 4 / Mathlib formalisation of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

Part 1 — Section 2: infinite summation, `κ`-monoids and `λ⁻`-monoids.

Design notes (see also `README.md`):

* Index sets.  The paper uses the von Neumann cardinal `κ` itself as index set.  We use
  `Idx κ := κ.ord.toType`, a fixed type of cardinality `κ`, and derive summation over an
  arbitrary index type of cardinality `≤ κ` (as the paper does after Lemma 2.5).

* Axiom (A1).  The paper states (A1) only for the distinguished element `0 ∈ κ`; combined
  with (A2) this yields the commutativity law (A3) and hence (A1) at every index.  We
  state (A1) at every index directly, which is equivalent and avoids having to name a
  distinguished element of `Idx κ`.

* Underlying additive monoid.  By Lemma 2.5 and the discussion following it, a `κ`-monoid
  carries a canonical commutative monoid structure with `a + b = Σ²(a, b)`.  Reconstructing
  that structure inside Lean each time is unpleasant, so we let `KMonoid` *extend*
  `AddCommMonoid` and add the (redundant, but harmless) compatibility axiom `ksum_two`.
  `KMonoid.ofBare` below records that nothing is lost.

* `λ⁻`-monoids.  Definition 2.18 gives a *partial* operation, defined on families indexed
  by `λ` with support of cardinality `< λ`.  We model it by a total function together with
  the junk convention `lsum x = 0` for families with large support; this pins the data down
  uniquely without changing the mathematics.
-/
import Mathlib

universe u v w

open Cardinal Function Set Classical

namespace NS

/-! ## The index types -/

/-- `Idx κ` is a fixed type of cardinality `κ`, playing the role of the von Neumann
cardinal `κ` used as an index set in the paper. -/
abbrev Idx (κ : Cardinal.{u}) : Type u := κ.ord.ToType

@[simp] theorem mk_Idx (κ : Cardinal.{u}) : #(Idx κ) = κ := mk_ord_toType κ

theorem nonempty_Idx {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) : Nonempty (Idx κ) := by
  rw [← mk_ne_zero_iff, mk_Idx]
  rintro rfl
  exact aleph0_ne_zero (le_antisymm hκ zero_le)

/-- An embedding of any type of cardinality `≤ κ` into `Idx κ`. -/
noncomputable def emb {ι : Type u} {κ : Cardinal.{u}} (h : #ι ≤ κ) : ι ↪ Idx κ :=
  ((Cardinal.le_def ι (Idx κ)).mp (by simpa using h)).some

/-- For infinite `κ` we have `κ * κ = κ`, hence a bijection `Idx κ × Idx κ ≃ Idx κ`. -/
noncomputable def pairEquiv {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) :
    Idx κ × Idx κ ≃ Idx κ :=
  (Cardinal.eq.mp (by simp [Cardinal.mul_eq_self hκ])).some

/-! ## `κ`-monoids (Definition 2.1) -/

/-- A `κ`-monoid: a commutative monoid `H` equipped with a summation operation for
`κ`-indexed families, subject to (A1) and (A2) of Definition 2.1. -/
class KMonoid (κ : Cardinal.{u}) (H : Type v) extends AddCommMonoid H where
  /-- `κ` is an infinite cardinal. -/
  aleph0_le : ℵ₀ ≤ κ
  /-- The `κ`-indexed summation `Σ : H^κ → H`. -/
  ksum : (Idx κ → H) → H
  /-- (A1): a family concentrated in one index sums to its unique possibly nonzero entry. -/
  ksum_single : ∀ (i₀ : Idx κ) (x : Idx κ → H), (∀ i, i ≠ i₀ → x i = 0) → ksum x = x i₀
  /-- (A2): the associativity law modelled on `⨁ᵢ ⨁ⱼ Mᵢⱼ ≅ ⨁_{(i,j)} Mᵢⱼ`. -/
  ksum_sigma : ∀ (x : Idx κ → Idx κ → H) (π : Idx κ × Idx κ ≃ Idx κ),
      ksum (fun i => ksum (x i)) = ksum fun k => x (π.symm k).1 (π.symm k).2
  /-- Compatibility of `+` with `Σ`.  This is not an extra assumption: by Lemma 2.5 the
  binary operation `Σ²` obtained from `Σ` is commutative and associative, and `ksum_two`
  holds for it by construction. -/
  ksum_two : ∀ (a b : H) (i₀ i₁ : Idx κ), i₀ ≠ i₁ →
      ksum (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b

namespace KMonoid

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

theorem ksum_zero : ksum (κ := κ) (fun _ : Idx κ => (0 : H)) = 0 := by
  obtain ⟨i₀⟩ := nonempty_Idx (aleph0_le (κ := κ) (H := H))
  exact ksum_single i₀ _ fun _ _ => rfl

/-! ### The derived commutativity and associativity laws (Lemma 2.5) -/

/-- (A3), Lemma 2.5: `Σ` is invariant under permutations of the index set.

Paper proof: spread `x` out as `y i j := if j = j₀ then x i else 0`, so that
`Σⱼ y i j = x i` by (A1); then apply (A2) once with the bijection `f ∘ (π⁻¹, id)` and once
with `f`, for an arbitrary bijection `f : κ × κ ≃ κ`. -/
theorem ksum_perm (x : Idx κ → H) (π : Idx κ ≃ Idx κ) :
    ksum (κ := κ) x = ksum (κ := κ) (x ∘ π) := by
  obtain ⟨j₀⟩ := nonempty_Idx (aleph0_le (κ := κ) (H := H))
  set y : Idx κ → Idx κ → H := fun i j => if j = j₀ then x i else 0 with hy
  set w : Idx κ → Idx κ → H := fun i j => y (π i) j with hw
  have hxy : ∀ i, ksum (κ := κ) (y i) = x i := fun i =>
    (ksum_single j₀ (y i) (fun j hj => if_neg hj)).trans (if_pos rfl)
  have hwx : ∀ i, ksum (κ := κ) (w i) = x (π i) := fun i => hxy (π i)
  set f := pairEquiv (aleph0_le (κ := κ) (H := H)) with hf
  set g : Idx κ × Idx κ ≃ Idx κ := (π.symm.prodCongr (Equiv.refl (Idx κ))).trans f with hg
  have hgsymm : ∀ l : Idx κ, g.symm l = (π (f.symm l).1, (f.symm l).2) := by
    intro l
    apply Prod.ext <;>
      simp [hg, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  have hstep : (fun l => y (g.symm l).1 (g.symm l).2) = fun l => w (f.symm l).1 (f.symm l).2 := by
    funext l
    rw [hgsymm l]
  calc ksum (κ := κ) x
      = ksum (κ := κ) (fun i => ksum (κ := κ) (y i)) := by
        congr 1; funext i; exact (hxy i).symm
    _ = ksum (κ := κ) (fun l => y (g.symm l).1 (g.symm l).2) := ksum_sigma y g
    _ = ksum (κ := κ) (fun l => w (f.symm l).1 (f.symm l).2) := congrArg _ hstep
    _ = ksum (κ := κ) (fun i => ksum (κ := κ) (w i)) := (ksum_sigma w f).symm
    _ = ksum (κ := κ) (fun i => x (π i)) := by
        congr 1; funext i; exact hwx i
    _ = ksum (κ := κ) (x ∘ π) := rfl

/-- (A4), Lemma 2.5: iterated sums may be interchanged.  Paper proof: apply (A2) twice,
once for `f` and once for `τ ∘ f` with `τ` the transposition of `κ × κ`. -/
theorem ksum_comm (x : Idx κ → Idx κ → H) :
    ksum (κ := κ) (fun i => ksum (x i)) = ksum (κ := κ) (fun j => ksum fun i => x i j) := by
  set y : Idx κ → Idx κ → H := fun i j => x j i with hy
  set f := pairEquiv (aleph0_le (κ := κ) (H := H)) with hf
  set τ : Idx κ × Idx κ ≃ Idx κ × Idx κ := Equiv.prodComm (Idx κ) (Idx κ) with hτ
  set σ : Idx κ ≃ Idx κ := (f.symm.trans τ).trans f with hσ
  have hστ : ∀ l : Idx κ, f.symm (σ l) = τ (f.symm l) := by
    intro l
    simp [hσ]
  have hz : (fun l => x (f.symm l).2 (f.symm l).1) = (fun l => x (f.symm l).1 (f.symm l).2) ∘ σ := by
    funext l
    simp only [Function.comp_apply, hστ l, hτ, Equiv.prodComm_apply, Prod.swap]
  calc ksum (κ := κ) (fun i => ksum (x i))
      = ksum (κ := κ) (fun l => x (f.symm l).1 (f.symm l).2) := ksum_sigma x f
    _ = ksum (κ := κ) ((fun l => x (f.symm l).1 (f.symm l).2) ∘ σ) := ksum_perm _ σ
    _ = ksum (κ := κ) (fun l => x (f.symm l).2 (f.symm l).1) := by rw [← hz]
    _ = ksum (κ := κ) (fun l => y (f.symm l).1 (f.symm l).2) := rfl
    _ = ksum (κ := κ) (fun i => ksum (y i)) := (ksum_sigma y f).symm
    _ = ksum (κ := κ) (fun j => ksum fun i => x i j) := rfl

/-! ### Summation over arbitrary index sets of cardinality `≤ κ`

This is the construction of `Σ^α` from `Σ^κ` described in the paper after Lemma 2.5. -/

/-- Inserting zeros does not change a `κ`-sum.

Paper proof (implicit): for `g` whose range has complement of cardinality `κ` this is (A2)
applied to `y i j := if j = j₀ then x i else 0`; the general case follows by composing with
such a `g` and using (A3). -/
theorem ksum_extend (g : Idx κ ↪ Idx κ) (x : Idx κ → H) :
    ksum (κ := κ) (Function.extend g x 0) = ksum (κ := κ) x := by
  have hκ := aleph0_le (κ := κ) (H := H)
  obtain ⟨j₀⟩ := nonempty_Idx hκ
  have hInf : Infinite (Idx κ) := Cardinal.infinite_iff.mpr (by rw [mk_Idx]; exact hκ)
  -- Case A: embeddings whose range has complement of cardinality `κ` absorb zero-padding.
  have caseA : ∀ (e : Idx κ ↪ Idx κ), #(↥(Set.range e)ᶜ) = κ →
      ∀ z : Idx κ → H, ksum (κ := κ) (Function.extend e z 0) = ksum (κ := κ) z := by
    intro e hcompl z
    set R₀ : Set (Idx κ × Idx κ) := Set.range (fun i : Idx κ => (i, j₀)) with hR₀def
    have hR₀inj : Function.Injective (fun i : Idx κ => (i, j₀)) := fun a b hab =>
      (Prod.ext_iff.mp hab).1
    set ρ₀ : Idx κ ≃ ↥R₀ := Equiv.ofInjective _ hR₀inj with hρ₀def
    set pt : Set (Idx κ) := {j₀} with hptdef
    have hptlt : #(pt : Set (Idx κ)) < #(Idx κ) :=
      (mk_singleton j₀).trans_lt (lt_of_lt_of_le one_lt_aleph0 (by rw [mk_Idx]; exact hκ))
    have hptc : #(↥ptᶜ) = #(Idx κ) := mk_compl_of_infinite pt hptlt
    set rowComplEquiv : ↥R₀ᶜ ≃ Idx κ × ↥ptᶜ :=
      { toFun := fun p => (p.1.1, ⟨p.1.2, fun hmem => p.2 ⟨p.1.1, Prod.ext rfl hmem.symm⟩⟩)
        invFun := fun q => ⟨(q.1, q.2.1), fun hmem => q.2.2 (by
          obtain ⟨i, hi⟩ := hmem
          exact (Prod.ext_iff.mp hi).2.symm)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } with hrowComplEquivdef
    have hR₀c : #(↥R₀ᶜ) = κ := by
      have heq := Cardinal.mk_congr rowComplEquiv
      rw [heq, Cardinal.mk_prod, hptc, mk_Idx]
      simp [Cardinal.mul_eq_self hκ]
    obtain ⟨β⟩ := Cardinal.eq.mp (hR₀c.trans hcompl.symm)
    set eEquiv : Idx κ ≃ ↥(Set.range e) := Equiv.ofInjective e e.injective with heEquivdef
    set αe : ↥R₀ ≃ ↥(Set.range e) := ρ₀.symm.trans eEquiv with hαedef
    set φ : Idx κ × Idx κ ≃ Idx κ :=
      (Equiv.Set.sumCompl R₀).symm.trans ((αe.sumCongr β).trans (Equiv.Set.sumCompl (Set.range e)))
      with hφdef
    have hφ_row : ∀ i, φ (i, j₀) = e i := by
      intro i
      have hmem : (i, j₀) ∈ R₀ := ⟨i, rfl⟩
      have h1 : (Equiv.Set.sumCompl R₀).symm (i, j₀) = Sum.inl ⟨(i, j₀), hmem⟩ :=
        Equiv.Set.sumCompl_symm_apply_of_mem hmem
      have h2 : ρ₀.symm ⟨(i, j₀), hmem⟩ = i := by
        apply ρ₀.injective
        rw [Equiv.apply_symm_apply]
        rfl
      show (Equiv.Set.sumCompl (Set.range e))
          ((αe.sumCongr β) ((Equiv.Set.sumCompl R₀).symm (i, j₀))) = e i
      rw [h1, Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
      show (eEquiv (ρ₀.symm ⟨(i, j₀), hmem⟩) : Idx κ) = e i
      rw [h2]
      rfl
    set Y : Idx κ → Idx κ → H := fun i j => if j = j₀ then z i else 0 with hYdef
    have hYsum : ∀ i, ksum (κ := κ) (Y i) = z i := fun i =>
      (ksum_single j₀ (Y i) (fun j hj => if_neg hj)).trans (if_pos rfl)
    have hkey : ∀ k, Y (φ.symm k).1 (φ.symm k).2 = Function.extend e z 0 k := by
      intro k
      by_cases hk : ∃ i, e i = k
      · obtain ⟨i, hi⟩ := hk
        have hφsymm : φ.symm k = (i, j₀) := by
          rw [← hi, ← hφ_row i, Equiv.symm_apply_apply]
        rw [hφsymm]
        show (if j₀ = j₀ then z i else 0) = Function.extend e z 0 k
        rw [if_pos rfl, ← hi, e.injective.extend_apply]
      · have hnotR₀ : φ.symm k ∉ R₀ := by
          rintro ⟨i, hi⟩
          dsimp only at hi
          apply hk
          refine ⟨i, ?_⟩
          rw [← hφ_row i, hi, Equiv.apply_symm_apply]
        have hne : (φ.symm k).2 ≠ j₀ := by
          intro heq
          exact hnotR₀ ⟨(φ.symm k).1, by rw [← heq]⟩
        show (if (φ.symm k).2 = j₀ then z (φ.symm k).1 else 0) = Function.extend e z 0 k
        rw [if_neg hne, Function.extend_apply' z (0 : Idx κ → H) k hk]
        rfl
    calc ksum (κ := κ) (Function.extend e z 0)
        = ksum (κ := κ) (fun k => Y (φ.symm k).1 (φ.symm k).2) := by
          congr 1; funext k; exact (hkey k).symm
      _ = ksum (κ := κ) (fun i => ksum (κ := κ) (Y i)) := (ksum_sigma Y φ).symm
      _ = ksum (κ := κ) z := by congr 1; funext i; exact hYsum i
  -- reduce the general case to Case A via a fixed "generic" embedding with big complement
  have hSum : #(Idx κ ⊕ Idx κ) = κ := by
    rw [mk_sum]
    simp [Cardinal.add_eq_self hκ]
  obtain ⟨Φ⟩ := Cardinal.eq.mp (hSum.trans (mk_Idx κ).symm)
  have hΦinj : Function.Injective (fun i : Idx κ => Φ (Sum.inl i)) := fun a b hab =>
    Sum.inl_injective (Φ.injective hab)
  set h : Idx κ ↪ Idx κ := ⟨fun i => Φ (Sum.inl i), hΦinj⟩ with hhdef
  have hrangeh : Set.range h = Φ '' Set.range (Sum.inl : Idx κ → Idx κ ⊕ Idx κ) := by
    ext y
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Sum.inl i, ⟨i, rfl⟩, hi⟩
    · rintro ⟨s, ⟨i, hi⟩, hs⟩
      exact ⟨i, by show Φ (Sum.inl i) = y; rw [hi]; exact hs⟩
  have hcomplh : #(↥(Set.range h)ᶜ) = κ := by
    rw [hrangeh, ← Equiv.image_compl, Set.isCompl_range_inl_range_inr.compl_eq,
      Cardinal.mk_image_eq Φ.injective, Cardinal.mk_range_eq Sum.inr Sum.inr_injective, mk_Idx]
  set g'' : Idx κ ↪ Idx κ := ⟨(h : Idx κ → Idx κ) ∘ (g : Idx κ → Idx κ),
    h.injective.comp g.injective⟩ with hg''def
  have hrange_sub : Set.range g'' ⊆ Set.range h := by
    rintro k ⟨i, hi⟩
    exact ⟨g i, hi⟩
  have hcomplg'' : #(↥(Set.range g'')ᶜ) = κ := by
    have hsub : (Set.range h)ᶜ ⊆ (Set.range g'')ᶜ := Set.compl_subset_compl.mpr hrange_sub
    have hle1 : κ ≤ #(↥(Set.range g'')ᶜ) := hcomplh.symm.trans_le (Cardinal.mk_le_mk_of_subset hsub)
    have hle2 : #(↥(Set.range g'')ᶜ) ≤ κ := (Cardinal.mk_set_le _).trans_eq (mk_Idx κ)
    exact le_antisymm hle2 hle1
  have e1 := caseA h hcomplh (Function.extend g x 0)
  have e2 := caseA g'' hcomplg'' x
  have hraw := Function.Injective.extend_comp g.injective h.injective x (0 : Idx κ → H)
  have h0 : (0 : Idx κ → H) ∘ (h : Idx κ → Idx κ) = (0 : Idx κ → H) := by
    funext i; simp
  rw [h0] at hraw
  have hcomp : Function.extend (⇑g'') x 0 = Function.extend (⇑h) (Function.extend (⇑g) x 0) 0 :=
    hraw
  rw [hcomp] at e2
  rw [← e1, ← e2]

/-- Two embeddings of the same index type into `Idx κ`, both with complement of cardinality
`κ`, give the same zero-padded `κ`-sum.  This is the workhorse behind `sumOf_eq_extend`. -/
theorem ksum_extend_congr {ι : Type u} (hι : #ι ≤ κ) (z : ι → H) (e1 e2 : ι ↪ Idx κ)
    (h1 : #(↥(Set.range e1)ᶜ) = κ) (h2 : #(↥(Set.range e2)ᶜ) = κ) :
    ksum (κ := κ) (Function.extend e1 z 0) = ksum (κ := κ) (Function.extend e2 z 0) := by
  have hκ := aleph0_le (κ := κ) (H := H)
  have hInf : Infinite (Idx κ) := Cardinal.infinite_iff.mpr (by rw [mk_Idx]; exact hκ)
  obtain ⟨j₀⟩ := nonempty_Idx hκ
  set R₀ : Set (Idx κ × Idx κ) := Set.range (fun i : ι => (emb hι i, j₀)) with hR₀def
  have hR₀inj : Function.Injective (fun i : ι => (emb hι i, j₀)) := fun a b hab =>
    (emb hι).injective (Prod.ext_iff.mp hab).1
  set ρ₀ : ι ≃ ↥R₀ := Equiv.ofInjective _ hR₀inj with hρ₀def
  have hR₀c : #(↥R₀ᶜ) = κ := by
    set FR : Set (Idx κ × Idx κ) := Set.range (fun i : Idx κ => (i, j₀)) with hFRdef
    have hsub : FRᶜ ⊆ R₀ᶜ := by
      apply Set.compl_subset_compl.mpr
      rintro p ⟨i, hi⟩
      exact ⟨emb hι i, hi⟩
    have hFRc : #(↥FRᶜ) = κ := by
      set pt : Set (Idx κ) := {j₀} with hptdef
      have hptlt : #(pt : Set (Idx κ)) < #(Idx κ) :=
        (mk_singleton j₀).trans_lt (lt_of_lt_of_le one_lt_aleph0 (by rw [mk_Idx]; exact hκ))
      have hptc : #(↥ptᶜ) = #(Idx κ) := mk_compl_of_infinite pt hptlt
      set rowComplEquiv : ↥FRᶜ ≃ Idx κ × ↥ptᶜ :=
        { toFun := fun p => (p.1.1, ⟨p.1.2, fun hmem => p.2 ⟨p.1.1, Prod.ext rfl hmem.symm⟩⟩)
          invFun := fun q => ⟨(q.1, q.2.1), fun hmem => q.2.2 (by
            obtain ⟨i, hi⟩ := hmem
            exact (Prod.ext_iff.mp hi).2.symm)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl } with hrowComplEquivdef
      have heq := Cardinal.mk_congr rowComplEquiv
      rw [heq, Cardinal.mk_prod, hptc, mk_Idx]
      simp [Cardinal.mul_eq_self hκ]
    have hle1 : κ ≤ #(↥R₀ᶜ) := hFRc.symm.trans_le (Cardinal.mk_le_mk_of_subset hsub)
    have hle2 : #(↥R₀ᶜ) ≤ κ := (Cardinal.mk_set_le _).trans_eq (by
      rw [Cardinal.mk_prod, mk_Idx]; simp [Cardinal.mul_eq_self hκ])
    exact le_antisymm hle2 hle1
  set Y : Idx κ → Idx κ → H := fun a b =>
    if hmem : (a, b) ∈ R₀ then z (ρ₀.symm ⟨(a, b), hmem⟩) else 0 with hYdef
  have match_e : ∀ (e : ι ↪ Idx κ), #(↥(Set.range e)ᶜ) = κ →
      ksum (κ := κ) (fun i => ksum (κ := κ) (Y i)) = ksum (κ := κ) (Function.extend e z 0) := by
    intro e hcompl
    obtain ⟨β⟩ := Cardinal.eq.mp (hR₀c.trans hcompl.symm)
    set eEquiv : ι ≃ ↥(Set.range e) := Equiv.ofInjective e e.injective with heEquivdef
    set αe : ↥R₀ ≃ ↥(Set.range e) := ρ₀.symm.trans eEquiv with hαedef
    set φ : Idx κ × Idx κ ≃ Idx κ :=
      (Equiv.Set.sumCompl R₀).symm.trans ((αe.sumCongr β).trans (Equiv.Set.sumCompl (Set.range e)))
      with hφdef
    have hφ_row : ∀ i : ι, φ (emb hι i, j₀) = e i := by
      intro i
      have hmem : (emb hι i, j₀) ∈ R₀ := ⟨i, rfl⟩
      have h1eq : (Equiv.Set.sumCompl R₀).symm (emb hι i, j₀) = Sum.inl ⟨(emb hι i, j₀), hmem⟩ :=
        Equiv.Set.sumCompl_symm_apply_of_mem hmem
      have h2eq : ρ₀.symm ⟨(emb hι i, j₀), hmem⟩ = i := by
        apply ρ₀.injective
        rw [Equiv.apply_symm_apply]
        rfl
      show (Equiv.Set.sumCompl (Set.range e))
          ((αe.sumCongr β) ((Equiv.Set.sumCompl R₀).symm (emb hι i, j₀))) = e i
      rw [h1eq, Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
      show (eEquiv (ρ₀.symm ⟨(emb hι i, j₀), hmem⟩) : Idx κ) = e i
      rw [h2eq]
      rfl
    have hkey : ∀ k, Y (φ.symm k).1 (φ.symm k).2 = Function.extend e z 0 k := by
      intro k
      by_cases hk : ∃ i, e i = k
      · obtain ⟨i, hi⟩ := hk
        have hmem : (emb hι i, j₀) ∈ R₀ := ⟨i, rfl⟩
        have hφsymm : φ.symm k = (emb hι i, j₀) := by
          rw [← hi, ← hφ_row i, Equiv.symm_apply_apply]
        have hρ : ρ₀.symm ⟨(emb hι i, j₀), hmem⟩ = i := by
          apply ρ₀.injective
          rw [Equiv.apply_symm_apply]
          rfl
        show Y (φ.symm k).1 (φ.symm k).2 = Function.extend e z 0 k
        rw [hφsymm, hYdef]
        show (if hmem' : (emb hι i, j₀) ∈ R₀ then z (ρ₀.symm ⟨(emb hι i, j₀), hmem'⟩) else 0)
          = Function.extend e z 0 k
        rw [dif_pos hmem, hρ, ← hi, e.injective.extend_apply]
      · have hnotR₀ : φ.symm k ∉ R₀ := by
          rintro ⟨i, hi⟩
          dsimp only at hi
          apply hk
          refine ⟨i, ?_⟩
          rw [← hφ_row i, hi, Equiv.apply_symm_apply]
        show Y (φ.symm k).1 (φ.symm k).2 = Function.extend e z 0 k
        rw [hYdef]
        show (if hmem : ((φ.symm k).1, (φ.symm k).2) ∈ R₀ then
            z (ρ₀.symm ⟨((φ.symm k).1, (φ.symm k).2), hmem⟩) else 0) = Function.extend e z 0 k
        rw [dif_neg hnotR₀, Function.extend_apply' z (0 : Idx κ → H) k hk]
        rfl
    calc ksum (κ := κ) (fun i => ksum (κ := κ) (Y i))
        = ksum (κ := κ) (fun k => Y (φ.symm k).1 (φ.symm k).2) := ksum_sigma Y φ
      _ = ksum (κ := κ) (Function.extend e z 0) := by
          congr 1; funext k; exact hkey k
  exact (match_e e1 h1).symm.trans (match_e e2 h2)

/-- The sum of a family indexed by an arbitrary type of cardinality `≤ κ`. -/
noncomputable def sumOf {ι : Type u} (h : #ι ≤ κ) (x : ι → H) : H :=
  ksum (κ := κ) (Function.extend (emb h) x 0)

/-- `sumOf` may be computed using *any* embedding of the index type into `Idx κ`. -/
theorem sumOf_eq_extend {ι : Type u} (h : #ι ≤ κ) (e : ι ↪ Idx κ) (x : ι → H) :
    sumOf (κ := κ) h x = ksum (κ := κ) (Function.extend e x 0) := by
  show ksum (κ := κ) (Function.extend (emb h) x 0) = ksum (κ := κ) (Function.extend e x 0)
  have hκ := aleph0_le (κ := κ) (H := H)
  -- a fixed self-embedding of `Idx κ` with complement of cardinality `κ`
  have hSum : #(Idx κ ⊕ Idx κ) = κ := by
    rw [mk_sum]; simp [Cardinal.add_eq_self hκ]
  obtain ⟨Φ⟩ := Cardinal.eq.mp (hSum.trans (mk_Idx κ).symm)
  have hΦinj : Function.Injective (fun i : Idx κ => Φ (Sum.inl i)) := fun a b hab =>
    Sum.inl_injective (Φ.injective hab)
  set Hgen : Idx κ ↪ Idx κ := ⟨fun i => Φ (Sum.inl i), hΦinj⟩ with hHgendef
  have hrangeHgen : Set.range Hgen = Φ '' Set.range (Sum.inl : Idx κ → Idx κ ⊕ Idx κ) := by
    ext y
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Sum.inl i, ⟨i, rfl⟩, hi⟩
    · rintro ⟨s, ⟨i, hi⟩, hs⟩
      exact ⟨i, by show Φ (Sum.inl i) = y; rw [hi]; exact hs⟩
  have hcomplHgen : #(↥(Set.range Hgen)ᶜ) = κ := by
    rw [hrangeHgen, ← Equiv.image_compl, Set.isCompl_range_inl_range_inr.compl_eq,
      Cardinal.mk_image_eq Φ.injective, Cardinal.mk_range_eq Sum.inr Sum.inr_injective, mk_Idx]
  -- boost both `emb h` and `e` by composing with `Hgen`, forcing big complements
  set G1 : ι ↪ Idx κ := ⟨(Hgen : Idx κ → Idx κ) ∘ (emb h : ι → Idx κ),
    Hgen.injective.comp (emb h).injective⟩ with hG1def
  set G2 : ι ↪ Idx κ := ⟨(Hgen : Idx κ → Idx κ) ∘ (e : ι → Idx κ),
    Hgen.injective.comp e.injective⟩ with hG2def
  have hcomplBoost : ∀ f : ι ↪ Idx κ,
      Set.range (⟨(Hgen : Idx κ → Idx κ) ∘ (f : ι → Idx κ), Hgen.injective.comp f.injective⟩ :
        ι ↪ Idx κ) ⊆ Set.range Hgen := by
    intro f
    rintro k ⟨i, hi⟩
    exact ⟨f i, hi⟩
  have hcomplG1 : #(↥(Set.range G1)ᶜ) = κ := by
    have hsub : (Set.range Hgen)ᶜ ⊆ (Set.range G1)ᶜ :=
      Set.compl_subset_compl.mpr (hcomplBoost (emb h))
    have hle1 : κ ≤ #(↥(Set.range G1)ᶜ) := hcomplHgen.symm.trans_le (Cardinal.mk_le_mk_of_subset hsub)
    have hle2 : #(↥(Set.range G1)ᶜ) ≤ κ := (Cardinal.mk_set_le _).trans_eq (mk_Idx κ)
    exact le_antisymm hle2 hle1
  have hcomplG2 : #(↥(Set.range G2)ᶜ) = κ := by
    have hsub : (Set.range Hgen)ᶜ ⊆ (Set.range G2)ᶜ :=
      Set.compl_subset_compl.mpr (hcomplBoost e)
    have hle1 : κ ≤ #(↥(Set.range G2)ᶜ) := hcomplHgen.symm.trans_le (Cardinal.mk_le_mk_of_subset hsub)
    have hle2 : #(↥(Set.range G2)ᶜ) ≤ κ := (Cardinal.mk_set_le _).trans_eq (mk_Idx κ)
    exact le_antisymm hle2 hle1
  have hcompeq :
      ksum (κ := κ) (Function.extend (⇑G1) x 0) = ksum (κ := κ) (Function.extend (⇑G2) x 0) :=
    ksum_extend_congr h x G1 G2 hcomplG1 hcomplG2
  have hcomp1 :
      Function.extend (⇑G1) x 0 = Function.extend (⇑Hgen) (Function.extend (⇑(emb h)) x 0) 0 := by
    have hraw := Function.Injective.extend_comp (emb h).injective Hgen.injective x (0 : Idx κ → H)
    have h0 : (0 : Idx κ → H) ∘ (⇑Hgen) = (0 : Idx κ → H) := by funext i; simp
    rw [h0] at hraw
    exact hraw
  have hcomp2 : Function.extend (⇑G2) x 0 = Function.extend (⇑Hgen) (Function.extend (⇑e) x 0) 0 := by
    have hraw := Function.Injective.extend_comp e.injective Hgen.injective x (0 : Idx κ → H)
    have h0 : (0 : Idx κ → H) ∘ (⇑Hgen) = (0 : Idx κ → H) := by funext i; simp
    rw [h0] at hraw
    exact hraw
  rw [hcomp1, hcomp2] at hcompeq
  rw [ksum_extend Hgen (Function.extend (⇑(emb h)) x 0),
    ksum_extend Hgen (Function.extend (⇑e) x 0)] at hcompeq
  exact hcompeq

@[simp] theorem sumOf_zero {ι : Type u} (h : #ι ≤ κ) :
    sumOf (κ := κ) (H := H) h (fun _ => 0) = 0 := by
  show ksum (κ := κ) (Function.extend (emb h) (fun _ : ι => (0 : H)) 0) = 0
  have heq : Function.extend (emb h) (fun _ : ι => (0 : H)) 0 = fun _ => (0 : H) := by
    funext k
    by_cases hk : ∃ i, emb h i = k
    · obtain ⟨i, hi⟩ := hk
      rw [← hi, (emb h).injective.extend_apply]
    · rw [Function.extend_apply' (fun _ : ι => (0 : H)) (0 : Idx κ → H) k hk]
      rfl
  rw [heq]
  exact ksum_zero

/-- `sumOf` is invariant under reindexing along an equivalence. -/
theorem sumOf_equiv {ι ι' : Type u} (h : #ι ≤ κ) (h' : #ι' ≤ κ) (e : ι' ≃ ι) (x : ι → H) :
    sumOf (κ := κ) h x = sumOf (κ := κ) h' (x ∘ e) := by
  rw [sumOf_eq_extend h' (e.toEmbedding.trans (emb h)) (x ∘ e)]
  show ksum (κ := κ) (Function.extend (emb h) x 0) = _
  congr 1
  funext k
  by_cases hk : ∃ i, emb h i = k
  · obtain ⟨i, hi⟩ := hk
    have hLHS : Function.extend (emb h) x 0 k = x i := by
      rw [← hi]; exact (emb h).injective.extend_apply x 0 i
    have hi' : (e.toEmbedding.trans (emb h)) (e.symm i) = k := by
      show emb h (e (e.symm i)) = k
      rw [Equiv.apply_symm_apply]; exact hi
    have hRHS : Function.extend (e.toEmbedding.trans (emb h)) (x ∘ e) 0 k = x i := by
      rw [← hi', (e.toEmbedding.trans (emb h)).injective.extend_apply]
      show x (e (e.symm i)) = x i
      rw [Equiv.apply_symm_apply]
    rw [hLHS, hRHS]
  · rw [Function.extend_apply' x (0 : Idx κ → H) k hk]
    symm
    apply Function.extend_apply'
    rintro ⟨i', hi'⟩
    exact hk ⟨e i', hi'⟩

theorem sumOf_Idx (x : Idx κ → H) : sumOf (κ := κ) (le_of_eq (mk_Idx κ)) x = ksum (κ := κ) x := by
  rw [sumOf_eq_extend (le_of_eq (mk_Idx κ)) (Equiv.refl (Idx κ)).toEmbedding x]
  have heq : Function.extend (⇑(Equiv.refl (Idx κ)).toEmbedding) x (0 : Idx κ → H) = x := by
    have hid : (⇑(Equiv.refl (Idx κ)).toEmbedding : Idx κ → Idx κ) = id := rfl
    rw [hid, Function.extend_id]
  rw [heq]

/-- Terms with value `0` may be discarded. -/
theorem sumOf_subtype_support {ι : Type u} (h : #ι ≤ κ) (x : ι → H)
    (h' : #(Function.support x) ≤ κ) :
    sumOf (κ := κ) h x = sumOf (κ := κ) h' (fun i : Function.support x => x i) := by
  rw [sumOf_eq_extend h' ((Function.Embedding.subtype _).trans (emb h))
    (fun i : Function.support x => x i)]
  show ksum (κ := κ) (Function.extend (emb h) x 0) = _
  congr 1
  funext k
  by_cases hk : ∃ i, emb h i = k
  · obtain ⟨i, hi⟩ := hk
    rw [← hi, (emb h).injective.extend_apply]
    by_cases hxi : x i = 0
    · have hne : ¬ ∃ i' : Function.support x,
          ((Function.Embedding.subtype _).trans (emb h)) i' = emb h i := by
        rintro ⟨i', hi'⟩
        have hival : (i' : ι) = i := (emb h).injective hi'
        apply i'.2
        rw [hival]
        exact hxi
      rw [Function.extend_apply' (fun i : Function.support x => x i) (0 : Idx κ → H)
        (emb h i) hne, hxi]
      rfl
    · have hmem : i ∈ Function.support x := hxi
      have hival : ((Function.Embedding.subtype _).trans (emb h))
          (⟨i, hmem⟩ : Function.support x) = emb h i := rfl
      rw [← hival, ((Function.Embedding.subtype _).trans (emb h)).injective.extend_apply]
  · rw [Function.extend_apply' x (0 : Idx κ → H) k hk]
    symm
    apply Function.extend_apply'
    rintro ⟨i', hi'⟩
    exact hk ⟨i', hi'⟩

@[simp] theorem sumOf_unique {ι : Type u} [Unique ι] (h : #ι ≤ κ) (x : ι → H) :
    sumOf (κ := κ) h x = x default := by
  show ksum (κ := κ) (Function.extend (emb h) x 0) = x default
  have hproof : ∀ j : Idx κ, j ≠ emb h default → Function.extend (emb h) x 0 j = 0 := by
    intro j hj
    by_cases hjk : ∃ i, emb h i = j
    · obtain ⟨i, hi⟩ := hjk
      exact absurd (by rw [← hi, Unique.eq_default i]) hj
    · exact Function.extend_apply' _ _ _ hjk
  rw [ksum_single (emb h default) _ hproof, (emb h).injective.extend_apply]

/-- The general associativity law for `sumOf`, i.e. the statement that a `κ`-sum may be
computed by first summing over the fibres of a partition. -/
theorem sumOf_sigma {ι : Type u} {ρ : ι → Type u} (h : #ι ≤ κ) (hρ : ∀ i, #(ρ i) ≤ κ)
    (hσ : #(Σ i, ρ i) ≤ κ) (x : ∀ i, ρ i → H) :
    sumOf (κ := κ) h (fun i => sumOf (κ := κ) (hρ i) (x i))
      = sumOf (κ := κ) hσ (fun p : Σ i, ρ i => x p.1 p.2) := by
  have hκ := aleph0_le (κ := κ) (H := H)
  set e : ι ↪ Idx κ := emb h with hedef
  set f : ∀ i, ρ i ↪ Idx κ := fun i => emb (hρ i) with hfdef
  set π : Idx κ × Idx κ ≃ Idx κ := pairEquiv hκ with hπdef
  set E : (Σ i, ρ i) ↪ Idx κ := ⟨fun p => π (e p.1, f p.1 p.2), by
    rintro ⟨i1, r1⟩ ⟨i2, r2⟩ hEq
    have hpair : (e i1, f i1 r1) = (e i2, f i2 r2) := π.injective hEq
    have hi : i1 = i2 := e.injective (Prod.ext_iff.mp hpair).1
    subst hi
    have hr : r1 = r2 := (f i1).injective (Prod.ext_iff.mp hpair).2
    subst hr
    rfl⟩ with hEdef
  set W : ∀ i, Idx κ → H := fun i => Function.extend (f i) (x i) 0 with hWdef
  set G : Idx κ → (Idx κ → H) := Function.extend e W (fun _ => (0 : Idx κ → H)) with hGdef
  have hGa : ∀ a, ksum (κ := κ) (G a) = Function.extend e (fun i => ksum (κ := κ) (W i)) 0 a := by
    intro a
    by_cases ha : ∃ i, e i = a
    · obtain ⟨i, hi⟩ := ha
      have h1 : G a = W i := by rw [← hi, hGdef, e.injective.extend_apply]
      have h2 : Function.extend e (fun i => ksum (κ := κ) (W i)) 0 a = ksum (κ := κ) (W i) := by
        rw [← hi, e.injective.extend_apply]
      rw [h1, h2]
    · have h1 : G a = fun _ => (0 : H) := by
        rw [hGdef]
        exact Function.extend_apply' W (fun _ => (0 : Idx κ → H)) a ha
      have h2 : Function.extend e (fun i => ksum (κ := κ) (W i)) 0 a = 0 :=
        Function.extend_apply' (fun i => ksum (κ := κ) (W i)) (0 : Idx κ → H) a ha
      rw [h1, h2]
      exact ksum_zero
  have hGk : ∀ k, G (π.symm k).1 (π.symm k).2 = Function.extend E (fun p => x p.1 p.2) 0 k := by
    intro k
    by_cases ha : ∃ i, e i = (π.symm k).1
    · obtain ⟨i, hi⟩ := ha
      have hGaeq : G (π.symm k).1 = W i := by rw [← hi, hGdef, e.injective.extend_apply]
      rw [hGaeq]
      by_cases hb : ∃ r, f i r = (π.symm k).2
      · obtain ⟨r, hr⟩ := hb
        have hWeq : W i (π.symm k).2 = x i r := by
          rw [← hr]
          show Function.extend (f i) (x i) 0 (f i r) = x i r
          exact (f i).injective.extend_apply (x i) 0 r
        rw [hWeq]
        have hEk : E ⟨i, r⟩ = k := by
          show π (e i, f i r) = k
          rw [hi, hr]
          exact Equiv.apply_symm_apply π k
        rw [← hEk, E.injective.extend_apply]
      · have hWeq : W i (π.symm k).2 = 0 :=
          Function.extend_apply' (x i) (0 : Idx κ → H) (π.symm k).2 hb
        rw [hWeq]
        symm
        apply Function.extend_apply'
        rintro ⟨⟨i', r'⟩, hp⟩
        have heqp : (e i', f i' r') = π.symm k := by
          rw [← hp]; exact (Equiv.symm_apply_apply π (e i', f i' r')).symm
        have hi' : e i' = (π.symm k).1 := congrArg Prod.fst heqp
        have hii : i' = i := e.injective (hi'.trans hi.symm)
        subst hii
        exact hb ⟨r', congrArg Prod.snd heqp⟩
    · have hGaeq : G (π.symm k).1 = fun _ => (0 : H) := by
        rw [hGdef]
        exact Function.extend_apply' W (fun _ => (0 : Idx κ → H)) (π.symm k).1 ha
      rw [hGaeq]
      symm
      apply Function.extend_apply'
      rintro ⟨⟨i', r'⟩, hp⟩
      apply ha
      refine ⟨i', ?_⟩
      have heqp : (e i', f i' r') = π.symm k := by
        rw [← hp]; exact (Equiv.symm_apply_apply π (e i', f i' r')).symm
      exact congrArg Prod.fst heqp
  have step1 : sumOf (κ := κ) h (fun i => sumOf (κ := κ) (hρ i) (x i))
      = ksum (κ := κ) (fun a => ksum (κ := κ) (G a)) := by
    show ksum (κ := κ) (Function.extend e (fun i => ksum (κ := κ) (W i)) 0)
      = ksum (κ := κ) (fun a => ksum (κ := κ) (G a))
    congr 1
    funext a
    exact (hGa a).symm
  have step2 : ksum (κ := κ) (fun a => ksum (κ := κ) (G a))
      = ksum (κ := κ) (fun k => G (π.symm k).1 (π.symm k).2) := ksum_sigma G π
  have step3 : ksum (κ := κ) (fun k => G (π.symm k).1 (π.symm k).2)
      = ksum (κ := κ) (Function.extend E (fun p => x p.1 p.2) 0) := by
    congr 1
    funext k
    exact hGk k
  have step4 : ksum (κ := κ) (Function.extend E (fun p => x p.1 p.2) 0)
      = sumOf (κ := κ) hσ (fun p : Σ i, ρ i => x p.1 p.2) :=
    (sumOf_eq_extend hσ E (fun p => x p.1 p.2)).symm
  rw [step1, step2, step3, step4]

/-- The special case of `sumOf_sigma` for a partition of the index set into subsets. -/
theorem sumOf_biUnion {ι J : Type u} (I : J → Set ι) (hdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q))
    (hcover : (⋃ p, I p) = Set.univ) (hJ : #J ≤ κ) (hι : #ι ≤ κ) (hI : ∀ p, #(I p) ≤ κ)
    (x : ι → H) :
    sumOf (κ := κ) hJ (fun p => sumOf (κ := κ) (hI p) (fun i : I p => x i))
      = sumOf (κ := κ) hι x := by
  set Φ : (Σ p : J, I p) ≃ ι := Equiv.ofBijective (fun q : Σ p : J, I p => (q.2 : ι))
    ⟨by
      rintro ⟨p1, i1, hi1⟩ ⟨p2, i2, hi2⟩ heq
      have heqι : i1 = i2 := heq
      by_cases hpp : p1 = p2
      · subst hpp
        subst heqι
        rfl
      · exact absurd hi2 (heqι ▸ (Set.disjoint_left.mp (hdisj p1 p2 hpp) hi1))
      , by
      intro i
      have hi : i ∈ (⋃ p, I p) := hcover ▸ Set.mem_univ i
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hi
      exact ⟨⟨p, ⟨i, hp⟩⟩, rfl⟩⟩ with hΦdef
  have hσ : #(Σ p : J, I p) ≤ κ := (Cardinal.mk_congr Φ).trans_le hι
  have hmain := sumOf_sigma hJ hI hσ (fun p (i : I p) => x (i : ι))
  have hequiv := sumOf_equiv hι hσ Φ x
  exact hmain.trans hequiv.symm

/-! ### Cardinal scalar multiplication (Definition 2.6, Lemma 2.7) -/

/-- `cmul α x` is the sum of `α` many copies of `x` (Definition 2.6). -/
noncomputable def cmul (α : Cardinal.{u}) (hα : α ≤ κ) (x : H) : H :=
  sumOf (κ := κ) (le_of_eq_of_le (mk_Idx α) hα) fun _ : Idx α => x

@[simp] theorem cmul_zero_cardinal (x : H) :
    cmul (κ := κ) 0 zero_le x = 0 := by
  show ksum (κ := κ) (Function.extend (emb (le_of_eq_of_le (mk_Idx (0 : Cardinal)) zero_le))
    (fun _ : Idx (0 : Cardinal) => x) 0) = 0
  have hEmpty : IsEmpty (Idx (0 : Cardinal)) := Cardinal.mk_eq_zero_iff.mp (mk_Idx 0)
  have heq : Function.extend (emb (le_of_eq_of_le (mk_Idx (0 : Cardinal)) zero_le))
      (fun _ : Idx (0 : Cardinal) => x) (0 : Idx κ → H) = fun _ => (0 : H) := by
    funext k
    apply Function.extend_apply'
    rintro ⟨i, _⟩
    exact hEmpty.false i
  rw [heq]
  exact ksum_zero

/-- Lemma 2.7(2). -/
theorem cmul_sumOf_cardinal {I : Type u} (hI : #I ≤ κ) (l : I → Cardinal.{u})
    (hl : ∀ i, l i ≤ κ) (hsum : (sum l) ≤ κ) (x : H) :
    cmul (κ := κ) (sum l) hsum x = sumOf (κ := κ) hI fun i => cmul (κ := κ) (l i) (hl i) x := by
  set ρ : I → Type u := fun i => Idx (l i) with hρdef
  have hρ : ∀ i, #(ρ i) ≤ κ := fun i => le_of_eq_of_le (mk_Idx (l i)) (hl i)
  have hmk : #(Σ i, ρ i) = Cardinal.sum l := by
    rw [mk_sigma]
    congr 1
    funext i
    exact mk_Idx (l i)
  have hσ : #(Σ i, ρ i) ≤ κ := le_of_eq_of_le hmk hsum
  obtain ⟨Ψ⟩ := Cardinal.eq.mp (hmk.trans (mk_Idx (Cardinal.sum l)).symm)
  have step1 : cmul (κ := κ) (sum l) hsum x
      = sumOf (κ := κ) hσ (fun _ : Σ i, ρ i => x) := by
    show sumOf (κ := κ) (le_of_eq_of_le (mk_Idx (Cardinal.sum l)) hsum) (fun _ => x) = _
    exact sumOf_equiv (le_of_eq_of_le (mk_Idx (Cardinal.sum l)) hsum) hσ Ψ (fun _ => x)
  have step2 : sumOf (κ := κ) hσ (fun _ : Σ i, ρ i => x)
      = sumOf (κ := κ) hI (fun i => cmul (κ := κ) (l i) (hl i) x) :=
    (sumOf_sigma hI hρ hσ (fun i (_ : ρ i) => x)).symm
  rw [step1, step2]

/-- Lemma 2.7(3). -/
theorem cmul_sumOf {I : Type u} (hI : #I ≤ κ) (α : Cardinal.{u}) (hα : α ≤ κ) (x : I → H) :
    cmul (κ := κ) α hα (sumOf (κ := κ) hI x)
      = sumOf (κ := κ) hI fun i => cmul (κ := κ) α hα (x i) := by
  have hκ := aleph0_le (κ := κ) (H := H)
  set hα' : #(Idx α) ≤ κ := le_of_eq_of_le (mk_Idx α) hα with hα'def
  have hprod1 : #(Idx α × I) ≤ κ := by
    have hmp : #(Idx α × I) = #(Idx α) * #I := by simp [Cardinal.mk_prod]
    rw [hmp]
    calc #(Idx α) * #I ≤ κ * κ := mul_le_mul' hα' hI
      _ = κ := Cardinal.mul_eq_self hκ
  have hprod2 : #(I × Idx α) ≤ κ := by
    have hmp : #(I × Idx α) = #I * #(Idx α) := by simp [Cardinal.mk_prod]
    rw [hmp]
    calc #I * #(Idx α) ≤ κ * κ := mul_le_mul' hI hα'
      _ = κ := Cardinal.mul_eq_self hκ
  have hσ1 : #(Σ _ : Idx α, I) ≤ κ :=
    (Cardinal.mk_congr (Equiv.sigmaEquivProd (Idx α) I)).trans_le hprod1
  have hσ2 : #(Σ _ : I, Idx α) ≤ κ :=
    (Cardinal.mk_congr (Equiv.sigmaEquivProd I (Idx α))).trans_le hprod2
  set Θ : (Σ _ : Idx α, I) ≃ (Σ _ : I, Idx α) :=
    (Equiv.sigmaEquivProd (Idx α) I).trans
      ((Equiv.prodComm (Idx α) I).trans (Equiv.sigmaEquivProd I (Idx α)).symm) with hΘdef
  have hΘapp : ∀ (a : Idx α) (i : I), Θ ⟨a, i⟩ = ⟨i, a⟩ := by
    intro a i
    simp [hΘdef]
  have stepA : cmul (κ := κ) α hα (sumOf (κ := κ) hI x)
      = sumOf (κ := κ) hσ1 (fun p : Σ _ : Idx α, I => x p.2) :=
    sumOf_sigma hα' (fun _ => hI) hσ1 (fun (_ : Idx α) (i : I) => x i)
  have stepB : sumOf (κ := κ) hI (fun i => cmul (κ := κ) α hα (x i))
      = sumOf (κ := κ) hσ2 (fun q : Σ _ : I, Idx α => x q.1) :=
    sumOf_sigma hI (fun _ => hα') hσ2 (fun (i : I) (_ : Idx α) => x i)
  have stepC : sumOf (κ := κ) hσ2 (fun q : Σ _ : I, Idx α => x q.1)
      = sumOf (κ := κ) hσ1 (fun p : Σ _ : Idx α, I => x p.2) := by
    rw [sumOf_equiv hσ2 hσ1 Θ (fun q : Σ _ : I, Idx α => x q.1)]
    congr 1
  rw [stepA, stepB, stepC]

/-! ### Reducedness (Lemma 2.8) -/

/-- A commutative monoid is *reduced* (or *conical*) if `a + b = 0` forces `a = b = 0`. -/
def IsConical (X : Type v) [AddCommMonoid X] : Prop :=
  ∀ a b : X, a + b = 0 → a = 0 ∧ b = 0

/-- A `sumOf` indexed by (a universe-lifted) `Bool` recovers the binary operation `+`. -/
theorem sumOf_two (a b : H) (hUB : #(ULift.{u} Bool) ≤ κ) :
    sumOf (κ := κ) hUB (fun p : ULift.{u} Bool => if p.down then a else b) = a + b := by
  have hκ := aleph0_le (κ := κ) (H := H)
  have hnt : Nontrivial (Idx κ) := by
    rw [← Cardinal.one_lt_iff_nontrivial, mk_Idx]
    exact lt_of_lt_of_le one_lt_aleph0 hκ
  obtain ⟨i0, i1, hne⟩ := hnt.exists_pair_ne
  set e : ULift.{u} Bool ↪ Idx κ := ⟨fun p => if p.down then i0 else i1, by
    intro p q hpq
    match p, q with
    | ⟨true⟩, ⟨true⟩ => rfl
    | ⟨false⟩, ⟨false⟩ => rfl
    | ⟨true⟩, ⟨false⟩ => exact absurd hpq hne
    | ⟨false⟩, ⟨true⟩ => exact absurd hpq.symm hne⟩ with hedef
  rw [sumOf_eq_extend hUB e (fun p : ULift.{u} Bool => if p.down then a else b)]
  have heq : Function.extend e (fun p : ULift.{u} Bool => if p.down then a else b) 0
      = fun j => if j = i0 then a else if j = i1 then b else 0 := by
    funext j
    by_cases hj : ∃ p, e p = j
    · obtain ⟨p, hp⟩ := hj
      match p with
      | ⟨true⟩ =>
        have hval : Function.extend e (fun p : ULift.{u} Bool => if p.down then a else b) 0 j
            = a := by
          rw [← hp]; exact e.injective.extend_apply _ _ _
        rw [hval]
        have hji0 : j = i0 := hp.symm
        rw [hji0]
        simp
      | ⟨false⟩ =>
        have hval : Function.extend e (fun p : ULift.{u} Bool => if p.down then a else b) 0 j
            = b := by
          rw [← hp]; exact e.injective.extend_apply _ _ _
        rw [hval]
        have hji1 : j = i1 := hp.symm
        rw [hji1]
        simp [hne.symm]
    · rw [Function.extend_apply' _ _ _ hj]
      have hj0 : j ≠ i0 := fun heq0 => hj ⟨⟨true⟩, heq0.symm⟩
      have hj1 : j ≠ i1 := fun heq1 => hj ⟨⟨false⟩, heq1.symm⟩
      simp [hj0, hj1]
  rw [heq]
  exact ksum_two a b i0 i1 hne

theorem mk_uLift_bool_le (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] :
    #(ULift.{u} Bool) ≤ κ := by
  have hκ := aleph0_le (κ := κ) (H := H)
  rw [Cardinal.mk_uLift]
  calc Cardinal.lift.{u, 0} (#Bool) ≤ Cardinal.lift.{u, 0} ℵ₀ :=
        Cardinal.lift_le.mpr Cardinal.mk_le_aleph0
    _ = ℵ₀ := Cardinal.lift_aleph0
    _ ≤ κ := hκ

/-- `κ`-many copies of `0` sum to `0`. -/
theorem cmul_top_zero (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] :
    cmul (κ := κ) κ le_rfl (0 : H) = 0 := by
  show sumOf (κ := κ) (le_of_eq_of_le (mk_Idx κ) le_rfl) (fun _ : Idx κ => (0 : H)) = 0
  exact sumOf_zero _

/-- Scaling by `κ` distributes over `+` (a consequence of Lemma 2.7(3) via `sumOf_two`). -/
theorem cmul_top_distrib (a b : H) :
    cmul (κ := κ) κ le_rfl (a + b)
      = cmul (κ := κ) κ le_rfl a + cmul (κ := κ) κ le_rfl b := by
  have hUB := mk_uLift_bool_le κ H
  rw [← sumOf_two a b hUB, cmul_sumOf hUB κ le_rfl (fun p : ULift.{u} Bool => if p.down then a else b)]
  have hcongr : (fun p : ULift.{u} Bool => cmul (κ := κ) κ le_rfl (if p.down then a else b))
      = fun p : ULift.{u} Bool =>
        if p.down then cmul (κ := κ) κ le_rfl a else cmul (κ := κ) κ le_rfl b := by
    funext p
    cases p.down <;> rfl
  rw [hcongr]
  exact sumOf_two _ _ hUB

/-- Lemma 2.8(2), the key idempotence step of the swindle: adding one more copy of `z` to
`κ`-many copies of `z` does not change the value. -/
theorem add_cmul_top_self (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] (z : H) :
    z + cmul (κ := κ) κ le_rfl z = cmul (κ := κ) κ le_rfl z := by
  have hκ := aleph0_le (κ := κ) (H := H)
  obtain ⟨j0⟩ := nonempty_Idx hκ
  have hInf : Infinite (Idx κ) := Cardinal.infinite_iff.mpr (by rw [mk_Idx]; exact hκ)
  have hcompl : #(↥({j0}ᶜ : Set (Idx κ))) = κ :=
    (mk_compl_of_infinite {j0} (by
      rw [mk_singleton]
      exact lt_of_lt_of_le one_lt_aleph0 (by rw [mk_Idx]; exact hκ))).trans (mk_Idx κ)
  set I : ULift.{u} Bool → Set (Idx κ) := fun p => match p with
    | ⟨true⟩ => ({j0} : Set (Idx κ))
    | ⟨false⟩ => {j0}ᶜ with hIdef
  have hdisj : ∀ p q : ULift.{u} Bool, p ≠ q → Disjoint (I p) (I q) := by
    intro p q hpq
    match p, q with
    | ⟨true⟩, ⟨true⟩ => exact absurd rfl hpq
    | ⟨false⟩, ⟨false⟩ => exact absurd rfl hpq
    | ⟨true⟩, ⟨false⟩ => exact disjoint_compl_right
    | ⟨false⟩, ⟨true⟩ => exact disjoint_compl_left
  have hcover : (⋃ p, I p) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    by_cases ha : a = j0
    · exact Set.mem_iUnion.mpr ⟨⟨true⟩, ha⟩
    · exact Set.mem_iUnion.mpr ⟨⟨false⟩, ha⟩
  have hJ := mk_uLift_bool_le κ H
  have hI : ∀ p : ULift.{u} Bool, #(I p) ≤ κ := by
    intro p
    match p with
    | ⟨true⟩ =>
      show #(({j0} : Set (Idx κ))) ≤ κ
      rw [mk_singleton]
      exact one_le_aleph0.trans hκ
    | ⟨false⟩ =>
      show #(({j0}ᶜ : Set (Idx κ))) ≤ κ
      exact hcompl.le
  have hmain := sumOf_biUnion I hdisj hcover hJ (le_of_eq (mk_Idx κ)) hI (fun _ : Idx κ => z)
  have hleftpt : sumOf (κ := κ) (hI (⟨true⟩ : ULift.{u} Bool))
      (fun i : I (⟨true⟩ : ULift.{u} Bool) => z) = z :=
    sumOf_unique (hI (⟨true⟩ : ULift.{u} Bool)) (fun _ => z)
  have hleftcompl : sumOf (κ := κ) (hI (⟨false⟩ : ULift.{u} Bool))
      (fun i : I (⟨false⟩ : ULift.{u} Bool) => z) = cmul (κ := κ) κ le_rfl z := by
    show sumOf (κ := κ) (hI (⟨false⟩ : ULift.{u} Bool)) (fun i : ({j0}ᶜ : Set (Idx κ)) => z) = _
    obtain ⟨Ψ⟩ := Cardinal.eq.mp (hcompl.trans (mk_Idx κ).symm)
    exact (sumOf_equiv (le_of_eq (mk_Idx κ)) (hI (⟨false⟩ : ULift.{u} Bool)) Ψ (fun _ => z)).symm
  have hleft : sumOf (κ := κ) hJ (fun p => sumOf (κ := κ) (hI p) (fun i : I p => z))
      = sumOf (κ := κ) hJ (fun p : ULift.{u} Bool =>
          if p.down then z else cmul (κ := κ) κ le_rfl z) := by
    congr 1
    funext p
    match p with
    | ⟨true⟩ => exact hleftpt
    | ⟨false⟩ => exact hleftcompl
  rw [hleft] at hmain
  rw [sumOf_two z (cmul (κ := κ) κ le_rfl z) hJ] at hmain
  exact hmain

/-- Lemma 2.8(1): a variant of the Eilenberg–Mazur swindle shows that every `κ`-monoid is
reduced.

Paper proof: if `x + y = 0` then
`x = x + κ·0 = x + κ(x+y) = (x + κx) + κy = κx + κy = κ(x+y) = 0`. -/
theorem isConical (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] : IsConical H := by
  intro x y hxy
  have hcz := cmul_top_zero κ H
  have step1 : x = cmul (κ := κ) κ le_rfl x + cmul (κ := κ) κ le_rfl y := by
    calc x = x + (0 : H) := (add_zero x).symm
      _ = x + cmul (κ := κ) κ le_rfl 0 := by rw [hcz]
      _ = x + cmul (κ := κ) κ le_rfl (x + y) := by rw [hxy]
      _ = x + (cmul (κ := κ) κ le_rfl x + cmul (κ := κ) κ le_rfl y) := by rw [cmul_top_distrib]
      _ = (x + cmul (κ := κ) κ le_rfl x) + cmul (κ := κ) κ le_rfl y := (add_assoc _ _ _).symm
      _ = cmul (κ := κ) κ le_rfl x + cmul (κ := κ) κ le_rfl y := by rw [add_cmul_top_self κ H x]
  have step2 : cmul (κ := κ) κ le_rfl x + cmul (κ := κ) κ le_rfl y = 0 := by
    rw [← cmul_top_distrib, hxy]; exact hcz
  have hx0 : x = 0 := step1.trans step2
  have hyx : y + x = 0 := by rw [add_comm]; exact hxy
  have step1' : y = cmul (κ := κ) κ le_rfl y + cmul (κ := κ) κ le_rfl x := by
    calc y = y + (0 : H) := (add_zero y).symm
      _ = y + cmul (κ := κ) κ le_rfl 0 := by rw [hcz]
      _ = y + cmul (κ := κ) κ le_rfl (y + x) := by rw [hyx]
      _ = y + (cmul (κ := κ) κ le_rfl y + cmul (κ := κ) κ le_rfl x) := by rw [cmul_top_distrib]
      _ = (y + cmul (κ := κ) κ le_rfl y) + cmul (κ := κ) κ le_rfl x := (add_assoc _ _ _).symm
      _ = cmul (κ := κ) κ le_rfl y + cmul (κ := κ) κ le_rfl x := by rw [add_cmul_top_self κ H y]
  have step2' : cmul (κ := κ) κ le_rfl y + cmul (κ := κ) κ le_rfl x = 0 := by
    rw [← cmul_top_distrib, hyx]; exact hcz
  have hy0 : y = 0 := step1'.trans step2'
  exact ⟨hx0, hy0⟩

/-- Applying `cmul κ` twice is the same as applying it once (since `κ * κ = κ`). -/
theorem cmul_top_idem (z : H) :
    cmul (κ := κ) κ le_rfl (cmul (κ := κ) κ le_rfl z) = cmul (κ := κ) κ le_rfl z := by
  have hκ := aleph0_le (κ := κ) (H := H)
  have hρ : ∀ _ : Idx κ, #(Idx κ) ≤ κ := fun _ => le_of_eq (mk_Idx κ)
  have hσm : #(Σ _ : Idx κ, Idx κ) = κ := by
    have heq1 : #(Σ _ : Idx κ, Idx κ) = #(Idx κ) * #(Idx κ) := by
      rw [Cardinal.mk_congr (Equiv.sigmaEquivProd (Idx κ) (Idx κ))]
      simp [Cardinal.mk_prod]
    rw [heq1, mk_Idx]
    exact Cardinal.mul_eq_self hκ
  have hσ : #(Σ _ : Idx κ, Idx κ) ≤ κ := le_of_eq hσm
  have step1 : cmul (κ := κ) κ le_rfl (cmul (κ := κ) κ le_rfl z)
      = sumOf (κ := κ) hσ (fun _ : Σ _ : Idx κ, Idx κ => z) :=
    sumOf_sigma (le_of_eq (mk_Idx κ)) hρ hσ (fun (_ _ : Idx κ) => z)
  obtain ⟨Ψ⟩ := Cardinal.eq.mp (hσm.trans (mk_Idx κ).symm)
  have step2 : sumOf (κ := κ) hσ (fun _ : Σ _ : Idx κ, Idx κ => z)
      = cmul (κ := κ) κ le_rfl z :=
    (sumOf_equiv (le_of_eq (mk_Idx κ)) hσ Ψ (fun _ => z)).symm
  rw [step1, step2]

/-- Lemma 2.8(2). -/
theorem add_cmul_top_eq {t₁ t₂ t₃ : H} (h : t₁ + t₂ = cmul (κ := κ) κ le_rfl t₃) :
    t₁ + cmul (κ := κ) κ le_rfl t₃ = cmul (κ := κ) κ le_rfl t₃ := by
  have hstep : cmul (κ := κ) κ le_rfl (t₁ + t₂) = cmul (κ := κ) κ le_rfl t₃ := by
    rw [h]; exact cmul_top_idem t₃
  calc t₁ + cmul (κ := κ) κ le_rfl t₃ = t₁ + cmul (κ := κ) κ le_rfl (t₁ + t₂) := by rw [← hstep]
    _ = t₁ + (cmul (κ := κ) κ le_rfl t₁ + cmul (κ := κ) κ le_rfl t₂) := by rw [cmul_top_distrib]
    _ = (t₁ + cmul (κ := κ) κ le_rfl t₁) + cmul (κ := κ) κ le_rfl t₂ := (add_assoc _ _ _).symm
    _ = cmul (κ := κ) κ le_rfl t₁ + cmul (κ := κ) κ le_rfl t₂ := by rw [add_cmul_top_self κ H t₁]
    _ = cmul (κ := κ) κ le_rfl (t₁ + t₂) := by rw [cmul_top_distrib]
    _ = cmul (κ := κ) κ le_rfl t₃ := hstep

/-! ### Homomorphisms, submonoids and generation (Section 2.1) -/

/-- A homomorphism of `κ`-monoids. -/
def IsKHom (κ : Cardinal.{u}) {H : Type v} {K : Type w} [KMonoid κ H] [KMonoid κ K]
    (f : H → K) : Prop :=
  f 0 = 0 ∧ ∀ x : Idx κ → H, f (ksum (κ := κ) x) = ksum (κ := κ) (f ∘ x)

/-- A `κ`-submonoid of a `κ`-monoid. -/
structure IsKSubmonoid (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) : Prop where
  zero_mem : (0 : H) ∈ S
  ksum_mem : ∀ x : Idx κ → H, (∀ i, x i ∈ S) → ksum (κ := κ) x ∈ S

/-- The `κ`-submonoid `⟨S⟩_κ` generated by a subset. -/
def kclosure (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) : Set H :=
  ⋂₀ {T | S ⊆ T ∧ IsKSubmonoid κ T}

theorem subset_kclosure {S : Set H} : S ⊆ kclosure κ S := by
  intro _ hx _ hT; exact hT.1 hx

/-- Definition 2.10: `H` is generated as a `κ`-monoid by `S`. -/
def KGenerates (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) : Prop :=
  kclosure κ S = Set.univ

end KMonoid

/-! ## `λ⁻`-monoids (Definition 2.18) -/

open KMonoid

/-- A `λ⁻`-monoid for a regular cardinal `λ`: a commutative monoid with a summation
operation for families indexed by `λ` whose support has cardinality *strictly less than*
`λ`.  The operation is made total by the junk convention that families with large support
sum to `0`. -/
class LMonoid (lam : Cardinal.{u}) (X : Type v) extends AddCommMonoid X where
  isRegular : lam.IsRegular
  lsum : (Idx lam → X) → X
  /-- Junk convention outside the intended domain. -/
  lsum_of_large : ∀ x, ¬ #(Function.support x) < lam → lsum x = 0
  /-- (B1). -/
  lsum_single : ∀ (i₀ : Idx lam) (x : Idx lam → X), (∀ i, i ≠ i₀ → x i = 0) → lsum x = x i₀
  /-- (B2). -/
  lsum_sigma : ∀ (x : Idx lam → Idx lam → X) (π : Idx lam × Idx lam ≃ Idx lam),
      #{i | ∃ j, x i j ≠ 0} < lam → #{j | ∃ i, x i j ≠ 0} < lam →
      lsum (fun i => lsum (x i)) = lsum fun k => x (π.symm k).1 (π.symm k).2
  /-- Compatibility of `+` with `Σ`; cf. `KMonoid.ksum_two`. -/
  lsum_two : ∀ (a b : X) (i₀ i₁ : Idx lam), i₀ ≠ i₁ →
      lsum (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b

namespace LMonoid

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X]

theorem aleph0_le {X : Type v} [LMonoid lam X] : ℵ₀ ≤ lam := (‹LMonoid lam X›.isRegular).aleph0_le

/-- Summation of a family indexed by an arbitrary type of cardinality `< λ`. -/
noncomputable def lsumOf {ι : Type u} (h : #ι < lam) (x : ι → X) : X :=
  lsum (Function.extend (emb h.le) x 0)

theorem lsumOf_eq_extend {ι : Type u} (h : #ι < lam) (e : ι ↪ Idx lam) (x : ι → X) :
    lsumOf (lam := lam) h x = lsum (Function.extend e x 0) := by
  show lsum (Function.extend (emb h.le) x 0) = lsum (Function.extend e x 0)
  have hlam0 := aleph0_le (lam := lam) (X := X)
  -- Any embedding out of a `< lam`-sized type has complement of full cardinality `lam`.
  have hbig : ∀ e' : ι ↪ Idx lam, #(↥(Set.range e')ᶜ) = lam := by
    intro e'
    have hlt : #(↥(Set.range e')) < lam := by
      rw [Cardinal.mk_range_eq e' e'.injective]; exact h
    have hle : #(↥(Set.range e')ᶜ) ≤ lam := (Cardinal.mk_set_le _).trans_eq (mk_Idx lam)
    by_contra hne
    have hlt2 : #(↥(Set.range e')ᶜ) < lam := lt_of_le_of_ne hle hne
    have hsum : #(↥(Set.range e')) + #(↥(Set.range e')ᶜ) = lam := by
      rw [Cardinal.mk_sum_compl]; exact mk_Idx lam
    exact absurd hsum (ne_of_lt (Cardinal.add_lt_of_lt hlam0 hlt hlt2))
  obtain ⟨j₀⟩ := nonempty_Idx hlam0
  set R₀ : Set (Idx lam × Idx lam) := Set.range (fun i : ι => (emb h.le i, j₀)) with hR₀def
  have hR₀inj : Function.Injective (fun i : ι => (emb h.le i, j₀)) := fun a b hab =>
    (emb h.le).injective (Prod.ext_iff.mp hab).1
  set ρ₀ : ι ≃ ↥R₀ := Equiv.ofInjective _ hR₀inj with hρ₀def
  have hR₀c : #(↥R₀ᶜ) = lam := by
    set FR : Set (Idx lam × Idx lam) := Set.range (fun i : Idx lam => (i, j₀)) with hFRdef
    have hsub : FRᶜ ⊆ R₀ᶜ := by
      apply Set.compl_subset_compl.mpr
      rintro p ⟨i, hi⟩
      exact ⟨emb h.le i, hi⟩
    have hInf : Infinite (Idx lam) := Cardinal.infinite_iff.mpr (by rw [mk_Idx]; exact hlam0)
    have hFRc : #(↥FRᶜ) = lam := by
      set pt : Set (Idx lam) := {j₀} with hptdef
      have hptlt : #(pt : Set (Idx lam)) < #(Idx lam) :=
        (mk_singleton j₀).trans_lt (lt_of_lt_of_le one_lt_aleph0 (by rw [mk_Idx]; exact hlam0))
      have hptc : #(↥ptᶜ) = #(Idx lam) := mk_compl_of_infinite pt hptlt
      set rowComplEquiv : ↥FRᶜ ≃ Idx lam × ↥ptᶜ :=
        { toFun := fun p => (p.1.1, ⟨p.1.2, fun hmem => p.2 ⟨p.1.1, Prod.ext rfl hmem.symm⟩⟩)
          invFun := fun q => ⟨(q.1, q.2.1), fun hmem => q.2.2 (by
            obtain ⟨i, hi⟩ := hmem
            exact (Prod.ext_iff.mp hi).2.symm)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl } with hrowComplEquivdef
      have heq := Cardinal.mk_congr rowComplEquiv
      rw [heq, Cardinal.mk_prod, hptc, mk_Idx]
      simp [Cardinal.mul_eq_self hlam0]
    have hle1 : lam ≤ #(↥R₀ᶜ) := hFRc.symm.trans_le (Cardinal.mk_le_mk_of_subset hsub)
    have hle2 : #(↥R₀ᶜ) ≤ lam := (Cardinal.mk_set_le _).trans_eq (by
      rw [Cardinal.mk_prod, mk_Idx]; simp [Cardinal.mul_eq_self hlam0])
    exact le_antisymm hle2 hle1
  set Y : Idx lam → Idx lam → X := fun a b =>
    if hmem : (a, b) ∈ R₀ then x (ρ₀.symm ⟨(a, b), hmem⟩) else 0 with hYdef
  have hYrow : #{a : Idx lam | ∃ b, Y a b ≠ 0} < lam := by
    have hsub : {a : Idx lam | ∃ b, Y a b ≠ 0} ⊆ Set.range (emb h.le) := by
      rintro a ⟨b, hab⟩
      by_contra hna
      apply hab
      have hnotR₀ : (a, b) ∉ R₀ := by
        rintro ⟨i, hi⟩; exact hna ⟨i, (Prod.ext_iff.mp hi).1⟩
      show Y a b = 0
      rw [hYdef]
      exact dif_neg hnotR₀
    calc #{a : Idx lam | ∃ b, Y a b ≠ 0} ≤ #(Set.range (emb h.le)) :=
          Cardinal.mk_le_mk_of_subset hsub
      _ = #ι := Cardinal.mk_range_eq (emb h.le) (emb h.le).injective
      _ < lam := h
  have hYcol : #{b : Idx lam | ∃ a, Y a b ≠ 0} < lam := by
    have hsub : {b : Idx lam | ∃ a, Y a b ≠ 0} ⊆ ({j₀} : Set (Idx lam)) := by
      rintro b ⟨a, hab⟩
      by_contra hnb
      apply hab
      have hnotR₀ : (a, b) ∉ R₀ := by
        rintro ⟨i, hi⟩; exact hnb (Prod.ext_iff.mp hi).2.symm
      show Y a b = 0
      rw [hYdef]
      exact dif_neg hnotR₀
    calc #{b : Idx lam | ∃ a, Y a b ≠ 0} ≤ #({j₀} : Set (Idx lam)) :=
          Cardinal.mk_le_mk_of_subset hsub
      _ = 1 := mk_singleton j₀
      _ < lam := lt_of_lt_of_le one_lt_aleph0 hlam0
  have hYsum : ∀ i, lsum (Y (emb h.le i)) = x i := by
    intro i
    have hmem : (emb h.le i, j₀) ∈ R₀ := ⟨i, rfl⟩
    have hval : Y (emb h.le i) j₀ = x i := by
      rw [hYdef]
      show (if hmem' : (emb h.le i, j₀) ∈ R₀ then x (ρ₀.symm ⟨(emb h.le i, j₀), hmem'⟩) else 0)
        = x i
      rw [dif_pos hmem]
      congr 1
      apply ρ₀.injective
      rw [Equiv.apply_symm_apply]
      rfl
    rw [lsum_single j₀ (Y (emb h.le i)) ?_ , hval]
    intro j hj
    rw [hYdef]
    show (if hmem' : (emb h.le i, j) ∈ R₀ then x (ρ₀.symm ⟨(emb h.le i, j), hmem'⟩) else 0) = 0
    apply dif_neg
    rintro ⟨i', hi'⟩
    exact hj (Prod.ext_iff.mp hi').2.symm
  have caseA : ∀ (e' : ι ↪ Idx lam), #(↥(Set.range e')ᶜ) = lam →
      lsum (fun a => lsum (Y a)) = lsum (Function.extend e' x 0) := by
    intro e' hcompl
    obtain ⟨β⟩ := Cardinal.eq.mp (hR₀c.trans hcompl.symm)
    set e'Equiv : ι ≃ ↥(Set.range e') := Equiv.ofInjective e' e'.injective with he'Equivdef
    set αe : ↥R₀ ≃ ↥(Set.range e') := ρ₀.symm.trans e'Equiv with hαedef
    set φ : Idx lam × Idx lam ≃ Idx lam :=
      (Equiv.Set.sumCompl R₀).symm.trans
        ((αe.sumCongr β).trans (Equiv.Set.sumCompl (Set.range e')))
      with hφdef
    have hφ_row : ∀ i : ι, φ (emb h.le i, j₀) = e' i := by
      intro i
      have hmem : (emb h.le i, j₀) ∈ R₀ := ⟨i, rfl⟩
      have h1eq : (Equiv.Set.sumCompl R₀).symm (emb h.le i, j₀) = Sum.inl ⟨(emb h.le i, j₀), hmem⟩ :=
        Equiv.Set.sumCompl_symm_apply_of_mem hmem
      have h2eq : ρ₀.symm ⟨(emb h.le i, j₀), hmem⟩ = i := by
        apply ρ₀.injective
        rw [Equiv.apply_symm_apply]
        rfl
      show (Equiv.Set.sumCompl (Set.range e'))
          ((αe.sumCongr β) ((Equiv.Set.sumCompl R₀).symm (emb h.le i, j₀))) = e' i
      rw [h1eq, Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
      show (e'Equiv (ρ₀.symm ⟨(emb h.le i, j₀), hmem⟩) : Idx lam) = e' i
      rw [h2eq]
      rfl
    have hkey : ∀ k, Y (φ.symm k).1 (φ.symm k).2 = Function.extend e' x 0 k := by
      intro k
      by_cases hk : ∃ i, e' i = k
      · obtain ⟨i, hi⟩ := hk
        have hmem : (emb h.le i, j₀) ∈ R₀ := ⟨i, rfl⟩
        have hφsymm : φ.symm k = (emb h.le i, j₀) := by
          rw [← hi, ← hφ_row i, Equiv.symm_apply_apply]
        have hρ : ρ₀.symm ⟨(emb h.le i, j₀), hmem⟩ = i := by
          apply ρ₀.injective
          rw [Equiv.apply_symm_apply]
          rfl
        show Y (φ.symm k).1 (φ.symm k).2 = Function.extend e' x 0 k
        rw [hφsymm, hYdef]
        show (if hmem' : (emb h.le i, j₀) ∈ R₀ then x (ρ₀.symm ⟨(emb h.le i, j₀), hmem'⟩) else 0)
          = Function.extend e' x 0 k
        rw [dif_pos hmem, hρ, ← hi, e'.injective.extend_apply]
      · have hnotR₀ : φ.symm k ∉ R₀ := by
          rintro ⟨i, hi⟩
          dsimp only at hi
          apply hk
          refine ⟨i, ?_⟩
          rw [← hφ_row i, hi, Equiv.apply_symm_apply]
        show Y (φ.symm k).1 (φ.symm k).2 = Function.extend e' x 0 k
        rw [hYdef]
        show (if hmem : ((φ.symm k).1, (φ.symm k).2) ∈ R₀ then
            x (ρ₀.symm ⟨((φ.symm k).1, (φ.symm k).2), hmem⟩) else 0) = Function.extend e' x 0 k
        rw [dif_neg hnotR₀, Function.extend_apply' x (0 : Idx lam → X) k hk]
        rfl
    calc lsum (fun a => lsum (Y a))
        = lsum (fun k => Y (φ.symm k).1 (φ.symm k).2) := lsum_sigma Y φ hYrow hYcol
      _ = lsum (Function.extend e' x 0) := by
          congr 1; funext k; exact hkey k
  exact (caseA (emb h.le) (hbig (emb h.le))).symm.trans (caseA e (hbig e))

@[simp] theorem lsumOf_zero {ι : Type u} (h : #ι < lam) :
    lsumOf (lam := lam) (X := X) h (fun _ => 0) = 0 := by
  show lsum (Function.extend (emb h.le) (fun _ : ι => (0 : X)) 0) = 0
  obtain ⟨j₀⟩ := nonempty_Idx (aleph0_le (lam := lam) (X := X))
  have heq : Function.extend (emb h.le) (fun _ : ι => (0 : X)) 0 = fun _ => (0 : X) := by
    funext k
    by_cases hk : ∃ i, emb h.le i = k
    · obtain ⟨i, hi⟩ := hk
      rw [← hi, (emb h.le).injective.extend_apply]
    · rw [Function.extend_apply' (fun _ : ι => (0 : X)) (0 : Idx lam → X) k hk]
      rfl
  rw [heq]
  exact lsum_single j₀ (fun _ => (0 : X)) (fun _ _ => rfl)

theorem lsumOf_equiv {ι ι' : Type u} (h : #ι < lam) (h' : #ι' < lam) (e : ι' ≃ ι) (x : ι → X) :
    lsumOf (lam := lam) h x = lsumOf (lam := lam) h' (x ∘ e) := by
  rw [lsumOf_eq_extend h' (e.toEmbedding.trans (emb h.le)) (x ∘ e)]
  show lsum (Function.extend (emb h.le) x 0) = _
  congr 1
  funext k
  by_cases hk : ∃ i, emb h.le i = k
  · obtain ⟨i, hi⟩ := hk
    have hLHS : Function.extend (emb h.le) x 0 k = x i := by
      rw [← hi]; exact (emb h.le).injective.extend_apply x 0 i
    have hi' : (e.toEmbedding.trans (emb h.le)) (e.symm i) = k := by
      show emb h.le (e (e.symm i)) = k
      rw [Equiv.apply_symm_apply]; exact hi
    have hRHS : Function.extend (e.toEmbedding.trans (emb h.le)) (x ∘ e) 0 k = x i := by
      rw [← hi', (e.toEmbedding.trans (emb h.le)).injective.extend_apply]
      show x (e (e.symm i)) = x i
      rw [Equiv.apply_symm_apply]
    rw [hLHS, hRHS]
  · rw [Function.extend_apply' x (0 : Idx lam → X) k hk]
    symm
    apply Function.extend_apply'
    rintro ⟨i', hi'⟩
    exact hk ⟨e i', hi'⟩

@[simp] theorem lsumOf_unique {ι : Type u} [Unique ι] (h : #ι < lam) (x : ι → X) :
    lsumOf (lam := lam) h x = x default := by
  show lsum (Function.extend (emb h.le) x 0) = x default
  have hproof : ∀ j : Idx lam, j ≠ emb h.le default → Function.extend (emb h.le) x 0 j = 0 := by
    intro j hj
    by_cases hjk : ∃ i, emb h.le i = j
    · obtain ⟨i, hi⟩ := hjk
      exact absurd (by rw [← hi, Unique.eq_default i]) hj
    · exact Function.extend_apply' _ _ _ hjk
  rw [lsum_single (emb h.le default) _ hproof, (emb h.le).injective.extend_apply]

@[simp] theorem lsumOf_isEmpty {ι : Type u} [IsEmpty ι] (h : #ι < lam) (x : ι → X) :
    lsumOf (lam := lam) h x = 0 := by
  show lsum (Function.extend (emb h.le) x 0) = 0
  obtain ⟨j₀⟩ := nonempty_Idx (aleph0_le (lam := lam) (X := X))
  have heq : Function.extend (emb h.le) x 0 = fun _ => (0 : X) := by
    funext k
    apply Function.extend_apply'
    rintro ⟨i, _⟩
    exact IsEmpty.false i
  rw [heq]
  exact lsum_single j₀ (fun _ => (0 : X)) (fun _ _ => rfl)

/-- General associativity for `lsumOf`; regularity of `λ` is what makes the total index
type small again. -/
theorem lsumOf_sigma {ι : Type u} {ρ : ι → Type u} (h : #ι < lam) (hρ : ∀ i, #(ρ i) < lam)
    (x : ∀ i, ρ i → X) (hσ : #(Σ i, ρ i) < lam) :
    lsumOf (lam := lam) h (fun i => lsumOf (lam := lam) (hρ i) (x i))
      = lsumOf (lam := lam) hσ (fun p : Σ i, ρ i => x p.1 p.2) := by
  have hlam0 := aleph0_le (lam := lam) (X := X)
  obtain ⟨j₀⟩ := nonempty_Idx hlam0
  set e : ι ↪ Idx lam := emb h.le with hedef
  set f : ∀ i, ρ i ↪ Idx lam := fun i => emb (hρ i).le with hfdef
  set π : Idx lam × Idx lam ≃ Idx lam := pairEquiv hlam0 with hπdef
  set E : (Σ i, ρ i) ↪ Idx lam := ⟨fun p => π (e p.1, f p.1 p.2), by
    rintro ⟨i1, r1⟩ ⟨i2, r2⟩ hEq
    have hpair : (e i1, f i1 r1) = (e i2, f i2 r2) := π.injective hEq
    have hi : i1 = i2 := e.injective (Prod.ext_iff.mp hpair).1
    subst hi
    have hr : r1 = r2 := (f i1).injective (Prod.ext_iff.mp hpair).2
    subst hr
    rfl⟩ with hEdef
  set W : ∀ i, Idx lam → X := fun i => Function.extend (f i) (x i) 0 with hWdef
  set G : Idx lam → (Idx lam → X) := Function.extend e W (fun _ => (0 : Idx lam → X)) with hGdef
  have hGrow : #{a : Idx lam | ∃ b, G a b ≠ 0} < lam := by
    have hsub : {a : Idx lam | ∃ b, G a b ≠ 0} ⊆ Set.range e := by
      rintro a ⟨b, hab⟩
      by_contra ha
      exact hab (by rw [hGdef, Function.extend_apply' _ _ _ ha]; rfl)
    calc #{a : Idx lam | ∃ b, G a b ≠ 0} ≤ #(Set.range e) := Cardinal.mk_le_mk_of_subset hsub
      _ = #ι := Cardinal.mk_range_eq e e.injective
      _ < lam := h
  have hGcol : #{b : Idx lam | ∃ a, G a b ≠ 0} < lam := by
    have hsub : {b : Idx lam | ∃ a, G a b ≠ 0} ⊆ ⋃ i : ι, Set.range (f i) := by
      rintro b ⟨a, hab⟩
      by_cases ha : ∃ i, e i = a
      · obtain ⟨i, hi⟩ := ha
        have hGa : G a = W i := by rw [← hi, hGdef, e.injective.extend_apply]
        by_contra hb
        apply hab
        rw [hGa, hWdef]
        apply Function.extend_apply'
        rintro ⟨r, hr⟩
        exact hb (Set.mem_iUnion.mpr ⟨i, ⟨r, hr⟩⟩)
      · exfalso
        apply hab
        rw [hGdef, Function.extend_apply' _ _ _ ha]
        rfl
    calc #{b : Idx lam | ∃ a, G a b ≠ 0} ≤ #(⋃ i : ι, Set.range (f i)) :=
          Cardinal.mk_le_mk_of_subset hsub
      _ < lam := by
          apply (Cardinal.card_iUnion_lt_iff_forall_of_isRegular
            (‹LMonoid lam X›.isRegular) h).mpr
          intro i
          rw [Cardinal.mk_range_eq (f i) (f i).injective]
          exact hρ i
  have hGa : ∀ a, lsum (G a) = Function.extend e (fun i => lsum (W i)) 0 a := by
    intro a
    by_cases ha : ∃ i, e i = a
    · obtain ⟨i, hi⟩ := ha
      have h1 : G a = W i := by rw [← hi, hGdef, e.injective.extend_apply]
      have h2 : Function.extend e (fun i => lsum (W i)) 0 a = lsum (W i) := by
        rw [← hi, e.injective.extend_apply]
      rw [h1, h2]
    · have h1 : G a = fun _ => (0 : X) := by
        rw [hGdef]
        exact Function.extend_apply' W (fun _ => (0 : Idx lam → X)) a ha
      have h2 : Function.extend e (fun i => lsum (W i)) 0 a = 0 :=
        Function.extend_apply' (fun i => lsum (W i)) (0 : Idx lam → X) a ha
      rw [h1, h2]
      exact lsum_single j₀ (fun _ => (0 : X)) (fun _ _ => rfl)
  have hGk : ∀ k, G (π.symm k).1 (π.symm k).2 = Function.extend E (fun p => x p.1 p.2) 0 k := by
    intro k
    by_cases ha : ∃ i, e i = (π.symm k).1
    · obtain ⟨i, hi⟩ := ha
      have hGaeq : G (π.symm k).1 = W i := by rw [← hi, hGdef, e.injective.extend_apply]
      rw [hGaeq]
      by_cases hb : ∃ r, f i r = (π.symm k).2
      · obtain ⟨r, hr⟩ := hb
        have hWeq : W i (π.symm k).2 = x i r := by
          rw [← hr]
          show Function.extend (f i) (x i) 0 (f i r) = x i r
          exact (f i).injective.extend_apply (x i) 0 r
        rw [hWeq]
        have hEk : E ⟨i, r⟩ = k := by
          show π (e i, f i r) = k
          rw [hi, hr]
          exact Equiv.apply_symm_apply π k
        rw [← hEk, E.injective.extend_apply]
      · have hWeq : W i (π.symm k).2 = 0 :=
          Function.extend_apply' (x i) (0 : Idx lam → X) (π.symm k).2 hb
        rw [hWeq]
        symm
        apply Function.extend_apply'
        rintro ⟨⟨i', r'⟩, hp⟩
        have heqp : (e i', f i' r') = π.symm k := by
          rw [← hp]; exact (Equiv.symm_apply_apply π (e i', f i' r')).symm
        have hi' : e i' = (π.symm k).1 := congrArg Prod.fst heqp
        have hii : i' = i := e.injective (hi'.trans hi.symm)
        subst hii
        exact hb ⟨r', congrArg Prod.snd heqp⟩
    · have hGaeq : G (π.symm k).1 = fun _ => (0 : X) := by
        rw [hGdef]
        exact Function.extend_apply' W (fun _ => (0 : Idx lam → X)) (π.symm k).1 ha
      rw [hGaeq]
      symm
      apply Function.extend_apply'
      rintro ⟨⟨i', r'⟩, hp⟩
      apply ha
      refine ⟨i', ?_⟩
      have heqp : (e i', f i' r') = π.symm k := by
        rw [← hp]; exact (Equiv.symm_apply_apply π (e i', f i' r')).symm
      exact congrArg Prod.fst heqp
  have step1 : lsumOf (lam := lam) h (fun i => lsumOf (lam := lam) (hρ i) (x i))
      = lsum (fun a => lsum (G a)) := by
    show lsum (Function.extend e (fun i => lsum (W i)) 0) = lsum (fun a => lsum (G a))
    congr 1
    funext a
    exact (hGa a).symm
  have step2 : lsum (fun a => lsum (G a))
      = lsum (fun k => G (π.symm k).1 (π.symm k).2) := lsum_sigma G π hGrow hGcol
  have step3 : lsum (fun k => G (π.symm k).1 (π.symm k).2)
      = lsum (Function.extend E (fun p => x p.1 p.2) 0) := by
    congr 1
    funext k
    exact hGk k
  have step4 : lsum (Function.extend E (fun p => x p.1 p.2) 0)
      = lsumOf (lam := lam) hσ (fun p : Σ i, ρ i => x p.1 p.2) :=
    (lsumOf_eq_extend hσ E (fun p => x p.1 p.2)).symm
  rw [step1, step2, step3, step4]

/-- A `lsumOf` indexed by (a universe-lifted) `Bool` recovers the binary operation `+`. -/
theorem lsumOf_two (a b : X) (hUB : #(ULift.{u} Bool) < lam) :
    lsumOf (lam := lam) hUB (fun p : ULift.{u} Bool => if p.down then a else b) = a + b := by
  have hlam0 := aleph0_le (lam := lam) (X := X)
  have hnt : Nontrivial (Idx lam) := by
    rw [← Cardinal.one_lt_iff_nontrivial, mk_Idx]
    exact lt_of_lt_of_le one_lt_aleph0 hlam0
  obtain ⟨i0, i1, hne⟩ := hnt.exists_pair_ne
  set e : ULift.{u} Bool ↪ Idx lam := ⟨fun p => if p.down then i0 else i1, by
    intro p q hpq
    match p, q with
    | ⟨true⟩, ⟨true⟩ => rfl
    | ⟨false⟩, ⟨false⟩ => rfl
    | ⟨true⟩, ⟨false⟩ => exact absurd hpq hne
    | ⟨false⟩, ⟨true⟩ => exact absurd hpq.symm hne⟩ with hedef
  rw [lsumOf_eq_extend hUB e (fun p : ULift.{u} Bool => if p.down then a else b)]
  have heq : Function.extend e (fun p : ULift.{u} Bool => if p.down then a else b) 0
      = fun j => if j = i0 then a else if j = i1 then b else 0 := by
    funext j
    by_cases hj : ∃ p, e p = j
    · obtain ⟨p, hp⟩ := hj
      match p with
      | ⟨true⟩ =>
        have hval : Function.extend e (fun p : ULift.{u} Bool => if p.down then a else b) 0 j
            = a := by
          rw [← hp]; exact e.injective.extend_apply _ _ _
        rw [hval]
        have hji0 : j = i0 := hp.symm
        rw [hji0]
        simp
      | ⟨false⟩ =>
        have hval : Function.extend e (fun p : ULift.{u} Bool => if p.down then a else b) 0 j
            = b := by
          rw [← hp]; exact e.injective.extend_apply _ _ _
        rw [hval]
        have hji1 : j = i1 := hp.symm
        rw [hji1]
        simp [hne.symm]
    · rw [Function.extend_apply' _ _ _ hj]
      have hj0 : j ≠ i0 := fun heq0 => hj ⟨⟨true⟩, heq0.symm⟩
      have hj1 : j ≠ i1 := fun heq1 => hj ⟨⟨false⟩, heq1.symm⟩
      simp [hj0, hj1]
  rw [heq]
  exact lsum_two a b i0 i1 hne

/-- `Option α` decomposed as a `Bool`-indexed disjoint union: `true` selects `α` itself,
`false` selects the single point `none`. -/
def optionSigmaEquiv (α : Type u) :
    Option α ≃ Σ p : ULift.{u} Bool, (if p.down then α else PUnit.{u + 1}) where
  toFun := fun o => match o with
    | some i => ⟨ULift.up true, i⟩
    | none => ⟨ULift.up false, PUnit.unit⟩
  invFun := fun s => match s with
    | ⟨⟨true⟩, y⟩ => some y
    | ⟨⟨false⟩, _⟩ => none
  left_inv := fun o => by cases o <;> rfl
  right_inv := fun s => by
    obtain ⟨p, y⟩ := s
    match p with
    | ⟨true⟩ => rfl
    | ⟨false⟩ => rfl

/-- For `λ = ℵ₀` a `λ⁻`-monoid is nothing but a commutative monoid, and `lsumOf` is the
ordinary finite sum. -/
theorem lsumOf_aleph0_eq_finsum {ι : Type u} [Fintype ι] (h : #ι < ℵ₀)
    {X : Type v} [LMonoid ℵ₀ X] (x : ι → X) :
    lsumOf (lam := ℵ₀) h x = ∑ i, x i := by
  revert h x
  refine Fintype.induction_empty_option
    (P := fun (ι : Type u) [Fintype ι] =>
      ∀ (h : #ι < ℵ₀) (x : ι → X), lsumOf (lam := ℵ₀) h x = ∑ i, x i)
    ?_ ?_ ?_ ι
  · intro α β _ e ih h x
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have hα : #α < ℵ₀ := by rw [Cardinal.mk_congr e]; exact h
    rw [lsumOf_equiv h hα e x, ih hα (x ∘ e)]
    exact Equiv.sum_comp e x
  · intro h x
    simp [lsumOf_isEmpty]
  · intro α _ ih h x
    have hα : #α < ℵ₀ := lt_of_le_of_lt (Cardinal.mk_le_of_injective (Option.some_injective α)) h
    set e : Option α ≃ Σ p : ULift.{u} Bool, (if p.down then α else PUnit.{u + 1}) :=
      optionSigmaEquiv α with hedef
    have hUB : #(ULift.{u} Bool) < ℵ₀ := Cardinal.lt_aleph0_iff_finite.mpr inferInstance
    have hρ : ∀ p : ULift.{u} Bool, #(if p.down then α else PUnit.{u + 1}) < ℵ₀ := by
      intro p
      match p with
      | ⟨true⟩ => exact hα
      | ⟨false⟩ =>
        show #(PUnit.{u + 1}) < ℵ₀
        exact Cardinal.lt_aleph0_iff_finite.mpr inferInstance
    have hσ : #(Σ p : ULift.{u} Bool, if p.down then α else PUnit.{u + 1}) < ℵ₀ := by
      rw [Cardinal.mk_congr e.symm]; exact h
    have hmain := lsumOf_sigma (X := X) hUB hρ
      (fun p (y : if p.down then α else PUnit.{u + 1}) => x (e.symm ⟨p, y⟩)) hσ
    have hcomp : (x ∘ (⇑e.symm)) = fun p => x (e.symm ⟨p.fst, p.snd⟩) := rfl
    rw [lsumOf_equiv h hσ e.symm x, hcomp, ← hmain]
    have hinner_true : lsumOf (hρ (ULift.up true))
        (fun y => x (e.symm (⟨ULift.up true, y⟩ :
          Σ p : ULift.{u} Bool, if p.down then α else PUnit.{u + 1}))) = ∑ i, x (some i) :=
      ih hα (x ∘ some)
    have hinner_false : lsumOf (hρ (ULift.up false))
        (fun y => x (e.symm (⟨ULift.up false, y⟩ :
          Σ p : ULift.{u} Bool, if p.down then α else PUnit.{u + 1}))) = x none := by
      haveI : Unique (if ({down := false} : ULift.{u} Bool).down = true then α
          else PUnit.{u + 1}) := by
        show Unique PUnit.{u + 1}
        infer_instance
      exact lsumOf_unique (hρ (ULift.up false)) (fun _ => x none)
    have heq : (fun p : ULift.{u} Bool =>
        lsumOf (hρ p) (fun y => x (e.symm ⟨p, y⟩)))
        = fun p => if p.down then ∑ i, x (some i) else x none := by
      funext p
      match p with
      | ⟨true⟩ => exact hinner_true
      | ⟨false⟩ => exact hinner_false
    rw [heq, lsumOf_two (∑ i, x (some i)) (x none) hUB, Fintype.sum_option x, add_comm]

/-- Every `κ`-monoid is a `λ⁻`-monoid for every regular `λ ≤ κ` (Remark 2.19). -/
@[instance_reducible]
noncomputable def _root_.NS.KMonoid.toLMonoid {κ : Cardinal.{u}} (H : Type v) [KMonoid κ H]
    {lam : Cardinal.{u}} (hlam : lam.IsRegular) (hlk : lam ≤ κ) : LMonoid lam H where
  isRegular := hlam
  lsum x := if h : #(Function.support x) < lam then
      sumOf (κ := κ) (le_of_eq_of_le (mk_Idx lam) hlk) x else 0
  lsum_of_large := by intro x hx; simp [hx]
  lsum_single := by
    intro i₀ x hx
    have hsupp : #(Function.support x) < lam := by
      have hsub : Function.support x ⊆ {i₀} := by
        intro i hi
        by_contra hne
        exact hi (hx i (fun h => hne (Set.mem_singleton_iff.mpr h)))
      calc #(Function.support x) ≤ #({i₀} : Set (Idx lam)) := Cardinal.mk_le_mk_of_subset hsub
        _ = 1 := mk_singleton i₀
        _ < lam := lt_of_lt_of_le one_lt_aleph0 hlam.aleph0_le
    show (if h : #(Function.support x) < lam then
        sumOf (κ := κ) (le_of_eq_of_le (mk_Idx lam) hlk) x else 0) = x i₀
    rw [dif_pos hsupp]
    show ksum (κ := κ) (Function.extend (emb (le_of_eq_of_le (mk_Idx lam) hlk)) x 0) = x i₀
    set e := emb (le_of_eq_of_le (mk_Idx lam) hlk) with hedef
    rw [ksum_single (e i₀) _ ?_, e.injective.extend_apply]
    intro j hj
    by_cases hjk : ∃ i, e i = j
    · obtain ⟨i, hi⟩ := hjk
      rw [← hi, e.injective.extend_apply]
      apply hx i
      intro hii0
      apply hj
      rw [← hi, hii0]
    · exact Function.extend_apply' _ _ _ hjk
  lsum_sigma := by
    intro x π hrow hcol
    have hκ := KMonoid.aleph0_le (κ := κ) (H := H)
    have hidx : #(Idx lam) ≤ κ := le_of_eq_of_le (mk_Idx lam) hlk
    set L : (Idx lam → H) → H := fun z =>
      if h : #(Function.support z) < lam then sumOf (κ := κ) hidx z else 0 with hLdef
    show L (fun i => L (x i)) = L (fun k => x (π.symm k).1 (π.symm k).2)
    -- Every row has small support (it is contained in the column-marginal).
    have hsupp_row : ∀ i, #(Function.support (x i)) < lam := by
      intro i
      refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset ?_) hcol
      intro j hj
      exact ⟨i, hj⟩
    have hlsum_row : ∀ i, L (x i) = sumOf (κ := κ) hidx (x i) := by
      intro i
      rw [hLdef]
      exact dif_pos (hsupp_row i)
    -- Hence the outer family `fun i => L (x i)` has support inside the row-marginal.
    have hsupp_outer : #(Function.support (fun i => L (x i))) < lam := by
      refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset ?_) hrow
      intro i hi
      by_contra hcontra
      apply hi
      show L (x i) = 0
      rw [hlsum_row i]
      have hz : x i = fun _ => (0 : H) := by
        funext j
        by_contra hxij
        exact hcontra ⟨j, hxij⟩
      rw [hz]
      exact sumOf_zero hidx
    have hstep1 : L (fun i => L (x i))
        = sumOf (κ := κ) hidx (fun i => sumOf (κ := κ) hidx (x i)) := by
      show (if _ : #(Function.support (fun i => L (x i))) < lam then
          sumOf (κ := κ) hidx (fun i => L (x i)) else 0) = _
      rw [dif_pos hsupp_outer]
      congr 1
      funext i
      exact hlsum_row i
    have hσ' : #(Σ _ : Idx lam, Idx lam) ≤ κ := by
      have heq1 : #(Σ _ : Idx lam, Idx lam) = #(Idx lam) * #(Idx lam) := by
        rw [Cardinal.mk_congr (Equiv.sigmaEquivProd (Idx lam) (Idx lam))]
        simp [Cardinal.mk_prod]
      rw [heq1]
      calc #(Idx lam) * #(Idx lam) ≤ κ * κ := mul_le_mul' hidx hidx
        _ = κ := Cardinal.mul_eq_self hκ
    have hstep2 : sumOf (κ := κ) hidx (fun i => sumOf (κ := κ) hidx (x i))
        = sumOf (κ := κ) hσ' (fun p : Σ _ : Idx lam, Idx lam => x p.1 p.2) :=
      sumOf_sigma hidx (fun _ => hidx) hσ' (fun (i j : Idx lam) => x i j)
    have hprod : #(Idx lam × Idx lam) ≤ κ := by
      have hmp : #(Idx lam × Idx lam) = #(Idx lam) * #(Idx lam) := by simp [Cardinal.mk_prod]
      rw [hmp]
      calc #(Idx lam) * #(Idx lam) ≤ κ * κ := mul_le_mul' hidx hidx
        _ = κ := Cardinal.mul_eq_self hκ
    have hstep3 : sumOf (κ := κ) hσ' (fun p : Σ _ : Idx lam, Idx lam => x p.1 p.2)
        = sumOf (κ := κ) hprod (fun q : Idx lam × Idx lam => x q.1 q.2) :=
      (sumOf_equiv hprod hσ' (Equiv.sigmaEquivProd (Idx lam) (Idx lam)) (fun q => x q.1 q.2)).symm
    -- The 2-dimensional support of `x` is small: it embeds into the product of the marginals.
    have hqsubset : {q : Idx lam × Idx lam | x q.1 q.2 ≠ 0} ⊆
        {i : Idx lam | ∃ j, x i j ≠ 0} ×ˢ {j : Idx lam | ∃ i, x i j ≠ 0} := by
      rintro ⟨a, b⟩ hab
      exact ⟨⟨b, hab⟩, ⟨a, hab⟩⟩
    have hSTequiv :
        ↥({i : Idx lam | ∃ j, x i j ≠ 0} ×ˢ {j : Idx lam | ∃ i, x i j ≠ 0}) ≃
          ↥{i : Idx lam | ∃ j, x i j ≠ 0} × ↥{j : Idx lam | ∃ i, x i j ≠ 0} :=
      { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
        invFun := fun q => ⟨(q.1.1, q.2.1), q.1.2, q.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hqcard : #{q : Idx lam × Idx lam | x q.1 q.2 ≠ 0} < lam := by
      calc #{q : Idx lam × Idx lam | x q.1 q.2 ≠ 0}
          ≤ #(↥({i : Idx lam | ∃ j, x i j ≠ 0} ×ˢ {j : Idx lam | ∃ i, x i j ≠ 0})) :=
            Cardinal.mk_le_mk_of_subset hqsubset
        _ = #(↥{i : Idx lam | ∃ j, x i j ≠ 0}) * #(↥{j : Idx lam | ∃ i, x i j ≠ 0}) :=
            Cardinal.mk_congr hSTequiv
        _ < lam := Cardinal.mul_lt_of_lt hlam.aleph0_le hrow hcol
    have hkey : #{k : Idx lam | x (π.symm k).1 (π.symm k).2 ≠ 0} < lam := by
      have heqset : {k : Idx lam | x (π.symm k).1 (π.symm k).2 ≠ 0}
          = π.symm ⁻¹' {q : Idx lam × Idx lam | x q.1 q.2 ≠ 0} := rfl
      rw [heqset, Cardinal.mk_preimage_equiv]
      exact hqcard
    have hstep4 : sumOf (κ := κ) hprod (fun q : Idx lam × Idx lam => x q.1 q.2)
        = sumOf (κ := κ) hidx (fun k => x (π.symm k).1 (π.symm k).2) :=
      sumOf_equiv hprod hidx π.symm (fun q => x q.1 q.2)
    have hsupp_k : #(Function.support (fun k => x (π.symm k).1 (π.symm k).2)) < lam :=
      lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset (fun k hk => hk)) hkey
    have hstep5 : L (fun k => x (π.symm k).1 (π.symm k).2)
        = sumOf (κ := κ) hidx (fun k => x (π.symm k).1 (π.symm k).2) := by
      rw [hLdef]
      exact dif_pos hsupp_k
    rw [hstep1, hstep2, hstep3, hstep4, ← hstep5]
  lsum_two := by
    intro a b i0 i1 hne
    set y : Idx lam → H := fun i => if i = i0 then a else if i = i1 then b else 0 with hydef
    have hsub : Function.support y ⊆ {i0, i1} := by
      intro i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hcontra
      push Not at hcontra
      apply hi
      simp [hydef, hcontra.1, hcontra.2]
    have hsupp : #(Function.support y) < lam :=
      (((Set.finite_singleton i1).insert i0).subset hsub).lt_aleph0.trans_le
        hlam.aleph0_le
    show (if h : #(Function.support y) < lam then
        sumOf (κ := κ) (le_of_eq_of_le (mk_Idx lam) hlk) y else 0) = a + b
    rw [dif_pos hsupp]
    show ksum (κ := κ) (Function.extend (emb (le_of_eq_of_le (mk_Idx lam) hlk)) y 0) = a + b
    set e := emb (le_of_eq_of_le (mk_Idx lam) hlk) with hedef
    have heq : Function.extend e y 0
        = fun k => if k = e i0 then a else if k = e i1 then b else 0 := by
      funext k
      by_cases hk : ∃ i, e i = k
      · obtain ⟨i, hi⟩ := hk
        rw [← hi, e.injective.extend_apply, hydef]
        by_cases hi0 : i = i0
        · simp [hi0]
        · have hei0 : e i ≠ e i0 := fun h => hi0 (e.injective h)
          by_cases hi1 : i = i1
          · simp [hi1]
          · have hei1 : e i ≠ e i1 := fun h => hi1 (e.injective h)
            simp [hi0, hi1, hei0, hei1]
      · rw [Function.extend_apply' _ _ _ hk]
        have hne0 : k ≠ e i0 := fun h => hk ⟨i0, h.symm⟩
        have hne1 : k ≠ e i1 := fun h => hk ⟨i1, h.symm⟩
        simp [hne0, hne1]
    rw [heq]
    exact ksum_two a b (e i0) (e i1) (fun h => hne (e.injective h))

/-- A `λ⁻`-homomorphism from a `λ⁻`-monoid into (the underlying `λ⁻`-monoid of) a
`κ`-monoid. -/
def IsLHom {lam κ : Cardinal.{u}} {X : Type v} {H : Type w}
    [LMonoid lam X] [KMonoid κ H] (hκ : lam ≤ κ) (f : X → H) : Prop :=
  f 0 = 0 ∧ ∀ {ι : Type u} (h : #ι < lam) (x : ι → X),
    f (lsumOf (lam := lam) h x) = sumOf (κ := κ) (h.le.trans hκ) (f ∘ x)

end LMonoid

/-! ## Induced structures on sub-objects -/

/-- A subset of a `κ`-monoid closed under `λ⁻`-sums. -/
structure IsLSubset (lam : Cardinal.{u}) {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]
    (hlk : lam ≤ κ) (S : Set H) : Prop where
  zero_mem : (0 : H) ∈ S
  sumOf_mem : ∀ {ι : Type u} (h : #ι < lam) (x : ι → H), (∀ i, x i ∈ S) →
    sumOf (κ := κ) (h.le.trans hlk) x ∈ S

/-- A `κ`-submonoid of a `κ`-monoid is itself a `κ`-monoid. -/
@[instance_reducible]
noncomputable def KMonoid.IsKSubmonoid.kmonoid {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]
    {S : Set H} (hS : IsKSubmonoid κ S) : KMonoid κ S := by
  have hnt : Nontrivial (Idx κ) := by
    rw [← Cardinal.one_lt_iff_nontrivial, mk_Idx]
    exact lt_of_lt_of_le one_lt_aleph0 (KMonoid.aleph0_le (κ := κ) (H := H))
  set i0 := hnt.exists_pair_ne.choose with hi0def
  set i1 := hnt.exists_pair_ne.choose_spec.choose with hi1def
  have hne : i0 ≠ i1 := hnt.exists_pair_ne.choose_spec.choose_spec
  have hadd : ∀ a b : H, a ∈ S → b ∈ S → a + b ∈ S := by
    intro a b ha hb
    have hmem := hS.ksum_mem (fun i => if i = i0 then a else if i = i1 then b else 0) (by
      intro i
      by_cases hi0 : i = i0
      · simpa [hi0] using ha
      · by_cases hi1 : i = i1
        · rw [if_neg hi0, if_pos hi1]; exact hb
        · rw [if_neg hi0, if_neg hi1]; exact hS.zero_mem)
    rwa [ksum_two a b i0 i1 hne] at hmem
  letI zeroS : Zero (↥S) := ⟨⟨0, hS.zero_mem⟩⟩
  letI addS : Add (↥S) := ⟨fun a b => ⟨a.1 + b.1, hadd a.1 b.1 a.2 b.2⟩⟩
  have hzero : (0 : ↥S).1 = (0 : H) := rfl
  have haddv : ∀ a b : ↥S, (a + b).1 = a.1 + b.1 := fun _ _ => rfl
  letI addCommMonoidS : AddCommMonoid (↥S) :=
    { add_assoc := fun a b c => Subtype.ext (by simp only [haddv, add_assoc])
      zero_add := fun a => Subtype.ext (by simp only [haddv, hzero, zero_add])
      add_zero := fun a => Subtype.ext (by simp only [haddv, hzero, add_zero])
      add_comm := fun a b => Subtype.ext (by simp only [haddv, add_comm])
      nsmul := fun n a => ⟨n • a.1, by
        induction n with
        | zero => rw [zero_nsmul]; exact hS.zero_mem
        | succ n ih => rw [succ_nsmul]; exact hadd _ _ ih a.2⟩
      nsmul_zero := fun a => Subtype.ext (by show (0 : ℕ) • a.1 = (0 : H); simp)
      nsmul_succ := fun n a => Subtype.ext (by
        show (n + 1 : ℕ) • a.1 = n • a.1 + a.1
        simp [succ_nsmul]) }
  refine
  { toAddCommMonoid := addCommMonoidS
    aleph0_le := KMonoid.aleph0_le (κ := κ) (H := H)
    ksum := fun x => ⟨ksum (κ := κ) (fun i => (x i).1), hS.ksum_mem _ (fun i => (x i).2)⟩
    ksum_single := ?_
    ksum_sigma := ?_
    ksum_two := ?_ }
  · intro i₀ x hx
    apply Subtype.ext
    show ksum (κ := κ) (fun i => (x i).1) = (x i₀).1
    apply ksum_single i₀
    intro i hi
    exact congrArg Subtype.val (hx i hi)
  · intro x π
    apply Subtype.ext
    show ksum (κ := κ) (fun i => ksum (κ := κ) (fun j => (x i j).1))
      = ksum (κ := κ) (fun k => (x (π.symm k).1 (π.symm k).2).1)
    exact ksum_sigma (fun i j => (x i j).1) π
  · intro a b i₀ i₁ hne'
    apply Subtype.ext
    have key : ∀ i : Idx κ,
        ((if i = i₀ then a else if i = i₁ then b else 0 : ↥S) : H)
          = if i = i₀ then a.1 else if i = i₁ then b.1 else 0 := by
      intro i
      by_cases hi0 : i = i₀
      · rw [if_pos hi0, if_pos hi0]
      · rw [if_neg hi0, if_neg hi0]
        by_cases hi1 : i = i₁
        · rw [if_pos hi1, if_pos hi1]
        · rw [if_neg hi1, if_neg hi1]
          exact hzero
    show ksum (κ := κ) (fun i =>
        ((if i = i₀ then a else if i = i₁ then b else 0 : ↥S) : H)) = a.1 + b.1
    simp_rw [key]
    exact ksum_two a.1 b.1 i₀ i₁ hne'

/-- A `λ⁻`-closed subset of a `κ`-monoid is a `λ⁻`-monoid. -/
@[instance_reducible]
noncomputable def IsLSubset.lmonoid {lam κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]
    {hlk : lam ≤ κ} {S : Set H} (hlam : lam.IsRegular) (hS : IsLSubset lam hlk S) :
    LMonoid lam S := by
  have hκ := KMonoid.aleph0_le (κ := κ) (H := H)
  have hidx : #(Idx lam) ≤ κ := le_of_eq_of_le (mk_Idx lam) hlk
  letI LH : LMonoid lam H := KMonoid.toLMonoid H hlam hlk
  have hUBlt : #(ULift.{u} Bool) < lam :=
    lt_of_lt_of_le (Cardinal.lt_aleph0_iff_finite.mpr inferInstance) hlam.aleph0_le
  have hadd : ∀ a b : H, a ∈ S → b ∈ S → a + b ∈ S := by
    intro a b ha hb
    have hmem := hS.sumOf_mem hUBlt (fun p : ULift.{u} Bool => if p.down then a else b) (by
      intro p
      by_cases hp : p.down
      · simpa [hp] using ha
      · simpa [hp] using hb)
    rwa [sumOf_two a b (hUBlt.le.trans hlk)] at hmem
  letI zeroS : Zero (↥S) := ⟨⟨0, hS.zero_mem⟩⟩
  letI addS : Add (↥S) := ⟨fun a b => ⟨a.1 + b.1, hadd a.1 b.1 a.2 b.2⟩⟩
  have hzero : (0 : ↥S).1 = (0 : H) := rfl
  have haddv : ∀ a b : ↥S, (a + b).1 = a.1 + b.1 := fun _ _ => rfl
  letI addCommMonoidS : AddCommMonoid (↥S) :=
    { add_assoc := fun a b c => Subtype.ext (by simp only [haddv, add_assoc])
      zero_add := fun a => Subtype.ext (by simp only [haddv, hzero, zero_add])
      add_zero := fun a => Subtype.ext (by simp only [haddv, hzero, add_zero])
      add_comm := fun a b => Subtype.ext (by simp only [haddv, add_comm])
      nsmul := fun n a => ⟨n • a.1, by
        induction n with
        | zero => rw [zero_nsmul]; exact hS.zero_mem
        | succ n ih => rw [succ_nsmul]; exact hadd _ _ ih a.2⟩
      nsmul_zero := fun a => Subtype.ext (by show (0 : ℕ) • a.1 = (0 : H); simp)
      nsmul_succ := fun n a => Subtype.ext (by
        show (n + 1 : ℕ) • a.1 = n • a.1 + a.1
        simp [succ_nsmul]) }
  have hsupp_eq : ∀ x : Idx lam → ↥S,
      Function.support (fun i => (x i).1) = Function.support x := by
    intro x
    ext i
    simp only [Function.mem_support, ne_eq, Subtype.ext_iff, hzero]
  have hmem_of_small : ∀ (y : Idx lam → H), #(Function.support y) < lam →
      (∀ i, y i ∈ S) → sumOf (κ := κ) hidx y ∈ S := by
    intro y hy hyS
    rw [sumOf_subtype_support hidx y (hy.le.trans hlk)]
    exact hS.sumOf_mem hy (fun i : Function.support y => y i) (fun i => hyS i)
  have hLHmem : ∀ x : Idx lam → ↥S, LH.lsum (fun i => (x i).1) ∈ S := by
    intro x
    show (if h : #(Function.support (fun i => (x i).1)) < lam then
        sumOf (κ := κ) hidx (fun i => (x i).1) else 0) ∈ S
    by_cases h : #(Function.support (fun i => (x i).1)) < lam
    · rw [dif_pos h]
      exact hmem_of_small _ h (fun i => (x i).2)
    · rw [dif_neg h]
      exact hS.zero_mem
  refine
  { toAddCommMonoid := addCommMonoidS
    isRegular := hlam
    lsum := fun x => ⟨LH.lsum (fun i => (x i).1), hLHmem x⟩
    lsum_of_large := ?_
    lsum_single := ?_
    lsum_sigma := ?_
    lsum_two := ?_ }
  · intro x hx
    apply Subtype.ext
    show LH.lsum (fun i => (x i).1) = (0 : H)
    apply LH.lsum_of_large
    rwa [hsupp_eq]
  · intro i₀ x hx
    apply Subtype.ext
    show LH.lsum (fun i => (x i).1) = (x i₀).1
    apply LH.lsum_single
    intro i hi
    exact congrArg Subtype.val (hx i hi)
  · intro x π hrow hcol
    apply Subtype.ext
    show LH.lsum (fun i => LH.lsum (fun j => (x i j).1))
      = LH.lsum (fun k => (x (π.symm k).1 (π.symm k).2).1)
    have hSeteq_row : {i : Idx lam | ∃ j, x i j ≠ 0} = {i : Idx lam | ∃ j, (x i j).1 ≠ 0} := by
      ext i; simp only [Set.mem_ofPred_eq, ne_eq, Subtype.ext_iff, hzero]
    have hSeteq_col : {j : Idx lam | ∃ i, x i j ≠ 0} = {j : Idx lam | ∃ i, (x i j).1 ≠ 0} := by
      ext j; simp only [Set.mem_ofPred_eq, ne_eq, Subtype.ext_iff, hzero]
    exact LH.lsum_sigma (fun i j => (x i j).1) π (hSeteq_row ▸ hrow) (hSeteq_col ▸ hcol)
  · intro a b i₀ i₁ hne'
    apply Subtype.ext
    have key : ∀ i : Idx lam,
        ((if i = i₀ then a else if i = i₁ then b else 0 : ↥S) : H)
          = if i = i₀ then a.1 else if i = i₁ then b.1 else 0 := by
      intro i
      by_cases hi0 : i = i₀
      · rw [if_pos hi0, if_pos hi0]
      · rw [if_neg hi0, if_neg hi0]
        by_cases hi1 : i = i₁
        · rw [if_pos hi1, if_pos hi1]
        · rw [if_neg hi1, if_neg hi1]
          exact hzero
    show LH.lsum (fun i =>
        ((if i = i₀ then a else if i = i₁ then b else 0 : ↥S) : H)) = a.1 + b.1
    simp_rw [key]
    exact LH.lsum_two a.1 b.1 i₀ i₁ hne'

/-! ## The reducedness of `λ⁻`-monoids that embed into `κ`-monoids

This is the observation behind the hypothesis that has to be added to Theorem 3.11. -/

namespace LMonoid

variable {lam κ : Cardinal.{u}} {X : Type v} {H : Type w} [LMonoid lam X] [KMonoid κ H]

/-- If a `λ⁻`-monoid `X` admits an injective additive map into a `κ`-monoid, then `X` is
reduced.  Since `Theorem 3.11` asserts the existence of a `κ`-monoid `Ĥ ⊇ H`, this shows
that reducedness of `H` is a *necessary* hypothesis there. -/
theorem isConical_of_injective (f : X → H) (hf : Function.Injective f) (h0 : f 0 = 0)
    (hadd : ∀ a b, f (a + b) = f a + f b) : IsConical X := by
  intro a b hab
  have h : f a + f b = 0 := by rw [← hadd, hab, h0]
  obtain ⟨ha, hb⟩ := KMonoid.isConical κ H (f a) (f b) h
  exact ⟨hf (by rw [ha, h0]), hf (by rw [hb, h0])⟩

end LMonoid

end NS
