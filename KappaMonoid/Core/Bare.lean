/-
Reconstructing a `κ`-monoid from `κ`-indexed data (**Lemma 2.5** at the `κ`-level):
`BareKMonoid` and `KMonoid.ofBare`, which is what §§3-4 supply.
-/
import KappaMonoid.Core.Subobject
import KappaMonoid.Core.IdxSum

universe u v w

open Cardinal Function Set

namespace KappaMonoid

/-! ## Reconstructing a `κ`-monoid from `κ`-indexed data (Lemma 2.5)

The constructions of Sections 3 and 4 produce a summation operation for `Idx κ`-indexed
families only.  This section turns such data into a `κ`-monoid: an arbitrary family of size
`≤ κ` is summed by padding it with zeros along an embedding into `Idx κ`, the point being
that the result does not depend on the embedding chosen.  The padding is `IdxSumData`
(`Core/IdxSum.lean`) at `μ = κ`, `λ = κ⁺`, where every family is summed. -/

/-- **Definition 2.1**, verbatim: a set `H` with an element `0` and a map `Σ : H^κ → H` such that

* (A1) if `x ∈ H^κ` has `x i = 0` for all `i ≠ 0`, then `Σ x = x 0`;
* (A2) if `x ∈ H^{κ×κ}` and `π : κ × κ → κ` is a bijection, then `Σᵢ Σⱼ x i j = Σₖ x (π⁻¹ k)`.

The distinguished element `0 ∈ κ` of the paper is an arbitrary index `i₀ : Idx κ`, and (A1) is
assumed at `i₀` only, exactly as in the paper; at every other index it follows
(`ksum_single_at`).  By Lemma 2.5 the additive structure and the sums over arbitrary index types
of size `≤ κ` are determined by this data; `KMonoid.ofBare` reconstructs them, and
`Paper/Definition21.lean` shows that nothing is lost or added. -/
structure BareKMonoid (κ : Cardinal.{u}) (H : Type v) [Zero H] where
  /-- `κ` is an infinite cardinal. -/
  aleph0_le : ℵ₀ ≤ κ
  /-- The distinguished index, playing the role of `0 ∈ κ`. -/
  i₀ : Idx κ
  /-- The `κ`-indexed summation `Σ : H^κ → H`. -/
  ksum : (Idx κ → H) → H
  /-- (A1), at the distinguished index. -/
  ksum_single : ∀ x : Idx κ → H, (∀ i, i ≠ i₀ → x i = 0) → ksum x = x i₀
  /-- (A2). -/
  ksum_sigma : ∀ (x : Idx κ → Idx κ → H) (π : Idx κ × Idx κ ≃ Idx κ),
      ksum (fun i => ksum (x i)) = ksum fun k => x (π.symm k).1 (π.symm k).2


namespace BareKMonoid

variable {κ : Cardinal.{u}} {H : Type v} [Zero H] (B : BareKMonoid κ H)

/-- The data as a summation of `Idx κ`-indexed families for `λ = κ⁺`: every family has fewer than
`κ⁺` nonzero rows and columns, so (A2) holds without restriction. -/
def toIdxSumData : IdxSumData (Order.succ κ) κ H where
  isRegular := Cardinal.isRegular_succ B.aleph0_le
  aleph0_le := B.aleph0_le
  le_succ := le_rfl
  i₀ := B.i₀
  tot := B.ksum
  tot_single := B.ksum_single
  tot_sigma := fun x _ _ π => B.ksum_sigma x π

theorem ksum_zero : B.ksum (fun _ => 0) = 0 := B.toIdxSumData.tot_zero

/-- (A3), the first half of Lemma 2.5: `Σ` is invariant under permutations of `κ`
(`IdxSumData.tot_perm`). -/
theorem ksum_perm (x : Idx κ → H) (π : Idx κ ≃ Idx κ) : B.ksum x = B.ksum (x ∘ π) :=
  B.toIdxSumData.tot_perm (Order.lt_succ_iff.mpr ((Cardinal.mk_set_le _).trans_eq (mk_Idx κ))) π

/-- (A1) at an *arbitrary* index (`IdxSumData.tot_single_at`). -/
theorem ksum_single_at (a : Idx κ) (x : Idx κ → H) (hx : ∀ i, i ≠ a → x i = 0) :
    B.ksum x = x a :=
  B.toIdxSumData.tot_single_at a x hx

end BareKMonoid

/-- A `κ`-monoid is determined by its `κ`-indexed summation: the bullets after **Lemma 2.5**,
whose (A3) is `BareKMonoid.ksum_perm`. -/
@[instance_reducible]
noncomputable def KMonoid.ofBare {κ : Cardinal.{u}} {H : Type v} [Zero H]
    (B : BareKMonoid κ H) : KMonoid κ H :=
  { toLMonoid := LMonoid.ofIdxSumData B.toIdxSumData
    aleph0_le := B.aleph0_le }

@[simp] theorem KMonoid.ofBare_ksum {κ : Cardinal.{u}} {H : Type v} [Zero H]
    (B : BareKMonoid κ H) (x : Idx κ → H) :
    letI := KMonoid.ofBare B
    ksum (κ := κ) x = B.ksum x := by
  show B.toIdxSumData.lsum (KMonoid.lt_succ (le_of_eq (mk_Idx κ))) x = B.ksum x
  rw [← B.toIdxSumData.tot_extend_eq (KMonoid.lt_succ (le_of_eq (mk_Idx κ)))
    (Function.Embedding.refl (Idx κ)) x]
  exact congrArg B.ksum
    (funext fun k => (Function.Embedding.refl (Idx κ)).injective.extend_apply x 0 k)

/-- Nothing is added by the reconstruction: sums over an arbitrary index type are zero-padded
`Σ`'s. -/
theorem KMonoid.ofBare_sumOf {κ : Cardinal.{u}} {H : Type v} [Zero H] (B : BareKMonoid κ H)
    {ι : Type u} (h : #ι ≤ κ) (x : ι → H) :
    letI := KMonoid.ofBare B
    ∑[≤ κ] i, x i = B.ksum (Function.extend (emb h) x 0) := by
  let := KMonoid.ofBare B
  exact (KMonoid.sumOf_eq_extend (h := CardLE.mk' h) (emb h) x).trans (KMonoid.ofBare_ksum B _)

/-- Nor by the addition: it is a two-term `Σ`. -/
theorem KMonoid.ofBare_add {κ : Cardinal.{u}} {H : Type v} [Zero H] (B : BareKMonoid κ H)
    (a b : H) {i₀ i₁ : Idx κ} (hne : i₀ ≠ i₁) :
    letI := KMonoid.ofBare B
    a + b = B.ksum (fun i => if i = i₀ then a else if i = i₁ then b else 0) := by
  let := KMonoid.ofBare B
  rw [← KMonoid.ofBare_ksum B, KMonoid.ksum_two a b i₀ i₁ hne]

/-- The `κ`-indexed summation of a `κ`-monoid, as the data of Definition 2.1.  Any index may be
taken as the distinguished one, since a `κ`-monoid satisfies (A1) at every index. -/
noncomputable def KMonoid.toBare (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] :
    BareKMonoid κ H where
  aleph0_le := KMonoid.aleph0_le (κ := κ) (H := H)
  i₀ := (nonempty_Idx (KMonoid.aleph0_le (κ := κ) (H := H))).some
  ksum := KMonoid.ksum (κ := κ)
  ksum_single := fun x hx => KMonoid.ksum_single _ x hx
  ksum_sigma := fun x π => KMonoid.ksum_sigma x π

@[simp] theorem KMonoid.toBare_ksum (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H]
    (x : Idx κ → H) : (KMonoid.toBare κ H).ksum x = KMonoid.ksum (κ := κ) x := rfl

/-- A `κ`-monoid structure from `κ`-indexed data on a type that already carries a compatible
commutative monoid structure. -/
@[instance_reducible]
noncomputable def KMonoid.ofBare' {κ : Cardinal.{u}} {H : Type v} [AddCommMonoid H]
    (B : BareKMonoid κ H)
    (two : ∀ (a b : H) (i₀ i₁ : Idx κ), i₀ ≠ i₁ →
      B.ksum (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b) :
    KMonoid κ H := by
  classical
  refine { toLMonoid := LMonoid.ofSumData' B.toIdxSumData.sumData ?_, aleph0_le := B.aleph0_le }
  intro h a b
  set E : (PUnit.{u + 1} ⊕ PUnit.{u + 1}) ↪ Idx κ := emb (KMonoid.le_of_lt_succ h) with hEdef
  have hne : E (Sum.inl PUnit.unit) ≠ E (Sum.inr PUnit.unit) := by
    intro hh
    exact Sum.inl_ne_inr (E.injective hh)
  have hfun : Function.extend ⇑E (Sum.elim (fun _ => a) (fun _ => b)) 0
      = fun i => if i = E (Sum.inl PUnit.unit) then a
        else if i = E (Sum.inr PUnit.unit) then b else 0 := by
    funext k
    by_cases hk : ∃ p, E p = k
    · obtain ⟨p, rfl⟩ := hk
      rcases p with ⟨⟩ | ⟨⟩
      · rw [E.injective.extend_apply, if_pos rfl]
        rfl
      · rw [E.injective.extend_apply, if_neg (fun hh => hne hh.symm), if_pos rfl]
        rfl
    · rw [Function.extend_apply' _ _ _ hk,
        if_neg (fun hh => hk ⟨Sum.inl PUnit.unit, hh.symm⟩),
        if_neg (fun hh => hk ⟨Sum.inr PUnit.unit, hh.symm⟩)]
      rfl
  show a + b = B.toIdxSumData.lsum h _
  rw [← B.toIdxSumData.tot_extend_eq h E, hfun]
  exact (two a b _ _ hne).symm

@[simp] theorem KMonoid.ofBare'_ksum {κ : Cardinal.{u}} {H : Type v} [AddCommMonoid H]
    (B : BareKMonoid κ H) (two : ∀ (a b : H) (i₀ i₁ : Idx κ), i₀ ≠ i₁ →
      B.ksum (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b)
    (x : Idx κ → H) :
    letI := KMonoid.ofBare' B two
    ksum (κ := κ) x = B.ksum x := by
  show B.toIdxSumData.lsum (KMonoid.lt_succ (le_of_eq (mk_Idx κ))) x = B.ksum x
  rw [← B.toIdxSumData.tot_extend_eq (KMonoid.lt_succ (le_of_eq (mk_Idx κ)))
    (Function.Embedding.refl (Idx κ)) x]
  exact congrArg B.ksum
    (funext fun k => (Function.Embedding.refl (Idx κ)).injective.extend_apply x 0 k)

end KappaMonoid
