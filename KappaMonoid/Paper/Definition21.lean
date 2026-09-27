/-
**Definition 2.1 verbatim.**  `PaperKMonoid` transcribes the paper's definition literally - a
`Zero`, a map `Σ : H^κ → H`, (A1) at one distinguished index, (A2) for every bijection
`κ × κ ≃ κ` - and `toKMonoid` / `toPaper` show it agrees with the `KMonoid` the development
uses.  Nothing else depends on this file; it exists so that the working definition can be
checked against the paper's.
-/
import KappaMonoid.Core.Bare
import KappaMonoid.Core.Compatible

universe u v w

open Cardinal Function Set

namespace KappaMonoid

/-! ## Definition 2.1 verbatim, and its equivalence with `KMonoid`

`KMonoid` deviates from Definition 2.1 of the paper in three ways: sums are taken over an
arbitrary index type rather than over `κ` itself, (A1) appears as "a sum over a one-point index
type is its unique entry" rather than as a statement about the distinguished element `0 ∈ κ`, and
the commutative monoid structure is carried along rather than reconstructed.  This section
transcribes the paper's definition literally and shows that the two notions agree. -/

/-- **Definition 2.1**, verbatim: a set `H` with an element `0` and a map `Σ : H^κ → H` such that

* (A1) if `x ∈ H^κ` has `x i = 0` for all `i ≠ 0`, then `Σ x = x 0`;
* (A2) if `x ∈ H^{κ×κ}` and `π : κ × κ → κ` is a bijection, then `Σᵢ Σⱼ x i j = Σₖ x (π⁻¹ k)`.

The distinguished element `0 ∈ κ` of the paper is here an arbitrary index `i₀ : Idx κ`; (A1) is
assumed at `i₀` only, exactly as in the paper. -/
structure PaperKMonoid (κ : Cardinal.{u}) (H : Type v) [Zero H] where
  /-- `κ` is an infinite cardinal. -/
  aleph0_le : ℵ₀ ≤ κ
  /-- The distinguished index, playing the role of `0 ∈ κ`. -/
  i₀ : Idx κ
  /-- The summation `Σ : H^κ → H`. -/
  sigma : (Idx κ → H) → H
  /-- (A1), at the distinguished index. -/
  A1 : ∀ x : Idx κ → H, (∀ i, i ≠ i₀ → x i = 0) → sigma x = x i₀
  /-- (A2). -/
  A2 : ∀ (x : Idx κ → Idx κ → H) (π : Idx κ × Idx κ ≃ Idx κ),
      sigma (fun i => sigma (x i)) = sigma fun k => x (π.symm k).1 (π.symm k).2

namespace PaperKMonoid

variable {κ : Cardinal.{u}} {H : Type v} [Zero H] (P : PaperKMonoid κ H)

include P

/-- (A3), the first half of Lemma 2.5: `Σ` is invariant under permutations of `κ`.

Paper proof: spread `x` out as `y i j := if j = 0 then x i else 0`, so that `Σⱼ y i j = x i` by
(A1) — this is the only place (A1) is used, and it is used at the distinguished index — then
apply (A2) once with `f ∘ (π⁻¹, id)` and once with `f`, for an arbitrary bijection
`f : κ × κ ≃ κ`. -/
theorem sigma_perm (x : Idx κ → H) (π : Idx κ ≃ Idx κ) : P.sigma x = P.sigma (x ∘ π) := by
  set y : Idx κ → Idx κ → H := fun i j => if j = P.i₀ then x i else 0 with hy
  set w : Idx κ → Idx κ → H := fun i j => y (π i) j with hw
  have hxy : ∀ i, P.sigma (y i) = x i := fun i =>
    (P.A1 (y i) fun j hj => if_neg hj).trans (if_pos rfl)
  set f := pairEquiv P.aleph0_le with hf
  set g : Idx κ × Idx κ ≃ Idx κ := (π.symm.prodCongr (Equiv.refl (Idx κ))).trans f with hg
  have hgsymm : ∀ l : Idx κ, g.symm l = (π (f.symm l).1, (f.symm l).2) := by
    intro l
    apply Prod.ext <;>
      simp [hg, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  have hstep : (fun l => y (g.symm l).1 (g.symm l).2) = fun l => w (f.symm l).1 (f.symm l).2 := by
    funext l
    rw [hgsymm l]
  calc P.sigma x = P.sigma (fun i => P.sigma (y i)) := by congr 1; funext i; exact (hxy i).symm
    _ = P.sigma (fun l => y (g.symm l).1 (g.symm l).2) := P.A2 y g
    _ = P.sigma (fun l => w (f.symm l).1 (f.symm l).2) := congrArg _ hstep
    _ = P.sigma (fun i => P.sigma (w i)) := (P.A2 w f).symm
    _ = P.sigma (x ∘ π) := by congr 1; funext i; exact hxy (π i)

/-- (A1) at an *arbitrary* index, which is how `KMonoid` states it: transport the paper's (A1)
along the transposition exchanging that index with the distinguished one. -/
theorem sigma_single (a : Idx κ) (x : Idx κ → H) (hx : ∀ i, i ≠ a → x i = 0) :
    P.sigma x = x a := by
  classical
  by_cases ha : a = P.i₀
  · subst ha; exact P.A1 x hx
  · have hzero : ∀ i, i ≠ P.i₀ → (x ∘ Equiv.swap a P.i₀) i = 0 := by
      intro i hi
      refine hx _ fun hcon => ?_
      by_cases hia : i = a
      · subst hia
        rw [Equiv.swap_apply_left] at hcon
        exact ha hcon.symm
      · rw [Equiv.swap_apply_of_ne_of_ne hia hi] at hcon
        exact hia hcon
    rw [P.sigma_perm x (Equiv.swap a P.i₀), P.A1 _ hzero]
    show x (Equiv.swap a P.i₀ P.i₀) = x a
    rw [Equiv.swap_apply_right]

/-- The bare `κ`-monoid data underlying the paper's definition. -/
noncomputable def toBare : BareKMonoid κ H where
  aleph0_le := P.aleph0_le
  ksum := P.sigma
  ksum_single := P.sigma_single
  ksum_sigma := P.A2

/-- **Every `κ`-monoid in the sense of the paper is one in the sense of `KMonoid`.** -/
@[instance_reducible]
noncomputable def toKMonoid : KMonoid κ H := KMonoid.ofBare P.toBare

/-- The reconstructed `κ`-monoid has the paper's `Σ` as its `κ`-indexed summation (and, by
construction, the paper's `0` as its zero). -/
@[simp] theorem toKMonoid_ksum (x : Idx κ → H) :
    letI := P.toKMonoid
    KMonoid.ksum (κ := κ) x = P.sigma x := KMonoid.ofBare_ksum P.toBare x

/-- Nothing is added by the reconstruction: sums over an arbitrary index type are zero-padded
`Σ`'s. -/
theorem toKMonoid_sumOf {ι : Type u} (h : #ι ≤ κ) (x : ι → H) :
    letI := P.toKMonoid
    ∑[≤ κ] i, x i = P.sigma (Function.extend (emb h) x 0) := by
  let := P.toKMonoid
  exact (KMonoid.sumOf_eq_extend (h := CardLE.mk' h) (emb h) x).trans (P.toKMonoid_ksum _)

/-- Nor by the addition: it is a two-term `Σ`. -/
theorem toKMonoid_add (a b : H) {i₀ i₁ : Idx κ} (hne : i₀ ≠ i₁) :
    letI := P.toKMonoid
    a + b = P.sigma (fun i => if i = i₀ then a else if i = i₁ then b else 0) := by
  let := P.toKMonoid
  rw [← P.toKMonoid_ksum, KMonoid.ksum_two a b i₀ i₁ hne]

/-- **Remark 2.2(1)**: commutativity is automatic.  In terms of the paper's own data, a two-term
`Σ` does not depend on the order of its terms, although neither (A1) nor (A2) says so.

Paper proof: (A3) of Lemma 2.5 (`sigma_perm`), applied to the transposition of the two indices;
here it is read off from the reconstructed `κ`-monoid, whose addition is the two-term `Σ`
(`toKMonoid_add`) and is commutative. -/
theorem sigma_pair_comm (a b : H) {i₀ i₁ : Idx κ} (hne : i₀ ≠ i₁) :
    P.sigma (fun i => if i = i₀ then a else if i = i₁ then b else 0)
      = P.sigma (fun i => if i = i₀ then b else if i = i₁ then a else 0) := by
  let := P.toKMonoid
  rw [← P.toKMonoid_add a b hne, ← P.toKMonoid_add b a hne, add_comm]

end PaperKMonoid

/-- **Conversely, every `KMonoid` is a `κ`-monoid in the sense of the paper.**  Any index may be
taken as the distinguished one, since `KMonoid` assumes (A1) at every index. -/
noncomputable def KMonoid.toPaper (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] :
    PaperKMonoid κ H where
  aleph0_le := KMonoid.aleph0_le (κ := κ) (H := H)
  i₀ := (nonempty_Idx (KMonoid.aleph0_le (κ := κ) (H := H))).some
  sigma := KMonoid.ksum (κ := κ)
  A1 := fun x hx => KMonoid.ksum_single _ x hx
  A2 := fun x π => KMonoid.ksum_sigma x π

@[simp] theorem KMonoid.toPaper_sigma (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H]
    (x : Idx κ → H) : (KMonoid.toPaper κ H).sigma x = KMonoid.ksum (κ := κ) x := rfl

/-- The round trip `toPaper` then `toKMonoid` gives back the same `κ`-indexed `Σ`: `toPaper` changes
neither `0` nor `Σ`, and `PaperKMonoid.toKMonoid` recovers them (`PaperKMonoid.toKMonoid_ksum`).
The equality of the whole structures is `KMonoid.toPaper_toKMonoid`, below. -/
theorem KMonoid.toPaper_toKMonoid_ksum (κ : Cardinal.{u}) (H : Type v) [inst : KMonoid κ H]
    (x : Idx κ → H) :
    @KMonoid.ksum κ H (KMonoid.toPaper κ H).toKMonoid x = @KMonoid.ksum κ H inst x :=
  (KMonoid.toPaper κ H).toKMonoid_ksum x

/-- **The round trip `KMonoid → Definition 2.1 → KMonoid` is the identity**, as an equality of
structures: sums over every index type and the addition come back unchanged, so a `κ`-monoid is
exactly the data of Definition 2.1. -/
theorem KMonoid.toPaper_toKMonoid (κ : Cardinal.{u}) (H : Type v) [inst : KMonoid κ H] :
    (KMonoid.toPaper κ H).toKMonoid = inst := by
  obtain ⟨i₀, i₁, hne⟩ := (nontrivial_Idx (KMonoid.aleph0_le (κ := κ) (H := H))).exists_pair_ne
  refine KMonoid.ext_of_sumOf ?_ ?_
  · funext a b
    exact ((KMonoid.toPaper κ H).toKMonoid_add a b hne).trans (KMonoid.ksum_two a b i₀ i₁ hne)
  · intro ι h x
    exact ((KMonoid.toPaper κ H).toKMonoid_sumOf h x).trans
      (KMonoid.sumOf_eq_extend (h := CardLE.mk' h) (emb h) x).symm

end KappaMonoid
