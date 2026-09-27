/-
Reconstructing a `κ`-monoid from `κ`-indexed data (**Lemma 2.5** at the `κ`-level):
`BareKMonoid` and `KMonoid.ofBare`, which is what §§3-4 supply.
-/
import KappaMonoid.Core.Subobject

universe u v w

open Cardinal Function Set

namespace KappaMonoid

/-! ## Reconstructing a `κ`-monoid from `κ`-indexed data (Lemma 2.5)

The constructions of Sections 3 and 4 produce a summation operation for `Idx κ`-indexed
families only.  This section turns such data into a `κ`-monoid: an arbitrary family of size
`≤ κ` is summed by padding it with zeros along an embedding into `Idx κ`, the point being
that the result does not depend on the embedding chosen. -/

/-- Two embeddings whose ranges have equinumerous complements differ by a permutation. -/
theorem exists_perm_comp {ι : Type u} {κ : Cardinal.{u}} (e₁ e₂ : ι ↪ Idx κ)
    (h : #(↥(Set.range ⇑e₁)ᶜ) = #(↥(Set.range ⇑e₂)ᶜ)) :
    ∃ σ : Idx κ ≃ Idx κ, ∀ i, σ (e₁ i) = e₂ i := by
  classical
  obtain ⟨γ⟩ := Cardinal.eq.mp h
  set α : ↥(Set.range ⇑e₁) ≃ ↥(Set.range ⇑e₂) :=
    (Equiv.ofInjective _ e₁.injective).symm.trans (Equiv.ofInjective _ e₂.injective) with hα
  refine ⟨(Equiv.Set.sumCompl (Set.range ⇑e₁)).symm.trans
    ((α.sumCongr γ).trans (Equiv.Set.sumCompl (Set.range ⇑e₂))), fun i => ?_⟩
  have hmem : e₁ i ∈ Set.range ⇑e₁ := ⟨i, rfl⟩
  have hval : α ⟨e₁ i, hmem⟩ = Equiv.ofInjective _ e₂.injective i := by
    rw [hα, Equiv.trans_apply]
    congr 1
    apply (Equiv.ofInjective _ e₁.injective).injective
    rw [Equiv.apply_symm_apply]
    rfl
  show (Equiv.Set.sumCompl (Set.range ⇑e₂))
      ((α.sumCongr γ) ((Equiv.Set.sumCompl (Set.range ⇑e₁)).symm (e₁ i))) = e₂ i
  rw [Equiv.Set.sumCompl_symm_apply_of_mem hmem, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.Set.sumCompl_apply_inl, hval]
  rfl

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

include B

/-- A fixed bijection `Idx κ × Idx κ ≃ Idx κ`. -/
noncomputable def pair : Idx κ × Idx κ ≃ Idx κ := pairEquiv B.aleph0_le

theorem ksum_zero : B.ksum (fun _ => 0) = 0 :=
  B.ksum_single _ fun _ _ => rfl

/-- (A3), the first half of Lemma 2.5: `Σ` is invariant under permutations of `κ`.

Paper proof: spread `x` out as `y i j := if j = 0 then x i else 0`, so that `Σⱼ y i j = x i` by
(A1) — this is the only place (A1) is used, and it is used at the distinguished index — then
apply (A2) once with `f ∘ (π⁻¹, id)` and once with `f`, for an arbitrary bijection
`f : κ × κ ≃ κ`. -/
theorem ksum_perm (x : Idx κ → H) (π : Idx κ ≃ Idx κ) : B.ksum x = B.ksum (x ∘ π) := by
  set y : Idx κ → Idx κ → H := fun i j => if j = B.i₀ then x i else 0 with hy
  set w : Idx κ → Idx κ → H := fun i j => y (π i) j
  have hxy : ∀ i, B.ksum (y i) = x i := fun i =>
    (B.ksum_single (y i) fun j hj => if_neg hj).trans (if_pos rfl)
  set f := B.pair with hf
  set g : Idx κ × Idx κ ≃ Idx κ := (π.symm.prodCongr (Equiv.refl (Idx κ))).trans f with hg
  have hgsymm : ∀ l : Idx κ, g.symm l = (π (f.symm l).1, (f.symm l).2) := by
    intro l
    apply Prod.ext <;>
      simp [hg, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  have hstep : (fun l => y (g.symm l).1 (g.symm l).2) = fun l => w (f.symm l).1 (f.symm l).2 := by
    funext l
    rw [hgsymm l]
  calc B.ksum x = B.ksum (fun i => B.ksum (y i)) := by congr 1; funext i; exact (hxy i).symm
    _ = B.ksum (fun l => y (g.symm l).1 (g.symm l).2) := B.ksum_sigma y g
    _ = B.ksum (fun l => w (f.symm l).1 (f.symm l).2) := congrArg _ hstep
    _ = B.ksum (fun i => B.ksum (w i)) := (B.ksum_sigma w f).symm
    _ = B.ksum (x ∘ π) := by congr 1; funext i; exact hxy (π i)

/-- (A1) at an *arbitrary* index: transport (A1) along the transposition exchanging that index
with the distinguished one. -/
theorem ksum_single_at (a : Idx κ) (x : Idx κ → H) (hx : ∀ i, i ≠ a → x i = 0) :
    B.ksum x = x a := by
  classical
  by_cases ha : a = B.i₀
  · subst ha; exact B.ksum_single x hx
  · have hzero : ∀ i, i ≠ B.i₀ → (x ∘ Equiv.swap a B.i₀) i = 0 := by
      intro i hi
      refine hx _ fun hcon => ?_
      by_cases hia : i = a
      · subst hia
        rw [Equiv.swap_apply_left] at hcon
        exact ha hcon.symm
      · rw [Equiv.swap_apply_of_ne_of_ne hia hi] at hcon
        exact hia hcon
    rw [B.ksum_perm x (Equiv.swap a B.i₀), B.ksum_single _ hzero]
    show x (Equiv.swap a B.i₀ B.i₀) = x a
    rw [Equiv.swap_apply_right]

/-- The "first row" embedding `i ↦ (i, i₀)` of `Idx κ` into itself. -/
noncomputable def row : Idx κ ↪ Idx κ :=
  ⟨fun i => B.pair (i, B.i₀), fun _ _ h => (Prod.ext_iff.mp (B.pair.injective h)).1⟩

/-- Zero-padding along `row` does not change the sum: this is (A2) applied to a family
concentrated in one column. -/
theorem ksum_row (z : Idx κ → H) : B.ksum (Function.extend ⇑B.row z 0) = B.ksum z := by
  set Y : Idx κ → Idx κ → H := fun i j => if j = B.i₀ then z i else 0
  have hYsum : ∀ i, B.ksum (Y i) = z i := fun i =>
    (B.ksum_single (Y i) fun j hj => if_neg hj).trans (if_pos rfl)
  have hkey : ∀ k, Y (B.pair.symm k).1 (B.pair.symm k).2 = Function.extend ⇑B.row z 0 k := by
    intro k
    by_cases hk : ∃ i, B.row i = k
    · obtain ⟨i, rfl⟩ := hk
      have hps : B.pair.symm (B.row i) = (i, B.i₀) := B.pair.symm_apply_apply (i, B.i₀)
      rw [hps]
      show (if B.i₀ = B.i₀ then z i else 0) = _
      rw [if_pos rfl, B.row.injective.extend_apply]
    · have hne : (B.pair.symm k).2 ≠ B.i₀ := by
        intro heq
        exact hk ⟨(B.pair.symm k).1, by
          show B.pair ((B.pair.symm k).1, B.i₀) = k
          rw [← heq]
          exact B.pair.apply_symm_apply k⟩
      show (if (B.pair.symm k).2 = B.i₀ then _ else 0) = _
      rw [if_neg hne, Function.extend_apply' z (0 : Idx κ → H) k hk]
      rfl
  calc B.ksum (Function.extend ⇑B.row z 0)
      = B.ksum (fun k => Y (B.pair.symm k).1 (B.pair.symm k).2) := by
        congr 1; funext k; exact (hkey k).symm
    _ = B.ksum (fun i => B.ksum (Y i)) := (B.ksum_sigma Y B.pair).symm
    _ = B.ksum z := by congr 1; funext i; exact hYsum i

theorem mk_compl_row : #(↥(Set.range ⇑B.row)ᶜ) = κ := by
  have := nontrivial_Idx B.aleph0_le
  obtain ⟨j₁, hj₁⟩ := exists_ne B.i₀
  have hmem : ∀ i : Idx κ, B.pair (i, j₁) ∈ (Set.range ⇑B.row)ᶜ := by
    rintro i ⟨i', hi'⟩
    exact hj₁ (Prod.ext_iff.mp (B.pair.injective hi')).2.symm
  have hinj : Function.Injective
      (fun i : Idx κ => (⟨B.pair (i, j₁), hmem i⟩ : ↥(Set.range ⇑B.row)ᶜ)) := by
    intro a b hab
    exact (Prod.ext_iff.mp (B.pair.injective (congrArg Subtype.val hab))).1
  exact le_antisymm ((Cardinal.mk_set_le _).trans_eq (mk_Idx κ))
    ((mk_Idx κ).symm.trans_le (Cardinal.mk_le_of_injective hinj))

/-- Composing with `row` forces the complement of the range to have full cardinality. -/
theorem mk_compl_trans {ι : Type u} (e : ι ↪ Idx κ) :
    #(↥(Set.range ⇑(e.trans B.row))ᶜ) = κ := by
  have hsub : (Set.range ⇑B.row)ᶜ ⊆ (Set.range ⇑(e.trans B.row))ᶜ := by
    apply Set.compl_subset_compl.mpr
    rintro k ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  exact le_antisymm ((Cardinal.mk_set_le _).trans_eq (mk_Idx κ))
    (B.mk_compl_row.symm.trans_le (Cardinal.mk_le_mk_of_subset hsub))

/-- Zero-padded sums do not depend on the embedding, as long as both ranges have large
complement. -/
theorem ksum_extend_congr {ι : Type u} (e₁ e₂ : ι ↪ Idx κ) (h₁ : #(↥(Set.range ⇑e₁)ᶜ) = κ)
    (h₂ : #(↥(Set.range ⇑e₂)ᶜ) = κ) (x : ι → H) :
    B.ksum (Function.extend ⇑e₁ x 0) = B.ksum (Function.extend ⇑e₂ x 0) := by
  obtain ⟨σ, hσ⟩ := exists_perm_comp e₁ e₂ (h₁.trans h₂.symm)
  have hfun : Function.extend ⇑e₂ x 0 = (Function.extend ⇑e₁ x 0) ∘ σ.symm := by
    funext k
    by_cases hk : ∃ i, e₂ i = k
    · obtain ⟨i, rfl⟩ := hk
      show Function.extend ⇑e₂ x 0 (e₂ i) = Function.extend ⇑e₁ x 0 (σ.symm (e₂ i))
      rw [e₂.injective.extend_apply, ← hσ i, Equiv.symm_apply_apply, e₁.injective.extend_apply]
    · have hnot : ¬ ∃ i, e₁ i = σ.symm k := by
        rintro ⟨i, hi⟩
        exact hk ⟨i, by rw [← hσ i, hi, Equiv.apply_symm_apply]⟩
      show Function.extend ⇑e₂ x 0 k = Function.extend ⇑e₁ x 0 (σ.symm k)
      rw [Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ hnot]
      rfl
  rw [hfun]
  exact B.ksum_perm _ σ.symm

/-- The sum of a family indexed by an arbitrary type of cardinality `≤ κ`. -/
noncomputable def bsum {ι : Type u} (h : #ι ≤ κ) (x : ι → H) : H :=
  B.ksum (Function.extend ⇑((emb h).trans B.row) x 0)

theorem extend_trans_row {ι : Type u} (e : ι ↪ Idx κ) (x : ι → H) :
    Function.extend ⇑(e.trans B.row) x 0 = Function.extend ⇑B.row (Function.extend ⇑e x 0) 0 := by
  have hraw := Function.Injective.extend_comp e.injective B.row.injective x (0 : Idx κ → H)
  have h0 : (0 : Idx κ → H) ∘ (⇑B.row) = (0 : Idx κ → H) := rfl
  rw [h0] at hraw
  exact hraw

/-- `bsum` may be computed using *any* embedding of the index type into `Idx κ`. -/
theorem ksum_extend_eq {ι : Type u} (h : #ι ≤ κ) (e : ι ↪ Idx κ) (x : ι → H) :
    B.ksum (Function.extend ⇑e x 0) = B.bsum h x := by
  have h1 : B.ksum (Function.extend ⇑(e.trans B.row) x 0) = B.ksum (Function.extend ⇑e x 0) := by
    rw [B.extend_trans_row e x]; exact B.ksum_row _
  exact h1.symm.trans
    (B.ksum_extend_congr (e.trans B.row) ((emb h).trans B.row) (B.mk_compl_trans e)
      (B.mk_compl_trans (emb h)) x)

theorem bsum_unique {ι : Type u} [Unique ι] (h : #ι ≤ κ) (x : ι → H) : B.bsum h x = x default := by
  set E := (emb h).trans B.row with hE
  show B.ksum (Function.extend ⇑E x 0) = x default
  rw [B.ksum_single_at (E default) _ ?_, E.injective.extend_apply]
  intro j hj
  by_cases hjk : ∃ i, E i = j
  · obtain ⟨i, rfl⟩ := hjk
    exact absurd (congrArg E (Unique.eq_default i)) hj
  · exact Function.extend_apply' _ _ _ hjk

theorem bsum_congr {ι ι' : Type u} (h : #ι ≤ κ) (h' : #ι' ≤ κ) (e : ι ≃ ι') (x : ι' → H) :
    B.bsum h (x ∘ e) = B.bsum h' x := by
  set E' : ι' ↪ Idx κ := (emb h').trans B.row
  have hE : Function.extend ⇑(e.toEmbedding.trans E') (x ∘ e) 0 = Function.extend ⇑E' x 0 := by
    funext k
    by_cases hk : ∃ i', E' i' = k
    · obtain ⟨i', rfl⟩ := hk
      have hval : (e.toEmbedding.trans E') (e.symm i') = E' i' := by
        show E' (e (e.symm i')) = _
        rw [Equiv.apply_symm_apply]
      rw [E'.injective.extend_apply, ← hval,
        (e.toEmbedding.trans E').injective.extend_apply]
      show x (e (e.symm i')) = x i'
      rw [Equiv.apply_symm_apply]
    · have hnot : ¬ ∃ i, (e.toEmbedding.trans E') i = k := by
        rintro ⟨i, hi⟩
        exact hk ⟨e i, hi⟩
      rw [Function.extend_apply' _ _ _ hnot, Function.extend_apply' _ _ _ hk]
  rw [← B.ksum_extend_eq h (e.toEmbedding.trans E') (x ∘ e), hE]
  exact B.ksum_extend_eq h' E' x

theorem bsum_sigma {ι : Type u} {ρ : ι → Type u} (h : #ι ≤ κ) (hρ : ∀ i, #(ρ i) ≤ κ)
    (x : ∀ i, ρ i → H) (hσ : #((i : ι) × ρ i) ≤ κ) :
    B.bsum h (fun i => B.bsum (hρ i) (x i)) = B.bsum hσ (fun p => x p.1 p.2) := by
  set e : ι ↪ Idx κ := (emb h).trans B.row with hedef
  set f : ∀ i, ρ i ↪ Idx κ := fun i => (emb (hρ i)).trans B.row
  set π : Idx κ × Idx κ ≃ Idx κ := B.pair with hπdef
  set E : ((i : ι) × ρ i) ↪ Idx κ := ⟨fun p => π (e p.1, f p.1 p.2), by
    rintro ⟨i1, r1⟩ ⟨i2, r2⟩ hEq
    have hpair : (e i1, f i1 r1) = (e i2, f i2 r2) := π.injective hEq
    have hi : i1 = i2 := e.injective (Prod.ext_iff.mp hpair).1
    subst hi
    exact congrArg _ ((f i1).injective (Prod.ext_iff.mp hpair).2)⟩ with hEdef
  set W : ∀ _ : ι, Idx κ → H := fun i => Function.extend ⇑(f i) (x i) 0 with hWdef
  set G : Idx κ → (Idx κ → H) := Function.extend ⇑e W (fun _ => (0 : Idx κ → H)) with hGdef
  have hGa : ∀ a, B.ksum (G a) = Function.extend ⇑e (fun i => B.ksum (W i)) 0 a := by
    intro a
    by_cases ha : ∃ i, e i = a
    · obtain ⟨i, rfl⟩ := ha
      rw [hGdef, e.injective.extend_apply, e.injective.extend_apply]
    · rw [hGdef, Function.extend_apply' W (fun _ => (0 : Idx κ → H)) a ha,
        Function.extend_apply' (fun i => B.ksum (W i)) (0 : Idx κ → H) a ha]
      exact B.ksum_zero
  have hGk : ∀ k, G (π.symm k).1 (π.symm k).2 = Function.extend ⇑E (fun p => x p.1 p.2) 0 k := by
    intro k
    by_cases ha : ∃ i, e i = (π.symm k).1
    · obtain ⟨i, hi⟩ := ha
      have hGaeq : G (π.symm k).1 = W i := by rw [hGdef, ← hi, e.injective.extend_apply]
      rw [hGaeq]
      by_cases hb : ∃ r, f i r = (π.symm k).2
      · obtain ⟨r, hr⟩ := hb
        have hWeq : W i (π.symm k).2 = x i r := by
          rw [hWdef, ← hr]
          exact (f i).injective.extend_apply (x i) 0 r
        have hEk : E ⟨i, r⟩ = k := by
          show π (e i, f i r) = k
          rw [hi, hr]
          exact π.apply_symm_apply k
        rw [hWeq, ← hEk, E.injective.extend_apply]
      · show Function.extend ⇑(f i) (x i) 0 (π.symm k).2 = _
        rw [Function.extend_apply' (x i) (0 : Idx κ → H) (π.symm k).2 hb]
        symm
        apply Function.extend_apply'
        rintro ⟨⟨i', r'⟩, hp⟩
        have heqp : (e i', f i' r') = π.symm k := by
          rw [← hp]; exact (π.symm_apply_apply (e i', f i' r')).symm
        have hii : i' = i := e.injective ((congrArg Prod.fst heqp).trans hi.symm)
        subst hii
        exact hb ⟨r', congrArg Prod.snd heqp⟩
    · have hGaeq : G (π.symm k).1 = fun _ => (0 : H) := by
        rw [hGdef]
        exact Function.extend_apply' W (fun _ => (0 : Idx κ → H)) (π.symm k).1 ha
      rw [hGaeq]
      symm
      apply Function.extend_apply'
      rintro ⟨⟨i', r'⟩, hp⟩
      have heqp : (e i', f i' r') = π.symm k := by
        rw [← hp]; exact (π.symm_apply_apply (e i', f i' r')).symm
      exact ha ⟨i', congrArg Prod.fst heqp⟩
  calc B.bsum h (fun i => B.bsum (hρ i) (x i))
      = B.ksum (fun a => B.ksum (G a)) := by
        show B.ksum (Function.extend ⇑e (fun i => B.ksum (W i)) 0) = _
        congr 1
        funext a
        exact (hGa a).symm
    _ = B.ksum (fun k => G (π.symm k).1 (π.symm k).2) := B.ksum_sigma G π
    _ = B.ksum (Function.extend ⇑E (fun p => x p.1 p.2) 0) := by
        congr 1; funext k; exact hGk k
    _ = B.bsum hσ (fun p => x p.1 p.2) := B.ksum_extend_eq hσ E _

/-- The summation data determined by the bare data. -/
noncomputable def sumData : SumData (Order.succ κ) H where
  isRegular := Cardinal.isRegular_succ B.aleph0_le
  sum := fun h x => B.bsum (KMonoid.le_of_lt_succ h) x
  sum_congr := fun _ _ e x => B.bsum_congr _ _ e x
  sum_unique := fun _ x => B.bsum_unique _ x
  sum_sigma := fun _ hρ x hσ =>
    B.bsum_sigma _ (fun i => KMonoid.le_of_lt_succ (hρ i)) x (KMonoid.le_of_lt_succ hσ)

theorem sumData_zero : B.sumData.zero = 0 := by
  show B.bsum _ (PEmpty.elim : PEmpty.{u + 1} → H) = 0
  show B.ksum _ = 0
  have heq : Function.extend ⇑((emb (KMonoid.le_of_lt_succ (B.sumData.small PEmpty.{u + 1})))
      |>.trans B.row) (PEmpty.elim : PEmpty.{u + 1} → H) (0 : Idx κ → H) = fun _ => 0 := by
    funext k
    exact Function.extend_apply' _ _ _ (by rintro ⟨p, _⟩; exact p.elim)
  rw [heq]
  exact B.ksum_zero

end BareKMonoid

/-- A `κ`-monoid is determined by its `κ`-indexed summation: the bullets after **Lemma 2.5**,
whose (A3) is `BareKMonoid.ksum_perm`. -/
@[instance_reducible]
noncomputable def KMonoid.ofBare {κ : Cardinal.{u}} {H : Type v} [Zero H]
    (B : BareKMonoid κ H) : KMonoid κ H :=
  { toLMonoid := B.sumData.toLMonoidOfZero B.sumData_zero
    aleph0_le := B.aleph0_le }

@[simp] theorem KMonoid.ofBare_ksum {κ : Cardinal.{u}} {H : Type v} [Zero H]
    (B : BareKMonoid κ H) (x : Idx κ → H) :
    letI := KMonoid.ofBare B
    ksum (κ := κ) x = B.ksum x := by
  show B.bsum (le_of_eq (mk_Idx κ)) x = B.ksum x
  rw [← B.ksum_extend_eq (le_of_eq (mk_Idx κ)) (Function.Embedding.refl (Idx κ)) x]
  congr 1
  funext k
  exact (Function.Embedding.refl (Idx κ)).injective.extend_apply x 0 k

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
noncomputable def KMonoid.ofKsum {κ : Cardinal.{u}} {H : Type v} [AddCommMonoid H]
    (B : BareKMonoid κ H)
    (two : ∀ (a b : H) (i₀ i₁ : Idx κ), i₀ ≠ i₁ →
      B.ksum (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b) :
    KMonoid κ H := by
  classical
  refine { toLMonoid := B.sumData.toLMonoid' ?_, aleph0_le := B.aleph0_le }
  intro h a b
  set E : (PUnit.{u + 1} ⊕ PUnit.{u + 1}) ↪ Idx κ :=
    (emb (KMonoid.le_of_lt_succ h)).trans B.row with hEdef
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
  show a + b = B.ksum (Function.extend ⇑E (Sum.elim (fun _ => a) (fun _ => b)) 0)
  rw [hfun, two a b _ _ hne]

@[simp] theorem KMonoid.ofKsum_ksum {κ : Cardinal.{u}} {H : Type v} [AddCommMonoid H]
    (B : BareKMonoid κ H) (two : ∀ (a b : H) (i₀ i₁ : Idx κ), i₀ ≠ i₁ →
      B.ksum (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b)
    (x : Idx κ → H) :
    letI := KMonoid.ofKsum B two
    ksum (κ := κ) x = B.ksum x := by
  show B.bsum (le_of_eq (mk_Idx κ)) x = B.ksum x
  rw [← B.ksum_extend_eq (le_of_eq (mk_Idx κ)) (Function.Embedding.refl (Idx κ)) x]
  congr 1
  funext k
  exact (Function.Embedding.refl (Idx κ)).injective.extend_apply x 0 k

end KappaMonoid
