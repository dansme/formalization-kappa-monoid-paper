/-
`IdxSumData λ μ H`: a summation on the families indexed by the one type `Idx μ`, and its
extension, by zero padding, to families indexed by an arbitrary type of cardinality `< λ`
(**Lemma 2.5** and the bullets after it).

Both of the paper's definitions are of this shape: Definition 2.1 sums all `κ`-indexed families
(`μ = κ`, `λ = κ⁺`, see `BareKMonoid`), Definition 2.18 sums the `λ`-indexed families of support
`< λ` (`μ = λ`, see `PaperLMonoid`).  The extension is done once, here, for both.
-/
import KappaMonoid.Core.SumData

universe u v

open Cardinal Function Set

namespace KappaMonoid

/-- A subset of a set of size `< λ` has size `< λ`. -/
theorem mk_lt_of_subset' {α : Type u} {lam : Cardinal.{u}} {S T : Set α} (h : S ⊆ T)
    (hT : #T < lam) : #S < lam :=
  (Cardinal.mk_le_mk_of_subset h).trans_lt hT

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

/-- A summation `tot` on the `Idx μ`-indexed families, subject to the paper's two axioms:
(A1)/(B1) at a distinguished index `i₀`, and (A2)/(B2) for families `x : μ × μ → H` with fewer
than `λ` nonzero rows and columns.  `λ` is regular and at most `μ⁺`, so that every index type of
size `< λ` embeds into `Idx μ`.  Outside the families it is meant to sum, `tot` may take any
value: only families of support `< λ` are ever summed. -/
structure IdxSumData (lam μ : Cardinal.{u}) (H : Type v) [Zero H] where
  /-- `λ` is regular. -/
  isRegular : lam.IsRegular
  /-- `μ` is infinite. -/
  aleph0_le : ℵ₀ ≤ μ
  /-- Every index type of size `< λ` has size `≤ μ`. -/
  le_succ : lam ≤ Order.succ μ
  /-- The distinguished index, playing the role of `0 ∈ μ`. -/
  i₀ : Idx μ
  /-- The summation of `Idx μ`-indexed families. -/
  tot : (Idx μ → H) → H
  /-- (A1)/(B1), at the distinguished index. -/
  tot_single : ∀ x : Idx μ → H, (∀ i, i ≠ i₀ → x i = 0) → tot x = x i₀
  /-- (A2)/(B2), for families with fewer than `λ` nonzero rows and columns. -/
  tot_sigma : ∀ x : Idx μ → Idx μ → H, #{i | ∃ j, x i j ≠ 0} < lam → #{j | ∃ i, x i j ≠ 0} < lam →
    ∀ π : Idx μ × Idx μ ≃ Idx μ,
      tot (fun i => tot (x i)) = tot (fun k => x (π.symm k).1 (π.symm k).2)

namespace IdxSumData

variable {lam μ : Cardinal.{u}} {H : Type v} [Zero H] (D : IdxSumData lam μ H)

include D in
theorem mk_singleton_lt (a : Idx μ) : #(↥({a} : Set (Idx μ))) < lam := by
  rw [Cardinal.mk_singleton]
  exact Cardinal.one_lt_aleph0.trans_le D.isRegular.aleph0_le

include D in
/-- An index type of size `< λ` has size `≤ μ`, so it embeds into `Idx μ`. -/
theorem le_of_lt {ι : Type u} (h : #ι < lam) : #ι ≤ μ :=
  Order.lt_succ_iff.mp (h.trans_le D.le_succ)

theorem tot_zero : D.tot (fun _ => 0) = 0 := D.tot_single _ fun _ _ => rfl

/-- (A3), the first half of Lemma 2.5: `Σ` is invariant under permutations of `μ`.

Paper proof: spread `x` out as `y i j := if j = 0 then x i else 0`, so that `Σⱼ y i j = x i` by
(A1) — this is the only place (A1) is used, and it is used at the distinguished index — then
apply (A2) once with `f ∘ (σ⁻¹, id)` and once with `f`, for a bijection `f : μ × μ ≃ μ`.  The
family `y` has fewer than `λ` nonzero rows because `x` has support `< λ`, and one nonzero
column. -/
theorem tot_perm {x : Idx μ → H} (hx : #(support x) < lam) (σ : Idx μ ≃ Idx μ) :
    D.tot x = D.tot (x ∘ σ) := by
  classical
  set y : Idx μ → Idx μ → H := fun i j => if j = D.i₀ then x i else 0 with hy
  set w : Idx μ → Idx μ → H := fun i j => y (σ i) j with hw
  have hxy : ∀ i, D.tot (y i) = x i := fun i =>
    (D.tot_single (y i) fun j hj => if_neg hj).trans (if_pos rfl)
  have hyrows : #{i | ∃ j, y i j ≠ 0} < lam := by
    refine mk_lt_of_subset' (T := support x) (fun i ⟨j, hj⟩ => ?_) hx
    by_cases hj0 : j = D.i₀
    · intro hxi
      exact hj (by simp only [hy, if_pos hj0]; exact hxi)
    · exact absurd (if_neg hj0) hj
  have hycols : #{j | ∃ i, y i j ≠ 0} < lam :=
    mk_lt_of_subset' (T := {D.i₀}) (fun j ⟨_, hi⟩ => by_contra fun hj0 => hi (if_neg hj0))
      (D.mk_singleton_lt _)
  have hwrows : #{i | ∃ j, w i j ≠ 0} < lam :=
    (Cardinal.mk_le_of_injective
      (f := fun i : ↥{i | ∃ j, w i j ≠ 0} => (⟨σ i, i.2⟩ : ↥{i | ∃ j, y i j ≠ 0}))
      fun a b h => Subtype.ext (σ.injective (congrArg Subtype.val h))).trans_lt hyrows
  have hwcols : #{j | ∃ i, w i j ≠ 0} < lam :=
    mk_lt_of_subset' (T := {j | ∃ i, y i j ≠ 0}) (fun j ⟨i, hi⟩ => ⟨σ i, hi⟩) hycols
  set f := pairEquiv D.aleph0_le with hf
  set g : Idx μ × Idx μ ≃ Idx μ := (σ.symm.prodCongr (Equiv.refl (Idx μ))).trans f with hg
  have hgsymm : ∀ l : Idx μ, g.symm l = (σ (f.symm l).1, (f.symm l).2) := by
    intro l
    apply Prod.ext <;>
      simp [hg, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  have hstep : (fun l => y (g.symm l).1 (g.symm l).2) = fun l => w (f.symm l).1 (f.symm l).2 := by
    funext l
    rw [hgsymm l]
  calc D.tot x = D.tot (fun i => D.tot (y i)) := by congr 1; funext i; exact (hxy i).symm
    _ = D.tot (fun l => y (g.symm l).1 (g.symm l).2) := D.tot_sigma y hyrows hycols g
    _ = D.tot (fun l => w (f.symm l).1 (f.symm l).2) := congrArg _ hstep
    _ = D.tot (fun i => D.tot (w i)) := (D.tot_sigma w hwrows hwcols f).symm
    _ = D.tot (x ∘ σ) := by congr 1; funext i; exact hxy (σ i)

/-- (A1) at an *arbitrary* index: transport (A1) along the transposition exchanging that index
with the distinguished one. -/
theorem tot_single_at (a : Idx μ) (x : Idx μ → H) (hx : ∀ i, i ≠ a → x i = 0) :
    D.tot x = x a := by
  classical
  have hsupp : #(support x) < lam :=
    mk_lt_of_subset' (T := {a}) (fun i hi => by_contra fun h => hi (hx i h)) (D.mk_singleton_lt a)
  by_cases ha : a = D.i₀
  · subst ha; exact D.tot_single x hx
  · have hzero : ∀ i, i ≠ D.i₀ → (x ∘ Equiv.swap a D.i₀) i = 0 := by
      intro i hi
      refine hx _ fun hcon => ?_
      by_cases hia : i = a
      · subst hia
        rw [Equiv.swap_apply_left] at hcon
        exact ha hcon.symm
      · rw [Equiv.swap_apply_of_ne_of_ne hia hi] at hcon
        exact hia hcon
    rw [D.tot_perm hsupp (Equiv.swap a D.i₀), D.tot_single _ hzero]
    show x (Equiv.swap a D.i₀ D.i₀) = x a
    rw [Equiv.swap_apply_right]

/-! ### Zero padding

A family indexed by `ι` with `#ι < λ` is summed by padding it with zeros along an embedding into
`Idx μ`.  The result does not depend on the embedding as long as its range has a complement of
full size `μ`, which composing with the "first row" `i ↦ (i, i₀)` of `μ × μ ≃ μ` guarantees;
and padding along the first row does not change the sum, by (A2). -/

/-- The "first row" embedding `i ↦ (i, i₀)` of `Idx μ` into itself. -/
noncomputable def row : Idx μ ↪ Idx μ :=
  ⟨fun i => pairEquiv D.aleph0_le (i, D.i₀),
    fun _ _ h => (Prod.ext_iff.mp ((pairEquiv D.aleph0_le).injective h)).1⟩

/-- A family padded along an embedding of a small type has small support. -/
theorem small_extend {ι : Type u} (h : #ι < lam) (e : ι ↪ Idx μ) (x : ι → H) :
    #(support (extend e x 0)) < lam :=
  mk_lt_of_subset' (T := range e)
    (fun _ hk => by_contra fun hk' => hk (extend_apply' _ _ _ fun ⟨i, hi⟩ => hk' ⟨i, hi⟩))
    (Cardinal.mk_range_le.trans_lt h)

/-- Padding along the first row does not change the sum: this is (A2) applied to a family
concentrated in one column. -/
theorem tot_row {z : Idx μ → H} (hz : #(support z) < lam) :
    D.tot (extend D.row z 0) = D.tot z := by
  classical
  set π := pairEquiv D.aleph0_le
  set Y : Idx μ → Idx μ → H := fun i j => if j = D.i₀ then z i else 0
  have hYsum : ∀ i, D.tot (Y i) = z i := fun i =>
    (D.tot_single (Y i) fun j hj => if_neg hj).trans (if_pos rfl)
  have hrows : #{i | ∃ j, Y i j ≠ 0} < lam := by
    refine mk_lt_of_subset' (T := support z) (fun i ⟨j, hj⟩ => ?_) hz
    by_cases hj0 : j = D.i₀
    · intro hzi; exact hj (by simp only [Y, if_pos hj0]; exact hzi)
    · exact absurd (if_neg hj0) hj
  have hcols : #{j | ∃ i, Y i j ≠ 0} < lam :=
    mk_lt_of_subset' (T := {D.i₀}) (fun j ⟨_, hi⟩ => by_contra fun hj0 => hi (if_neg hj0))
      (D.mk_singleton_lt _)
  have hkey : ∀ k, Y (π.symm k).1 (π.symm k).2 = extend D.row z 0 k := by
    intro k
    by_cases hk : ∃ i, D.row i = k
    · obtain ⟨i, rfl⟩ := hk
      have hps : π.symm (D.row i) = (i, D.i₀) := π.symm_apply_apply (i, D.i₀)
      rw [hps]
      show (if D.i₀ = D.i₀ then z i else 0) = _
      rw [if_pos rfl, D.row.injective.extend_apply]
    · have hne : (π.symm k).2 ≠ D.i₀ := by
        intro heq
        exact hk ⟨(π.symm k).1, by
          show π ((π.symm k).1, D.i₀) = k
          rw [← heq]
          exact π.apply_symm_apply k⟩
      show (if (π.symm k).2 = D.i₀ then _ else 0) = _
      rw [if_neg hne, extend_apply' z (0 : Idx μ → H) k hk]
      rfl
  calc D.tot (extend D.row z 0)
      = D.tot (fun k => Y (π.symm k).1 (π.symm k).2) := by
        congr 1; funext k; exact (hkey k).symm
    _ = D.tot (fun i => D.tot (Y i)) := (D.tot_sigma Y hrows hcols π).symm
    _ = D.tot z := by congr 1; funext i; exact hYsum i

theorem mk_compl_row : #(↥(Set.range ⇑D.row)ᶜ) = μ := by
  have := nontrivial_Idx D.aleph0_le
  obtain ⟨j₁, hj₁⟩ := exists_ne D.i₀
  set π := pairEquiv D.aleph0_le
  have hmem : ∀ i : Idx μ, π (i, j₁) ∈ (Set.range ⇑D.row)ᶜ := by
    rintro i ⟨i', hi'⟩
    exact hj₁ (Prod.ext_iff.mp (π.injective hi')).2.symm
  have hinj : Function.Injective
      (fun i : Idx μ => (⟨π (i, j₁), hmem i⟩ : ↥(Set.range ⇑D.row)ᶜ)) := by
    intro a b hab
    exact (Prod.ext_iff.mp (π.injective (congrArg Subtype.val hab))).1
  exact le_antisymm ((Cardinal.mk_set_le _).trans_eq (mk_Idx μ))
    ((mk_Idx μ).symm.trans_le (Cardinal.mk_le_of_injective hinj))

/-- Composing with `row` forces the complement of the range to have full cardinality. -/
theorem mk_compl_trans {ι : Type u} (e : ι ↪ Idx μ) :
    #(↥(Set.range ⇑(e.trans D.row))ᶜ) = μ := by
  have hsub : (Set.range ⇑D.row)ᶜ ⊆ (Set.range ⇑(e.trans D.row))ᶜ := by
    apply Set.compl_subset_compl.mpr
    rintro k ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  exact le_antisymm ((Cardinal.mk_set_le _).trans_eq (mk_Idx μ))
    (D.mk_compl_row.symm.trans_le (Cardinal.mk_le_mk_of_subset hsub))

/-- Zero-padded sums do not depend on the embedding, as long as both ranges have complements of
the same size: the two paddings differ by a permutation. -/
theorem tot_extend_congr {ι : Type u} (h : #ι < lam) (e₁ e₂ : ι ↪ Idx μ)
    (hc : #(↥(Set.range ⇑e₁)ᶜ) = #(↥(Set.range ⇑e₂)ᶜ)) (x : ι → H) :
    D.tot (extend e₁ x 0) = D.tot (extend e₂ x 0) := by
  obtain ⟨σ, hσ⟩ := exists_perm_comp e₁ e₂ hc
  have hfun : extend e₂ x 0 = (extend e₁ x 0) ∘ σ.symm := by
    funext k
    by_cases hk : ∃ i, e₂ i = k
    · obtain ⟨i, rfl⟩ := hk
      show extend e₂ x 0 (e₂ i) = extend e₁ x 0 (σ.symm (e₂ i))
      rw [e₂.injective.extend_apply, ← hσ i, Equiv.symm_apply_apply, e₁.injective.extend_apply]
    · have hnot : ¬ ∃ i, e₁ i = σ.symm k := by
        rintro ⟨i, hi⟩
        exact hk ⟨i, by rw [← hσ i, hi, Equiv.apply_symm_apply]⟩
      show extend e₂ x 0 k = extend e₁ x 0 (σ.symm k)
      rw [extend_apply' _ _ _ hk, extend_apply' _ _ _ hnot]
      rfl
  rw [hfun]
  exact D.tot_perm (small_extend h e₁ x) σ.symm

/-- The sum of a family indexed by an arbitrary type of cardinality `< λ`: pad it with zeros
along an embedding into `Idx μ` whose range has a large complement. -/
noncomputable def lsum {ι : Type u} (h : #ι < lam) (x : ι → H) : H :=
  D.tot (extend ((emb (D.le_of_lt h)).trans D.row) x 0)

/-- `lsum` may be computed by padding along *any* embedding into `Idx μ`. -/
theorem tot_extend_eq {ι : Type u} (h : #ι < lam) (e : ι ↪ Idx μ) (x : ι → H) :
    D.tot (extend e x 0) = D.lsum h x := by
  have hrow : extend (e.trans D.row) x 0 = extend D.row (extend e x 0) 0 := by
    have hraw := Injective.extend_comp e.injective D.row.injective x (0 : Idx μ → H)
    have h0 : (0 : Idx μ → H) ∘ (⇑D.row) = (0 : Idx μ → H) := rfl
    rw [h0] at hraw
    exact hraw
  have h1 : D.tot (extend (e.trans D.row) x 0) = D.tot (extend e x 0) := by
    rw [hrow]; exact D.tot_row (small_extend h e x)
  exact h1.symm.trans (D.tot_extend_congr h (e.trans D.row) ((emb (D.le_of_lt h)).trans D.row)
    ((D.mk_compl_trans e).trans (D.mk_compl_trans _).symm) x)

/-- (B1) for `lsum`. -/
theorem lsum_unique {ι : Type u} [Unique ι] (h : #ι < lam) (x : ι → H) :
    D.lsum h x = x default := by
  set e : ι ↪ Idx μ := ⟨fun _ => D.i₀, fun a b _ => Subsingleton.elim a b⟩
  rw [← D.tot_extend_eq h e x,
    D.tot_single (extend e x 0) fun i hi =>
      extend_apply' _ _ _ (by rintro ⟨j, rfl⟩; exact hi rfl)]
  exact e.injective.extend_apply x 0 default

/-- Reindexing for `lsum`: pad along the embedding composed with the equivalence. -/
theorem lsum_congr {ι ι' : Type u} (h : #ι < lam) (h' : #ι' < lam) (e : ι ≃ ι') (x : ι' → H) :
    D.lsum h (x ∘ e) = D.lsum h' x := by
  set E' : ι' ↪ Idx μ := emb (D.le_of_lt h')
  have hE : extend (e.toEmbedding.trans E') (x ∘ e) 0 = extend E' x 0 := by
    funext k
    by_cases hk : ∃ i', E' i' = k
    · obtain ⟨i', rfl⟩ := hk
      have hval : (e.toEmbedding.trans E') (e.symm i') = E' i' := by
        show E' (e (e.symm i')) = _
        rw [Equiv.apply_symm_apply]
      rw [E'.injective.extend_apply, ← hval, (e.toEmbedding.trans E').injective.extend_apply]
      show x (e (e.symm i')) = x i'
      rw [Equiv.apply_symm_apply]
    · have hnot : ¬ ∃ i, (e.toEmbedding.trans E') i = k := by
        rintro ⟨i, hi⟩
        exact hk ⟨e i, hi⟩
      rw [extend_apply' _ _ _ hnot, extend_apply' _ _ _ hk]
  rw [← D.tot_extend_eq h (e.toEmbedding.trans E') (x ∘ e), hE]
  exact D.tot_extend_eq h' E' x

/-- (B2) for `lsum`.  Pad the rows along `e`, each row along `f i`, and read the padded double
family through `μ × μ ≃ μ`: it is the sigma family padded along `(i, r) ↦ (e i, f i r)`, and it
has fewer than `λ` nonzero rows (inside the range of `e`) and columns (inside the ranges of the
`f i`). -/
theorem lsum_sigma {ι : Type u} {ρ : ι → Type u} (h : #ι < lam) (hρ : ∀ i, #(ρ i) < lam)
    (x : ∀ i, ρ i → H) (hσ : #((i : ι) × ρ i) < lam) :
    D.lsum h (fun i => D.lsum (hρ i) (x i)) = D.lsum hσ (fun p => x p.1 p.2) := by
  set e : ι ↪ Idx μ := emb (D.le_of_lt h) with hedef
  set f : ∀ i, ρ i ↪ Idx μ := fun i => emb (D.le_of_lt (hρ i)) with hfdef
  set π : Idx μ × Idx μ ≃ Idx μ := pairEquiv D.aleph0_le with hπdef
  set E : ((i : ι) × ρ i) ↪ Idx μ := ⟨fun p => π (e p.1, f p.1 p.2), by
    rintro ⟨i1, r1⟩ ⟨i2, r2⟩ hEq
    have hpair : (e i1, f i1 r1) = (e i2, f i2 r2) := π.injective hEq
    have hi : i1 = i2 := e.injective (Prod.ext_iff.mp hpair).1
    subst hi
    exact congrArg _ ((f i1).injective (Prod.ext_iff.mp hpair).2)⟩ with hEdef
  set W : ∀ _ : ι, Idx μ → H := fun i => extend (f i) (x i) 0 with hWdef
  set G : Idx μ → (Idx μ → H) := extend e W (fun _ => (0 : Idx μ → H)) with hGdef
  have hGout : ∀ a, (¬ ∃ i, e i = a) → G a = fun _ => 0 := fun a ha => by
    rw [hGdef]
    exact extend_apply' W (fun _ => (0 : Idx μ → H)) a ha
  have hGa : ∀ a, D.tot (G a) = extend e (fun i => D.tot (W i)) 0 a := by
    intro a
    by_cases ha : ∃ i, e i = a
    · obtain ⟨i, rfl⟩ := ha
      rw [hGdef, e.injective.extend_apply, e.injective.extend_apply]
    · rw [hGout a ha, extend_apply' (fun i => D.tot (W i)) (0 : Idx μ → H) a ha]
      exact D.tot_zero
  have hGk : ∀ k, G (π.symm k).1 (π.symm k).2 = extend E (fun p => x p.1 p.2) 0 k := by
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
      · show extend (f i) (x i) 0 (π.symm k).2 = _
        rw [extend_apply' (x i) (0 : Idx μ → H) (π.symm k).2 hb]
        symm
        apply extend_apply'
        rintro ⟨⟨i', r'⟩, hp⟩
        have heqp : (e i', f i' r') = π.symm k := by
          rw [← hp]; exact (π.symm_apply_apply (e i', f i' r')).symm
        have hii : i' = i := e.injective ((congrArg Prod.fst heqp).trans hi.symm)
        subst hii
        exact hb ⟨r', congrArg Prod.snd heqp⟩
    · rw [hGout _ ha]
      symm
      apply extend_apply'
      rintro ⟨⟨i', r'⟩, hp⟩
      have heqp : (e i', f i' r') = π.symm k := by
        rw [← hp]; exact (π.symm_apply_apply (e i', f i' r')).symm
      exact ha ⟨i', congrArg Prod.fst heqp⟩
  have hrows : #{a | ∃ b, G a b ≠ 0} < lam := by
    refine mk_lt_of_subset' (T := range e) (fun a ⟨b, hb⟩ => by_contra fun ha => hb ?_)
      (Cardinal.mk_range_le.trans_lt h)
    rw [hGout a fun ⟨i, hi⟩ => ha ⟨i, hi⟩]
  have hcols : #{b | ∃ a, G a b ≠ 0} < lam := by
    refine mk_lt_of_subset' (T := range fun p : (i : ι) × ρ i => f p.1 p.2)
      (fun b ⟨a, hab⟩ => ?_) (Cardinal.mk_range_le.trans_lt hσ)
    by_cases ha : ∃ i, e i = a
    · obtain ⟨i, rfl⟩ := ha
      rw [hGdef, e.injective.extend_apply] at hab
      by_contra hb
      exact hab (extend_apply' (x i) (0 : Idx μ → H) b fun ⟨r, hr⟩ => hb ⟨⟨i, r⟩, hr⟩)
    · exact absurd (by rw [hGout a ha]) hab
  calc D.lsum h (fun i => D.lsum (hρ i) (x i))
      = D.tot (extend e (fun i => D.tot (W i)) 0) := by
        rw [← D.tot_extend_eq h e]
        congr 1; funext a
        by_cases ha : ∃ i, e i = a
        · obtain ⟨i, rfl⟩ := ha
          rw [e.injective.extend_apply, e.injective.extend_apply, D.tot_extend_eq (hρ i)]
        · rw [extend_apply' _ _ _ ha, extend_apply' _ _ _ ha]
    _ = D.tot (fun a => D.tot (G a)) := by congr 1; funext a; exact (hGa a).symm
    _ = D.tot (fun k => G (π.symm k).1 (π.symm k).2) := D.tot_sigma G hrows hcols π
    _ = D.tot (extend E (fun p => x p.1 p.2) 0) := by congr 1; funext k; exact hGk k
    _ = D.lsum hσ (fun p => x p.1 p.2) := D.tot_extend_eq hσ E _

/-- The summation data on arbitrary index types of size `< λ`. -/
noncomputable def sumData : SumData lam H where
  isRegular := D.isRegular
  sum := D.lsum
  sum_congr := D.lsum_congr
  sum_unique := D.lsum_unique
  sum_sigma := D.lsum_sigma

/-- The empty sum is `0`. -/
theorem sumData_zero : D.sumData.zero = 0 := by
  show D.lsum (D.sumData.small PEmpty.{u + 1}) (PEmpty.elim : PEmpty.{u + 1} → H) = 0
  rw [← D.tot_extend_eq (D.sumData.small _) ⟨PEmpty.elim, fun a => a.elim⟩]
  have heq : extend (⟨PEmpty.elim, fun a => a.elim⟩ : PEmpty.{u + 1} ↪ Idx μ)
      (PEmpty.elim : PEmpty.{u + 1} → H) (0 : Idx μ → H) = fun _ => 0 := by
    funext k
    exact extend_apply' _ _ _ (by rintro ⟨p, _⟩; exact p.elim)
  rw [heq]
  exact D.tot_zero

/-- The `λ⁻`-monoid determined by the data (Lemma 2.5): the sums are the zero-padded ones and
`0` is the given one. -/
@[instance_reducible]
noncomputable def toLMonoid : LMonoid lam H := D.sumData.toLMonoidOfZero D.sumData_zero

end IdxSumData

end KappaMonoid
