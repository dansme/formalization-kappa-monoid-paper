/-
**Definition 2.18 verbatim.**  `PaperLMonoid` transcribes the paper's definition of a
`λ⁻`-monoid literally - a `Zero`, a map `Σ : H^(λ) → H` on the `λ`-indexed families of support
`< λ`, (B1) at one distinguished index, (B2) for families with fewer than `λ` nonzero rows and
columns and every bijection `λ × λ ≃ λ` - and `toLMonoid` / `LMonoid.toPaper` show that it agrees
with the `LMonoid` the development uses.  Nothing else depends on this file; it exists so that the
working definition can be checked against the paper's, as `Paper/Definition21.lean` does for
Definition 2.1.
-/
import KappaMonoid.Core.Bare
import KappaMonoid.Core.Compatible

universe u v

open Cardinal Function Set

namespace KappaMonoid

/-! ## Definition 2.18 verbatim

`LMonoid` deviates from Definition 2.18 in the same three ways as `KMonoid` does from
Definition 2.1 (sums over arbitrary index types of size `< λ` rather than over `λ`-indexed
families of support `< λ`; (B1) as the one-point law; the commutative monoid carried along), see
`Paper/Definition21.lean`.  The one feature special to Definition 2.18 is that `Σ` is *partial*:
it is only defined on `H^(λ)`, the families `λ → H` whose support has cardinality `< λ`. -/

/-- A subset of a set of size `< λ` has size `< λ`. -/
theorem mk_lt_of_subset' {α : Type u} {lam : Cardinal.{u}} {S T : Set α} (h : S ⊆ T)
    (hT : #T < lam) : #S < lam :=
  (Cardinal.mk_le_mk_of_subset h).trans_lt hT

/-- **Definition 2.18**, verbatim: for a regular cardinal `λ`, a set `H` with an element `0` and
a map `Σ : H^(λ) → H`, where `H^(λ)` is the set of families `λ → H` of support `< λ`, such that

* (B1) if `x ∈ H^(λ)` has `x i = 0` for all `i ≠ 0`, then `Σ x = x 0`;
* (B2) if `x ∈ H^{λ×λ}` has fewer than `λ` rows containing a nonzero entry and fewer than `λ`
  columns containing a nonzero entry, and `π : λ × λ → λ` is a bijection, then
  `Σᵢ Σⱼ x i j = Σₖ x (π⁻¹ k)`.

`Σ` takes the family together with a proof that it lies in `H^(λ)`.  In (B2) the three families
that are summed - the rows `x i`, the family of row sums, and `x ∘ π⁻¹` - lie in `H^(λ)` because
of the two hypotheses on `x` (and, for the row sums, because a zero row sums to `0` by (B1)); the
paper leaves this implicit, here the three memberships are universally quantified arguments
`hin`, `hout`, `hπ`.  Since `Σ` is irrelevant in its proof argument this adds no assumption.

The distinguished element `0 ∈ λ` is an arbitrary index `i₀ : Idx λ`, and (B1) is assumed at `i₀`
only, exactly as in the paper. -/
structure PaperLMonoid (lam : Cardinal.{u}) (H : Type v) [Zero H] where
  /-- `λ` is a regular cardinal. -/
  isRegular : lam.IsRegular
  /-- The distinguished index, playing the role of `0 ∈ λ`. -/
  i₀ : Idx lam
  /-- The summation `Σ : H^(λ) → H`. -/
  sigma : ∀ x : Idx lam → H, #(support x) < lam → H
  /-- (B1), at the distinguished index. -/
  B1 : ∀ (x : Idx lam → H) (hx : #(support x) < lam), (∀ i, i ≠ i₀ → x i = 0) → sigma x hx = x i₀
  /-- (B2). -/
  B2 : ∀ (x : Idx lam → Idx lam → H), #{i | ∃ j, x i j ≠ 0} < lam → #{j | ∃ i, x i j ≠ 0} < lam →
      ∀ (π : Idx lam × Idx lam ≃ Idx lam) (hin : ∀ i, #(support (x i)) < lam)
        (hout : #(support fun i => sigma (x i) (hin i)) < lam)
        (hπ : #(support fun k => x (π.symm k).1 (π.symm k).2) < lam),
        sigma (fun i => sigma (x i) (hin i)) hout = sigma (fun k => x (π.symm k).1 (π.symm k).2) hπ

namespace PaperLMonoid

variable {lam : Cardinal.{u}} {H : Type v} [Zero H] (P : PaperLMonoid lam H)

include P in
theorem aleph0_le : ℵ₀ ≤ lam := P.isRegular.aleph0_le

include P in
theorem mk_singleton_lt (a : Idx lam) : #(↥({a} : Set (Idx lam))) < lam := by
  rw [Cardinal.mk_singleton]
  exact Cardinal.one_lt_aleph0.trans_le P.aleph0_le

/-- `Σ` does not depend on the proof of membership in `H^(λ)`. -/
theorem sigma_congr {x y : Idx lam → H} (hxy : x = y) (hx : #(support x) < lam)
    (hy : #(support y) < lam) : P.sigma x hx = P.sigma y hy := by
  subst hxy
  rfl

open Classical in
/-- `Σ` extended by `0` to all of `H^λ`; this only removes the proof arguments. -/
noncomputable def tot (x : Idx lam → H) : H :=
  if h : #(support x) < lam then P.sigma x h else 0

theorem tot_eq {x : Idx lam → H} (h : #(support x) < lam) : P.tot x = P.sigma x h := dif_pos h

theorem tot_single {x : Idx lam → H} (hx : ∀ i, i ≠ P.i₀ → x i = 0) : P.tot x = x P.i₀ := by
  have hs : #(support x) < lam :=
    mk_lt_of_subset' (T := {P.i₀}) (fun i hi => by_contra fun h => hi (hx i h))
      (P.mk_singleton_lt _)
  exact (P.tot_eq hs).trans (P.B1 x hs hx)

theorem tot_zero : P.tot (fun _ => 0) = 0 := P.tot_single fun _ _ => rfl

/-- (B2) for `tot`: only the hypotheses on rows and columns remain. -/
theorem tot_B2 (x : Idx lam → Idx lam → H) (hrows : #{i | ∃ j, x i j ≠ 0} < lam)
    (hcols : #{j | ∃ i, x i j ≠ 0} < lam) (π : Idx lam × Idx lam ≃ Idx lam) :
    P.tot (fun i => P.tot (x i)) = P.tot (fun k => x (π.symm k).1 (π.symm k).2) := by
  have hin : ∀ i, #(support (x i)) < lam := fun i =>
    mk_lt_of_subset' (T := {j | ∃ i, x i j ≠ 0}) (fun j hj => ⟨i, hj⟩) hcols
  have hinner : (fun i => P.tot (x i)) = fun i => P.sigma (x i) (hin i) :=
    funext fun i => P.tot_eq (hin i)
  have hout : #(support fun i => P.sigma (x i) (hin i)) < lam := by
    refine mk_lt_of_subset' (fun i hi => by_contra fun hni => hi ?_) hrows
    have h0 : x i = fun _ => 0 := funext fun j => by_contra fun hj => hni ⟨j, hj⟩
    show P.sigma (x i) (hin i) = 0
    rw [← P.tot_eq (hin i), h0, P.tot_zero]
  have hπ : #(support fun k => x (π.symm k).1 (π.symm k).2) < lam := by
    refine mk_lt_of_subset'
      (T := range fun p : ↥{i | ∃ j, x i j ≠ 0} × ↥{j | ∃ i, x i j ≠ 0} => π (p.1.1, p.2.1))
      (fun k hk => ⟨(⟨(π.symm k).1, (π.symm k).2, hk⟩, ⟨(π.symm k).2, (π.symm k).1, hk⟩), ?_⟩)
      (Cardinal.mk_range_le.trans_lt (mk_prod_lt P.isRegular hrows hcols))
    simp
  rw [hinner, P.tot_eq hout, P.tot_eq hπ]
  exact P.B2 x hrows hcols π hin hout hπ

/-- (A3) for `λ⁻`-monoids: `Σ` is invariant under permutations of `λ`.

Paper proof (as for Lemma 2.5): spread `x` out as `y i j := if j = 0 then x i else 0`, so that
`Σⱼ y i j = x i` by (B1), and apply (B2) once with `f ∘ (σ⁻¹, id)` and once with `f`, for a
bijection `f : λ × λ ≃ λ`.  The family `y` has fewer than `λ` nonzero rows because `x ∈ H^(λ)`,
and a single nonzero column. -/
theorem tot_perm {x : Idx lam → H} (hx : #(support x) < lam) (σ : Idx lam ≃ Idx lam) :
    P.tot x = P.tot (x ∘ σ) := by
  classical
  set y : Idx lam → Idx lam → H := fun i j => if j = P.i₀ then x i else 0 with hy
  set w : Idx lam → Idx lam → H := fun i j => y (σ i) j with hw
  have hxy : ∀ i, P.tot (y i) = x i := fun i =>
    (P.tot_single fun j hj => if_neg hj).trans (if_pos rfl)
  have hyrows : #{i | ∃ j, y i j ≠ 0} < lam := by
    refine mk_lt_of_subset' (T := support x) (fun i ⟨j, hj⟩ => ?_) hx
    by_cases hj0 : j = P.i₀
    · intro hxi
      exact hj (by simp only [hy, if_pos hj0]; exact hxi)
    · exact absurd (if_neg hj0) hj
  have hycols : #{j | ∃ i, y i j ≠ 0} < lam :=
    mk_lt_of_subset' (T := {P.i₀}) (fun j ⟨_, hi⟩ => by_contra fun hj0 => hi (if_neg hj0))
      (P.mk_singleton_lt _)
  have hwrows : #{i | ∃ j, w i j ≠ 0} < lam :=
    (Cardinal.mk_le_of_injective
      (f := fun i : ↥{i | ∃ j, w i j ≠ 0} => (⟨σ i, i.2⟩ : ↥{i | ∃ j, y i j ≠ 0}))
      fun a b h => Subtype.ext (σ.injective (congrArg Subtype.val h))).trans_lt hyrows
  have hwcols : #{j | ∃ i, w i j ≠ 0} < lam :=
    mk_lt_of_subset' (T := {j | ∃ i, y i j ≠ 0}) (fun j ⟨i, hi⟩ => ⟨σ i, hi⟩) hycols
  set f := pairEquiv P.aleph0_le with hf
  set g : Idx lam × Idx lam ≃ Idx lam := (σ.symm.prodCongr (Equiv.refl (Idx lam))).trans f with hg
  have hgsymm : ∀ l : Idx lam, g.symm l = (σ (f.symm l).1, (f.symm l).2) := by
    intro l
    apply Prod.ext <;>
      simp [hg, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  have hstep : (fun l => y (g.symm l).1 (g.symm l).2) = fun l => w (f.symm l).1 (f.symm l).2 := by
    funext l
    rw [hgsymm l]
  calc P.tot x = P.tot (fun i => P.tot (y i)) := by congr 1; funext i; exact (hxy i).symm
    _ = P.tot (fun l => y (g.symm l).1 (g.symm l).2) := P.tot_B2 y hyrows hycols g
    _ = P.tot (fun l => w (f.symm l).1 (f.symm l).2) := congrArg _ hstep
    _ = P.tot (fun i => P.tot (w i)) := (P.tot_B2 w hwrows hwcols f).symm
    _ = P.tot (x ∘ σ) := by congr 1; funext i; exact hxy (σ i)

theorem small_extend {ι : Type u} (h : #ι < lam) (e : ι ↪ Idx lam) (x : ι → H) :
    #(support (extend e x 0)) < lam :=
  mk_lt_of_subset' (T := range e)
    (fun _ hk => by_contra fun hk' => hk (extend_apply' _ _ _ fun ⟨i, hi⟩ => hk' ⟨i, hi⟩))
    (Cardinal.mk_range_le.trans_lt h)

/-- Zero-padded sums do not depend on the embedding. -/
theorem tot_extend_congr {ι : Type u} (h : #ι < lam) (e₁ e₂ : ι ↪ Idx lam) (x : ι → H) :
    P.tot (extend e₁ x 0) = P.tot (extend e₂ x 0) := by
  have := infinite_Idx P.aleph0_le
  have hc : ∀ e : ι ↪ Idx lam, #(↥(Set.range ⇑e)ᶜ) = lam := fun e => by
    rw [Cardinal.mk_compl_of_infinite _
      (Cardinal.mk_range_le.trans_lt (h.trans_eq (mk_Idx lam).symm)), mk_Idx]
  obtain ⟨σ, hσ⟩ := exists_perm_comp e₁ e₂ ((hc e₁).trans (hc e₂).symm)
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
  exact P.tot_perm (small_extend h e₁ x) σ.symm

/-- The sum of a family indexed by an arbitrary type of cardinality `< λ`: pad it with zeros
along an embedding into `λ`. -/
noncomputable def lsum {ι : Type u} (h : #ι < lam) (x : ι → H) : H :=
  P.tot (extend (emb h.le) x 0)

theorem tot_extend_eq {ι : Type u} (h : #ι < lam) (e : ι ↪ Idx lam) (x : ι → H) :
    P.tot (extend e x 0) = P.lsum h x :=
  P.tot_extend_congr h e (emb h.le) x

theorem lsum_unique {ι : Type u} [Unique ι] (h : #ι < lam) (x : ι → H) :
    P.lsum h x = x default := by
  set e : ι ↪ Idx lam := ⟨fun _ => P.i₀, fun a b _ => Subsingleton.elim a b⟩ with he
  rw [← P.tot_extend_eq h e x,
    P.tot_single (x := extend e x 0) fun i hi =>
      extend_apply' _ _ _ (by rintro ⟨j, rfl⟩; exact hi rfl)]
  exact e.injective.extend_apply x 0 default

theorem lsum_congr {ι ι' : Type u} (h : #ι < lam) (h' : #ι' < lam) (e : ι ≃ ι') (x : ι' → H) :
    P.lsum h (x ∘ e) = P.lsum h' x := by
  set E' : ι' ↪ Idx lam := emb h'.le
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
  rw [← P.tot_extend_eq h (e.toEmbedding.trans E') (x ∘ e), hE]
  exact P.tot_extend_eq h' E' x

theorem lsum_sigma {ι : Type u} {ρ : ι → Type u} (h : #ι < lam) (hρ : ∀ i, #(ρ i) < lam)
    (x : ∀ i, ρ i → H) (hσ : #((i : ι) × ρ i) < lam) :
    P.lsum h (fun i => P.lsum (hρ i) (x i)) = P.lsum hσ (fun p => x p.1 p.2) := by
  set e : ι ↪ Idx lam := emb h.le with hedef
  set f : ∀ i, ρ i ↪ Idx lam := fun i => emb (hρ i).le with hfdef
  set π : Idx lam × Idx lam ≃ Idx lam := pairEquiv P.aleph0_le with hπdef
  set E : ((i : ι) × ρ i) ↪ Idx lam := ⟨fun p => π (e p.1, f p.1 p.2), by
    rintro ⟨i1, r1⟩ ⟨i2, r2⟩ hEq
    have hpair : (e i1, f i1 r1) = (e i2, f i2 r2) := π.injective hEq
    have hi : i1 = i2 := e.injective (Prod.ext_iff.mp hpair).1
    subst hi
    exact congrArg _ ((f i1).injective (Prod.ext_iff.mp hpair).2)⟩ with hEdef
  set W : ∀ _ : ι, Idx lam → H := fun i => extend (f i) (x i) 0 with hWdef
  set G : Idx lam → (Idx lam → H) := extend e W (fun _ => (0 : Idx lam → H)) with hGdef
  have hGout : ∀ a, (¬ ∃ i, e i = a) → G a = fun _ => 0 := fun a ha => by
    rw [hGdef]
    exact extend_apply' W (fun _ => (0 : Idx lam → H)) a ha
  have hGa : ∀ a, P.tot (G a) = extend e (fun i => P.tot (W i)) 0 a := by
    intro a
    by_cases ha : ∃ i, e i = a
    · obtain ⟨i, rfl⟩ := ha
      rw [hGdef, e.injective.extend_apply, e.injective.extend_apply]
    · rw [hGout a ha, extend_apply' (fun i => P.tot (W i)) (0 : Idx lam → H) a ha]
      exact P.tot_zero
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
        rw [extend_apply' (x i) (0 : Idx lam → H) (π.symm k).2 hb]
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
      exact hab (extend_apply' (x i) (0 : Idx lam → H) b fun ⟨r, hr⟩ => hb ⟨⟨i, r⟩, hr⟩)
    · exact absurd (by rw [hGout a ha]) hab
  calc P.lsum h (fun i => P.lsum (hρ i) (x i))
      = P.tot (fun a => P.tot (G a)) := by
        show P.tot (extend e (fun i => P.tot (W i)) 0) = _
        congr 1
        funext a
        exact (hGa a).symm
    _ = P.tot (fun k => G (π.symm k).1 (π.symm k).2) := P.tot_B2 G hrows hcols π
    _ = P.tot (extend E (fun p => x p.1 p.2) 0) := by
        congr 1; funext k; exact hGk k
    _ = P.lsum hσ (fun p => x p.1 p.2) := P.tot_extend_eq hσ E _

/-- The summation data underlying the paper's definition. -/
noncomputable def sumData : SumData lam H where
  isRegular := P.isRegular
  sum := P.lsum
  sum_congr := P.lsum_congr
  sum_unique := P.lsum_unique
  sum_sigma := P.lsum_sigma

theorem sumData_zero : P.sumData.zero = 0 := by
  show P.tot (extend (emb _) (PEmpty.elim : PEmpty.{u + 1} → H) 0) = 0
  have heq : extend (emb (P.sumData.small PEmpty.{u + 1}).le) (PEmpty.elim : PEmpty.{u + 1} → H)
      (0 : Idx lam → H) = fun _ => 0 := by
    funext k
    exact extend_apply' _ _ _ (by rintro ⟨p, _⟩; exact p.elim)
  rw [heq]
  exact P.tot_zero

/-- **Every `λ⁻`-monoid in the sense of the paper is one in the sense of `LMonoid`.** -/
@[instance_reducible]
noncomputable def toLMonoid : LMonoid lam H := P.sumData.toLMonoidOfZero P.sumData_zero

/-- The reconstructed sums are zero-padded `Σ`'s, along any embedding into `λ`. -/
theorem toLMonoid_lsumOf {ι : Type u} (h : #ι < lam) (e : ι ↪ Idx lam) (x : ι → H) :
    letI := P.toLMonoid
    LMonoid.lsumOf (lam := lam) h x = P.sigma (extend e x 0) (small_extend h e x) := by
  let := P.toLMonoid
  exact (P.tot_extend_eq h e x).symm.trans (P.tot_eq _)

end PaperLMonoid

/-! ## Every `LMonoid` is a `λ⁻`-monoid in the sense of the paper -/

namespace LMonoid

variable {lam : Cardinal.{u}} {H : Type v} [LMonoid lam H]

/-- (B1) for the sum over the support. -/
theorem paper_B1 (a : Idx lam) (x : Idx lam → H) (hx : #(support x) < lam)
    (h1 : ∀ i, i ≠ a → x i = 0) : lsumOf hx (fun i : support x => x i) = x a := by
  have hsub : support x ⊆ {a} := fun i hi => by_contra fun h => hi (h1 i h)
  have hsing : #(↥({a} : Set (Idx lam))) < lam := by
    rw [Cardinal.mk_singleton]
    exact Cardinal.one_lt_aleph0.trans_le (aleph0_le (lam := lam) (X := H))
  rw [← lsumOf_of_subset (hS := ⟨hsing⟩) (hT := ⟨hx⟩) hsub x
    fun i _ hi => Function.notMem_support.mp hi]
  exact lsumOf_unique hsing _

/-- (B2) for the sum over the support. -/
theorem paper_B2 (x : Idx lam → Idx lam → H) (hrows : #{i | ∃ j, x i j ≠ 0} < lam)
    (hcols : #{j | ∃ i, x i j ≠ 0} < lam) (π : Idx lam × Idx lam ≃ Idx lam)
    (hin : ∀ i, #(support (x i)) < lam)
    (hout : #(support fun i => lsumOf (hin i) fun j : support (x i) => x i j) < lam)
    (hπ : #(support fun k => x (π.symm k).1 (π.symm k).2) < lam) :
    lsumOf hout (fun i : support (fun i => lsumOf (hin i) fun j : support (x i) => x i j) =>
        lsumOf (hin i) fun j : support (x i) => x i j)
      = lsumOf hπ (fun k : support (fun k => x (π.symm k).1 (π.symm k).2) =>
          x (π.symm k).1 (π.symm k).2) := by
  have hreg := isRegular' (lam := lam) (X := H)
  set R : Set (Idx lam) := {i | ∃ j, x i j ≠ 0} with hR
  set C : Set (Idx lam) := {j | ∃ i, x i j ≠ 0} with hC
  set F : Idx lam → H := fun i => lsumOf (hin i) fun j : support (x i) => x i j with hFdef
  have hF : ∀ i, F i = lsumOf hcols (fun j : C => x i j) := fun i =>
    (lsumOf_of_subset (hS := ⟨hcols⟩) (hT := ⟨hin i⟩) (fun j hj => ⟨i, hj⟩) (x i)
      fun j _ hj => Function.notMem_support.mp hj).symm
  have hsuppF : support F ⊆ R := fun i hi => by
    by_contra hni
    apply hi
    rw [hF i]
    exact lsumOf_eq_zero (hT := ⟨hcols⟩) (x i) fun j _ => by_contra fun hj => hni ⟨j, hj⟩
  have hprod : #(R × C) < lam := mk_prod_lt hreg hrows hcols
  have hsig : #((_ : R) × C) < lam := mk_sigma_lt hreg hrows fun _ => hcols
  set G : Idx lam → H := fun k => x (π.symm k).1 (π.symm k).2 with hGdef
  set φ : R × C → Idx lam := fun p => π (p.1, p.2) with hφdef
  have hφ : Function.Injective φ := fun p q hpq => by
    have h := π.injective hpq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hT : #(range φ) < lam := Cardinal.mk_range_le.trans_lt hprod
  have hsuppG : support G ⊆ range φ := fun k hk =>
    ⟨(⟨(π.symm k).1, (π.symm k).2, hk⟩, ⟨(π.symm k).2, (π.symm k).1, hk⟩), by simp [hφdef]⟩
  calc lsumOf hout (fun i : support F => F i)
      = lsumOf hrows (fun i : R => F i) :=
        (lsumOf_of_subset (hS := ⟨hrows⟩) (hT := ⟨hout⟩) hsuppF F fun i _ hi =>
            Function.notMem_support.mp hi).symm
    _ = lsumOf hrows (fun i : R => lsumOf hcols (fun j : C => x i j)) := by
        congr 1; funext i; exact hF i
    _ = lsumOf hsig (fun p : (_ : R) × C => x p.1 p.2) :=
        lsumOf_sigma hrows (fun _ => hcols) (fun (i : R) (j : C) => x i j) hsig
    _ = lsumOf hprod (fun p : R × C => x p.1 p.2) :=
        lsumOf_equiv (h := ⟨hsig⟩) (h' := ⟨hprod⟩) (Equiv.sigmaEquivProd R C).symm _
    _ = lsumOf hprod ((fun k : range φ => G k) ∘ Equiv.ofInjective φ hφ) := by
        congr 1; funext p; simp [hGdef, hφdef]
    _ = lsumOf hT (fun k : range φ => G k) := by
        rw [lsumOf_equiv (h := ⟨hT⟩) (h' := ⟨hprod⟩) (Equiv.ofInjective φ hφ)]
        rfl
    _ = lsumOf hπ (fun k : support G => G k) :=
        lsumOf_of_subset (hS := ⟨hT⟩) (hT := ⟨hπ⟩) hsuppG G fun k _ hk =>
            Function.notMem_support.mp hk

/-- **Conversely, every `LMonoid` is a `λ⁻`-monoid in the sense of the paper**: `Σ` sums a
family of `H^(λ)` over its support.  Any index may be taken as the distinguished one. -/
noncomputable def toPaper (lam : Cardinal.{u}) (H : Type v) [LMonoid lam H] :
    PaperLMonoid lam H where
  isRegular := isRegular' (lam := lam) (X := H)
  i₀ := (nonempty_Idx (aleph0_le (lam := lam) (X := H))).some
  sigma := fun x hx => lsumOf hx (fun i : support x => x i)
  B1 := fun x hx h1 => paper_B1 _ x hx h1
  B2 := fun x hrows hcols π hin hout hπ => paper_B2 x hrows hcols π hin hout hπ

@[simp] theorem toPaper_sigma (x : Idx lam → H) (hx : #(support x) < lam) :
    (toPaper lam H).sigma x hx = lsumOf hx (fun i : support x => x i) := rfl

/-- The round trip `toPaper` then `toLMonoid` gives back the same `λ⁻`-monoid: not only the same
sums, but the same structure. -/
theorem toPaper_toLMonoid (lam : Cardinal.{u}) (H : Type v) [M : LMonoid lam H] :
    (toPaper lam H).toLMonoid = M := by
  have hsupp : ∀ {ι : Type u} (h : #ι < lam) (e : ι ↪ Idx lam) (x : ι → H)
      (hS : #(support (extend e x 0)) < lam),
      lsumOf hS (fun i : support (extend e x 0) => extend e x 0 i) = lsumOf h x := by
    intro ι h e x hS
    have hR : #(range e) < lam := Cardinal.mk_range_le.trans_lt h
    rw [← lsumOf_of_subset (hS := ⟨hR⟩) (hT := ⟨hS⟩)
      (fun k hk => by_contra fun hk' => hk (extend_apply' _ _ _ fun ⟨i, hi⟩ => hk' ⟨i, hi⟩))
      (extend e x 0) fun k _ hk => Function.notMem_support.mp hk,
      lsumOf_equiv (h := ⟨hR⟩) (h' := ⟨h⟩) (Equiv.ofInjective e e.injective) _]
    congr 1
    funext i
    exact e.injective.extend_apply x 0 i
  have hsum : ∀ {ι : Type u} (h : #ι < lam) (x : ι → H),
      (toPaper lam H).lsum h x = lsumOf h x := by
    intro ι h x
    show (toPaper lam H).tot (extend (emb h.le) x 0) = _
    rw [(toPaper lam H).tot_eq (PaperLMonoid.small_extend h (emb h.le) x)]
    exact hsupp h (emb h.le) x _
  refine LMonoid.ext_of_lsumOf ?_ (fun h x => hsum h x)
  funext a b
  have hPP : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) < lam :=
    mk_sum_lt (isRegular' (X := H)) (mk_lt_finite (X := H) _) (mk_lt_finite (X := H) _)
  show (toPaper lam H).sumData.add a b = a + b
  exact (hsum hPP _).trans (LMonoid.add_eq_lsumOf hPP a b).symm

end LMonoid

/-- The round trip `toLMonoid` then `toPaper` gives back the paper's `Σ`. -/
theorem PaperLMonoid.toLMonoid_toPaper_sigma {lam : Cardinal.{u}} {H : Type v} [Zero H]
    (P : PaperLMonoid lam H) (x : Idx lam → H) (hx : #(support x) < lam) :
    letI := P.toLMonoid
    (LMonoid.toPaper lam H).sigma x hx = P.sigma x hx := by
  let := P.toLMonoid
  show LMonoid.lsumOf hx (fun i : support x => x i) = _
  rw [P.toLMonoid_lsumOf hx (Function.Embedding.subtype _)]
  apply P.sigma_congr
  funext i
  by_cases hi : i ∈ support x
  · exact (Function.Embedding.subtype _).injective.extend_apply (fun i : support x => x i) 0
      ⟨i, hi⟩
  · rw [extend_apply' _ _ _ (by rintro ⟨j, rfl⟩; exact hi j.2)]
    exact (Function.notMem_support.mp hi).symm

end KappaMonoid
