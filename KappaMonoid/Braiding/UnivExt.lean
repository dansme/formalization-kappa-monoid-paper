/-
The construction `Ĥ = X^κ / (λ⁻-braiding)` and **Theorem 3.12**, with the `IsConical`
hypothesis the paper omits, and its converse.
-/
import KappaMonoid.Braiding.Prop310
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Group.Int.Defs

universe u v w z

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid

variable {lam κ : Cardinal.{u}}

/-! ## The construction `Ĥ = X^κ / (λ⁻-braiding)` -/

section Construction

variable (lam κ) (X : Type v) [LMonoid lam X]

/-- The underlying type of the universal `κ`-extension: `κ`-indexed families over `X`
modulo `λ⁻`-braiding (Theorem 3.12(1)). -/
def UnivExt : Type (max u v) := Quotient (braidingSetoid lam κ X)

namespace UnivExt

variable {lam κ X}

/-- The class of a family. -/
def mk (x : Idx κ → X) : UnivExt lam κ X := Quotient.mk _ x

theorem mk_eq_mk {x y : Idx κ → X} : mk (lam := lam) x = mk y ↔ IsBraided lam x y :=
  Quotient.eq (r := braidingSetoid lam κ X)

/-- A chosen representative of a class. -/
noncomputable def rep (q : UnivExt lam κ X) : Idx κ → X := Quotient.out q

@[simp] theorem mk_rep (q : UnivExt lam κ X) : mk (rep q) = q := Quotient.out_eq q

theorem rep_braided (x : Idx κ → X) : IsBraided lam (rep (mk (lam := lam) x)) x :=
  Quotient.exact (mk_rep (mk (lam := lam) x))

/-- Concatenation of a `κ`-indexed family of `κ`-indexed families, using a fixed bijection
`Idx κ × Idx κ ≃ Idx κ`.  This is the operation on `Ĥ`; it is well defined because braidings
can be concatenated (and independent of the bijection by Lemma 3.6(1)). -/
noncomputable def concat (hκ : ℵ₀ ≤ κ) (F : Idx κ → Idx κ → X) : Idx κ → X :=
  fun k => F ((pairEquiv hκ).symm k).1 ((pairEquiv hκ).symm k).2

/-- The embedding of the `i₀`-th row `{i₀} × κ` of `κ × κ` into `κ`. -/
noncomputable def slot (hκ : ℵ₀ ≤ κ) (i₀ : Idx κ) : Idx κ ↪ Idx κ :=
  ⟨fun j => pairEquiv hκ (i₀, j), fun _a _b hab => congrArg Prod.snd ((pairEquiv hκ).injective hab)⟩

/-- The embedding of the `j₀`-th column `κ × {j₀}` of `κ × κ` into `κ`. -/
noncomputable def coslot (hκ : ℵ₀ ≤ κ) (j₀ : Idx κ) : Idx κ ↪ Idx κ :=
  ⟨fun a => pairEquiv hκ (a, j₀), fun _a _b hab => congrArg Prod.fst ((pairEquiv hκ).injective hab)⟩

theorem slot_ne_slot (hκ : ℵ₀ ≤ κ) {i₀ i₁ : Idx κ} (hne : i₀ ≠ i₁) (i j : Idx κ) :
    slot hκ i₀ i ≠ slot hκ i₁ j := by
  intro h
  exact hne (congrArg Prod.fst ((pairEquiv hκ).injective h))

theorem extend_slot (hκ : ℵ₀ ≤ κ) (i₀ : Idx κ) (a : Idx κ → X) (k : Idx κ) :
    Function.extend (slot hκ i₀) a 0 k =
      if ((pairEquiv hκ).symm k).1 = i₀ then a ((pairEquiv hκ).symm k).2 else 0 := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p : Idx κ × Idx κ, pairEquiv hκ p = k :=
    ⟨(pairEquiv hκ).symm k, Equiv.apply_symm_apply _ _⟩
  rw [Equiv.symm_apply_apply]
  by_cases h : p.1 = i₀
  · have hk : slot hκ i₀ p.2 = pairEquiv hκ p := by
      show pairEquiv hκ (i₀, p.2) = pairEquiv hκ p
      rw [← h]
    rw [← hk, (slot hκ i₀).injective.extend_apply, if_pos h]
  · rw [Function.extend_apply' a (0 : Idx κ → X) _ ?_, if_neg h]
    · rfl
    · rintro ⟨j, hj⟩
      exact h ((congrArg Prod.fst ((pairEquiv hκ).injective hj)).symm)

theorem extend_coslot (hκ : ℵ₀ ≤ κ) (j₀ : Idx κ) (w : Idx κ → X) (k : Idx κ) :
    Function.extend (coslot hκ j₀) w 0 k =
      if ((pairEquiv hκ).symm k).2 = j₀ then w ((pairEquiv hκ).symm k).1 else 0 := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p : Idx κ × Idx κ, pairEquiv hκ p = k :=
    ⟨(pairEquiv hκ).symm k, Equiv.apply_symm_apply _ _⟩
  rw [Equiv.symm_apply_apply]
  by_cases h : p.2 = j₀
  · have hk : coslot hκ j₀ p.1 = pairEquiv hκ p := by
      show pairEquiv hκ (p.1, j₀) = pairEquiv hκ p
      rw [← h]
    rw [← hk, (coslot hκ j₀).injective.extend_apply, if_pos h]
  · rw [Function.extend_apply' w (0 : Idx κ → X) _ ?_, if_neg h]
    · rfl
    · rintro ⟨j, hj⟩
      exact h ((congrArg Prod.snd ((pairEquiv hκ).injective hj)).symm)

theorem concat_slot (hκ : ℵ₀ ≤ κ) (i₀ : Idx κ) (a : Idx κ → X) :
    concat hκ (fun i => if i = i₀ then a else 0) = Function.extend (slot hκ i₀) a 0 := by
  classical
  funext k
  rw [extend_slot]
  show (if ((pairEquiv hκ).symm k).1 = i₀ then a else 0) ((pairEquiv hκ).symm k).2 = _
  by_cases h : ((pairEquiv hκ).symm k).1 = i₀
  · simp only [if_pos h]
  · simp only [if_neg h, Pi.zero_apply]

theorem concat_coslot (hκ : ℵ₀ ≤ κ) (j₀ : Idx κ) (w : Idx κ → X) :
    concat hκ (fun i j => if j = j₀ then w i else 0) = Function.extend (coslot hκ j₀) w 0 := by
  classical
  funext k
  rw [extend_coslot]
  show (if ((pairEquiv hκ).symm k).2 = j₀ then w ((pairEquiv hκ).symm k).1 else 0) = _
  rfl

theorem concat_pair (hκ : ℵ₀ ≤ κ) {i₀ i₁ : Idx κ} (hne : i₀ ≠ i₁) (a b : Idx κ → X) :
    concat hκ (fun i => if i = i₀ then a else if i = i₁ then b else 0)
      = fun k => Function.extend (slot hκ i₀) a 0 k + Function.extend (slot hκ i₁) b 0 k := by
  classical
  funext k
  rw [extend_slot, extend_slot]
  show (if ((pairEquiv hκ).symm k).1 = i₀ then a
      else if ((pairEquiv hκ).symm k).1 = i₁ then b else 0) ((pairEquiv hκ).symm k).2 = _
  by_cases h0 : ((pairEquiv hκ).symm k).1 = i₀
  · have h1 : ¬ ((pairEquiv hκ).symm k).1 = i₁ := by rw [h0]; exact hne
    simp only [if_pos h0, if_neg h1, add_zero]
  · by_cases h1 : ((pairEquiv hκ).symm k).1 = i₁
    · simp only [if_neg h0, if_pos h1, zero_add]
    · simp only [if_neg h0, if_neg h1, Pi.zero_apply, add_zero]

/-- Braidings can be concatenated. -/
theorem mk_concat_congr (hκ : ℵ₀ ≤ κ) {x y : Idx κ → Idx κ → X}
    (h : ∀ i, IsBraided lam (x i) (y i)) :
    mk (lam := lam) (concat hκ x) = mk (concat hκ y) :=
  mk_eq_mk.mpr ((IsBraided.prod h).reindex (pairEquiv hκ).symm)

/-- The `κ`-sum on `Ĥ`. -/
noncomputable def ksumQ (hκ : ℵ₀ ≤ κ) (A : Idx κ → UnivExt lam κ X) : UnivExt lam κ X :=
  mk (concat hκ fun i => rep (A i))

theorem ksumQ_mk (hκ : ℵ₀ ≤ κ) (x : Idx κ → Idx κ → X) :
    ksumQ (lam := lam) hκ (fun i => mk (x i)) = mk (concat hκ x) :=
  mk_concat_congr hκ fun i => rep_braided (x i)

/-- Pointwise addition is compatible with braiding. -/
theorem isBraided_add (hκ : ℵ₀ ≤ κ) {x x' y y' : Idx κ → X}
    (hx : IsBraided lam x x') (hy : IsBraided lam y y') :
    IsBraided lam (fun i => x i + y i) (fun i => x' i + y' i) := by
  classical
  have hnt : Nontrivial (Idx κ) := by
    rw [← Cardinal.one_lt_iff_nontrivial, mk_Idx]
    exact lt_of_lt_of_le one_lt_aleph0 hκ
  obtain ⟨i₀, i₁, hne⟩ := hnt.exists_pair_ne
  have key : ∀ a b : Idx κ → X, mk (lam := lam) (fun i => a i + b i)
      = mk (concat hκ (fun i => if i = i₀ then a else if i = i₁ then b else 0)) := by
    intro a b
    rw [concat_pair hκ hne a b]
    exact mk_eq_mk.mpr (isBraided_merge (slot hκ i₀) (slot hκ i₁) (slot_ne_slot hκ hne) a b)
  rw [← mk_eq_mk, key x y, key x' y']
  refine mk_concat_congr hκ fun i => ?_
  by_cases h0 : i = i₀
  · simp only [if_pos h0]; exact hx
  · by_cases h1 : i = i₁
    · simp only [if_neg h0, if_pos h1]; exact hy
    · simp only [if_neg h0, if_neg h1]; exact IsBraided.refl _

/-- Addition on `Ĥ`, induced by pointwise addition of families. -/
noncomputable def addQ (hκ : ℵ₀ ≤ κ) :
    UnivExt lam κ X → UnivExt lam κ X → UnivExt lam κ X :=
  Quotient.map₂ (fun x y i => x i + y i) fun _ _ hx _ _ hy => isBraided_add hκ hx hy

/-- The commutative monoid structure on `Ĥ`, induced by the pointwise one on `X^κ`. -/
@[instance_reducible]
noncomputable def instAddCommMonoid (hκ : ℵ₀ ≤ κ) : AddCommMonoid (UnivExt lam κ X) :=
  letI : Zero (UnivExt lam κ X) := ⟨mk 0⟩
  letI : Add (UnivExt lam κ X) := ⟨addQ hκ⟩
  { zero := mk 0
    add := addQ hκ
    nsmul := nsmulRec
    nsmul_zero := fun _ => rfl
    nsmul_succ := fun _ _ => rfl
    add_assoc := Quotient.ind fun x => Quotient.ind fun y => Quotient.ind fun z =>
      congrArg mk (funext fun i => add_assoc (x i) (y i) (z i))
    zero_add := Quotient.ind fun x => congrArg mk (funext fun i => zero_add (x i))
    add_zero := Quotient.ind fun x => congrArg mk (funext fun i => add_zero (x i))
    add_comm := Quotient.ind fun x => Quotient.ind fun y =>
      congrArg mk (funext fun i => add_comm (x i) (y i)) }

/-- Axiom (A1) for `Ĥ`. -/
theorem ksumQ_single (hκ : ℵ₀ ≤ κ) (i₀ : Idx κ) (A : Idx κ → UnivExt lam κ X)
    (hA : ∀ i, i ≠ i₀ → A i = mk 0) : ksumQ hκ A = A i₀ := by
  classical
  have h1 : ksumQ hκ A = mk (concat hκ (fun i => if i = i₀ then rep (A i₀) else 0)) := by
    show mk (concat hκ fun i => rep (A i)) = _
    refine mk_concat_congr hκ fun i => ?_
    by_cases h : i = i₀
    · subst h
      simp only [↓reduceIte]
      exact IsBraided.refl _
    · simp only [hA i h, if_neg h]
      exact rep_braided (lam := lam) (0 : Idx κ → X)
  rw [h1, concat_slot, mk_eq_mk.mpr (isBraided_extend (slot hκ i₀) (rep (A i₀))), mk_rep]

/-- Axiom (A2) for `Ĥ`: concatenating in two steps or in one gives braided families. -/
theorem ksumQ_sigma (hκ : ℵ₀ ≤ κ) (A : Idx κ → Idx κ → UnivExt lam κ X)
    (π : Idx κ × Idx κ ≃ Idx κ) :
    ksumQ hκ (fun i => ksumQ hκ (A i))
      = ksumQ hκ (fun k => A (π.symm k).1 (π.symm k).2) := by
  set P := pairEquiv hκ with hPdef
  set x : Idx κ → Idx κ → Idx κ → X := fun i j => rep (A i j) with hxdef
  have hL : ksumQ hκ (fun i => ksumQ hκ (A i)) = mk (concat hκ (fun i => concat hκ (x i))) := by
    show mk (concat hκ fun i => rep (ksumQ hκ (A i))) = _
    exact mk_concat_congr hκ fun i => rep_braided (concat hκ (x i))
  have hR : ksumQ hκ (fun k => A (π.symm k).1 (π.symm k).2)
      = mk (concat hκ (fun k => x (π.symm k).1 (π.symm k).2)) := rfl
  rw [hL, hR]
  set e₁ : Idx κ ≃ Idx κ × Idx κ × Idx κ :=
    P.symm.trans ((Equiv.refl (Idx κ)).prodCongr P.symm) with he₁
  set e₂ : Idx κ ≃ Idx κ × Idx κ × Idx κ :=
    P.symm.trans ((π.symm.prodCongr (Equiv.refl (Idx κ))).trans (Equiv.prodAssoc _ _ _)) with he₂
  set F : Idx κ × Idx κ × Idx κ → X := fun t => x t.1 t.2.1 t.2.2 with hFdef
  have hLe : concat hκ (fun i => concat hκ (x i)) = F ∘ e₁ := rfl
  have hRe : concat hκ (fun k => x (π.symm k).1 (π.symm k).2) = F ∘ e₂ := rfl
  rw [hLe, hRe]
  have hcomp : (F ∘ e₂) ∘ (e₁.trans e₂.symm) = F ∘ e₁ := by
    funext k
    show F (e₂ (e₂.symm (e₁ k))) = F (e₁ k)
    rw [Equiv.apply_symm_apply]
  have hbr : IsBraided lam (F ∘ e₂) (F ∘ e₁) := by
    have h := IsBraided.of_perm (lam := lam) (F ∘ e₂) (e₁.trans e₂.symm)
    rwa [hcomp] at h
  exact (mk_eq_mk.mpr hbr).symm

/-- Compatibility of the `κ`-sum on `Ĥ` with its binary addition. -/
theorem ksumQ_two (hκ : ℵ₀ ≤ κ) (a b : UnivExt lam κ X) (i₀ i₁ : Idx κ) (hne : i₀ ≠ i₁) :
    ksumQ hκ (fun i => if i = i₀ then a else if i = i₁ then b else mk 0) = addQ hκ a b := by
  classical
  have h1 : ksumQ hκ (fun i => if i = i₀ then a else if i = i₁ then b else mk 0)
      = mk (concat hκ (fun i => if i = i₀ then rep a else if i = i₁ then rep b else 0)) := by
    show mk (concat hκ fun i => rep _) = _
    refine mk_concat_congr hκ fun i => ?_
    by_cases h0 : i = i₀
    · simp only [if_pos h0]
      exact IsBraided.refl _
    · by_cases h1 : i = i₁
      · simp only [if_neg h0, if_pos h1]
        exact IsBraided.refl _
      · simp only [if_neg h0, if_neg h1]
        exact rep_braided (lam := lam) (0 : Idx κ → X)
  have h2 : addQ hκ a b = mk (fun i => rep a i + rep b i) := by
    conv_lhs => rw [← mk_rep a, ← mk_rep b]
    rfl
  rw [h1, concat_pair hκ hne, h2]
  exact (mk_eq_mk.mpr (isBraided_merge (slot hκ i₀) (slot hκ i₁) (slot_ne_slot hκ hne)
    (rep a) (rep b))).symm

/-- The `κ`-monoid structure on `Ĥ` (Theorem 3.12(1)). -/
@[instance_reducible]
noncomputable def instKMonoid (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ) :
    KMonoid κ (UnivExt lam κ X) :=
  letI hκ : ℵ₀ ≤ κ := aleph0_le_of_aleph0_le_succ (hlam.aleph0_le.trans hlk)
  letI := instAddCommMonoid (lam := lam) (κ := κ) (X := X) hκ
  KMonoid.ofKsum
    { aleph0_le := hκ
      ksum := ksumQ hκ
      ksum_single := fun i₀ A hA => ksumQ_single hκ i₀ A hA
      ksum_sigma := fun A π => ksumQ_sigma hκ A π }
    fun a b i₀ i₁ hne => ksumQ_two hκ a b i₀ i₁ hne

/-- The `κ`-sum on `Ĥ` is the concatenation operation `ksumQ`. -/
@[simp] theorem instKMonoid_ksum (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ)
    (A : Idx κ → UnivExt lam κ X) :
    letI := instKMonoid (lam := lam) (κ := κ) (X := X) hlam hlk
    ksum (κ := κ) A = ksumQ (aleph0_le_of_aleph0_le_succ (hlam.aleph0_le.trans hlk)) A := by
  let hκ : ℵ₀ ≤ κ := aleph0_le_of_aleph0_le_succ (hlam.aleph0_le.trans hlk)
  let := instAddCommMonoid (lam := lam) (κ := κ) (X := X) hκ
  exact KMonoid.ofKsum_ksum
    { aleph0_le := hκ
      ksum := ksumQ hκ
      ksum_single := fun i₀ A hA => ksumQ_single hκ i₀ A hA
      ksum_sigma := fun A π => ksumQ_sigma hκ A π }
    (fun a b i₀ i₁ hne => ksumQ_two hκ a b i₀ i₁ hne) A

/-- The canonical `λ⁻`-homomorphism `X → Ĥ`, sending `x` to the class of the family
concentrated at one index. -/
noncomputable def of (i₀ : Idx κ) (x : X) : UnivExt lam κ X :=
  mk (fun i => if i = i₀ then x else 0)

theorem of_zero (i₀ : Idx κ) : of (lam := lam) i₀ (0 : X) = mk 0 :=
  congrArg mk (funext fun _ => ite_self 0)

/-- Every class is the `κ`-sum of the images of the entries of any representative. -/
theorem ksumQ_of (hκ : ℵ₀ ≤ κ) (i₀ : Idx κ) (w : Idx κ → X) :
    ksumQ (lam := lam) hκ (fun i => of i₀ (w i)) = mk w := by
  show ksumQ hκ (fun i => mk (fun j => if j = i₀ then w i else 0)) = _
  rw [ksumQ_mk hκ, concat_coslot hκ i₀ w]
  exact mk_eq_mk.mpr (isBraided_extend (coslot hκ i₀) w)

end UnivExt

end Construction

/-! ## Theorem 3.12 -/

/-- **Injectivity of the canonical map**, and the reason reducedness is the right
hypothesis: over a reduced `λ⁻`-monoid `X`, two families concentrated at a single index are
`λ⁻`-braided only if they have the same entry.

Paper-style proof: in a braiding of `(x,0,0,…)` and `(y,0,0,…)`, reducedness forces
`u μ = v μ = 0` for all but at most one index, and the remaining equations give `x = y`.
(Neither the regularity of `λ` nor `λ ≤ κ⁺` is used; the two hypotheses are kept for
uniformity with the rest of the section.) -/
theorem UnivExt.of_injective (_hlam : lam.IsRegular) (_hlk : lam ≤ Order.succ κ) {X : Type v}
    [LMonoid lam X] (hred : IsConical X) (i₀ : Idx κ) :
    Function.Injective (UnivExt.of (lam := lam) (κ := κ) (X := X) i₀) := by
  classical
  intro a b hab
  obtain ⟨d⟩ := UnivExt.mk_eq_mk.mp hab
  have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
  have hsingle : #({i₀} : Set (Idx κ)) < lam := by
    rw [Cardinal.mk_singleton]; exact lt_of_lt_of_le one_lt_aleph0 hlam0
  -- partial sums of a family concentrated at `i₀`
  have hsum : ∀ (S : Set (Idx κ)) (hS : #S < lam) (c : X), i₀ ∈ S →
      lsumOf (lam := lam) hS (fun i : S => (if (i : Idx κ) = i₀ then c else 0)) = c := by
    intro S hS c hmem
    rw [LMonoid.lsumOf_of_subset hS hsingle (Set.singleton_subset_iff.mpr hmem)
      (fun i => if i = i₀ then c else 0)
      (fun i _ hi => if_neg (fun h : i = i₀ => hi (by rw [h]; rfl)))]
    let : Unique ({i₀} : Set (Idx κ)) := Set.uniqueSingleton i₀
    rw [lsumOf_unique hsingle (fun i : ({i₀} : Set (Idx κ)) => (if (i : Idx κ) = i₀ then c else 0))]
    exact if_pos rfl
  have hsum0 : ∀ (S : Set (Idx κ)) (hS : #S < lam) (c : X), i₀ ∉ S →
      lsumOf (lam := lam) hS (fun i : S => (if (i : Idx κ) = i₀ then c else 0)) = 0 :=
    fun S hS c hmem =>
      LMonoid.lsumOf_eq_zero hS (fun i => if i = i₀ then c else 0)
        (fun i hi => if_neg (fun h : i = i₀ => hmem (h ▸ hi)))
  set p₀ := IsBraided.blockOf d.I d.I_cover i₀ with hp₀def
  set q₀ := IsBraided.blockOf d.J d.J_cover i₀ with hq₀def
  have hp₀mem : i₀ ∈ d.I p₀ := IsBraided.mem_blockOf d.I d.I_cover i₀
  have hq₀mem : i₀ ∈ d.J q₀ := IsBraided.mem_blockOf d.J d.J_cover i₀
  have hIeq : ∀ p, d.v p + d.u p = if p = p₀ then a else 0 := by
    intro p
    rw [← d.hI p]
    by_cases h : p = p₀
    · subst h
      rw [if_pos rfl]
      exact hsum _ _ a hp₀mem
    · rw [if_neg h]
      refine hsum0 _ _ a (fun hmem => h ?_)
      exact (IsBraided.blockOf_eq d.I_disjoint d.I_cover hmem).symm
  have hJeq : ∀ p, d.v (bsucc p) + d.u p = if p = q₀ then b else 0 := by
    intro p
    rw [← d.hJ p]
    by_cases h : p = q₀
    · subst h
      rw [if_pos rfl]
      exact hsum _ _ b hq₀mem
    · rw [if_neg h]
      refine hsum0 _ _ b (fun hmem => h ?_)
      exact (IsBraided.blockOf_eq d.J_disjoint d.J_cover hmem).symm
  -- reducedness forces the braiding families to vanish away from the two special positions
  have hA : ∀ r, r ≠ p₀ → d.v r = 0 ∧ d.u r = 0 := by
    intro r hr
    exact hred _ _ (by rw [hIeq r, if_neg hr])
  have hB : ∀ r, r ≠ q₀ → d.v (bsucc r) = 0 ∧ d.u r = 0 := by
    intro r hr
    exact hred _ _ (by rw [hJeq r, if_neg hr])
  have hvzero : ∀ r, r ≠ bsucc q₀ → d.v r = 0 := by
    intro r hr
    by_cases h0 : r.2 = 0
    · have hr0 : r = (r.1, 0) := by rw [← h0]
      rw [hr0]
      exact d.v_limit r.1
    · have hpred : bsucc (r.1, r.2 - 1) = r := IsBraided.bsucc_prev h0
      have hne : (r.1, r.2 - 1) ≠ q₀ := fun hcon => hr (by rw [← hpred, hcon])
      have hv := (hB _ hne).1
      rwa [hpred] at hv
  have ha : d.v p₀ + d.u p₀ = a := by rw [hIeq p₀, if_pos rfl]
  have hb : d.v (bsucc q₀) + d.u q₀ = b := by rw [hJeq q₀, if_pos rfl]
  by_cases hpq : p₀ = q₀
  · have h1 : d.v p₀ = 0 := hvzero p₀ (by rw [← hpq]; exact IsBraided.bsucc_ne_self p₀)
    have h2 : d.v (bsucc q₀) = 0 :=
      (hA _ (by rw [← hpq]; exact Ne.symm (IsBraided.bsucc_ne_self p₀))).1
    calc a = d.v p₀ + d.u p₀ := ha.symm
      _ = d.u p₀ := by rw [h1, zero_add]
      _ = d.u q₀ := by rw [hpq]
      _ = d.v (bsucc q₀) + d.u q₀ := by rw [h2, zero_add]
      _ = b := hb
  · have hu1 : d.u p₀ = 0 := (hB p₀ hpq).2
    have hu2 : d.u q₀ = 0 := (hA q₀ (Ne.symm hpq)).2
    by_cases hbq : p₀ = bsucc q₀
    · calc a = d.v p₀ + d.u p₀ := ha.symm
        _ = d.v p₀ := by rw [hu1, add_zero]
        _ = d.v (bsucc q₀) := by rw [hbq]
        _ = d.v (bsucc q₀) + d.u q₀ := by rw [hu2, add_zero]
        _ = b := hb
    · have h1 : d.v p₀ = 0 := hvzero p₀ hbq
      have h2 : d.v (bsucc q₀) = 0 := (hA _ (fun hc => hbq hc.symm)).1
      calc a = d.v p₀ + d.u p₀ := ha.symm
        _ = d.v p₀ := by rw [hu1, add_zero]
        _ = 0 := h1
        _ = d.v (bsucc q₀) := h2.symm
        _ = d.v (bsucc q₀) + d.u q₀ := by rw [hu2, add_zero]
        _ = b := hb

/-- **Theorem 3.12** (with the hypothesis `IsConical X` added, cf. the module docstring).

Let `λ ≤ κ⁺` with `λ` regular and let `X` be a *reduced* `λ⁻`-monoid.  Then there is a
`κ`-monoid `Ĥ` containing `X` as a `λ⁻`-submonoid such that

1. `Ĥ` is `λ⁻`-braided over `X`, and
2. `Ĥ` is the universal `κ`-extension of `X`. -/
theorem theorem_3_12 (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ) (X : Type v) [LMonoid lam X]
    (hred : IsConical X) :
    ∃ (Hh : Type (max u v)) (_ : KMonoid κ Hh) (f : X → Hh),
      Function.Injective f ∧
      IsBraidedOver lam κ X Hh hlk f ∧
      IsUniversalKExtension lam κ X Hh hlk f := by
  classical
  have hκ : ℵ₀ ≤ κ := aleph0_le_of_aleph0_le_succ (hlam.aleph0_le.trans hlk)
  obtain ⟨i₀⟩ := nonempty_Idx hκ
  let inst : KMonoid κ (UnivExt lam κ X) := UnivExt.instKMonoid hlam hlk
  have hgen : ∀ w : Idx κ → X,
      ksum (κ := κ) (fun i => UnivExt.of (lam := lam) i₀ (w i)) = UnivExt.mk w :=
    fun w => (UnivExt.instKMonoid_ksum hlam hlk _).trans (UnivExt.ksumQ_of hκ i₀ w)
  have hof0 : UnivExt.of (lam := lam) (κ := κ) (X := X) i₀ 0 = 0 := UnivExt.of_zero i₀
  have hbraided : IsBraidedOver lam κ X (UnivExt lam κ X) hlk (UnivExt.of i₀) := by
    refine ⟨⟨hof0, ?_⟩, UnivExt.of_injective hlam hlk hred i₀, ?_, ?_⟩
    · -- `of i₀` is a `λ⁻`-homomorphism
      intro ι h z
      have hg : #ι ≤ κ := le_of_lt_of_le_succ hlk h
      set g : ι ↪ Idx κ := emb hg with hgdef
      have hfam : Function.extend g (fun i => UnivExt.of (lam := lam) i₀ (z i)) 0
          = fun a => UnivExt.of (lam := lam) i₀ (Function.extend g z 0 a) := by
        funext a
        by_cases ha : ∃ i, g i = a
        · obtain ⟨i, rfl⟩ := ha
          rw [g.injective.extend_apply, g.injective.extend_apply]
        · rw [Function.extend_apply' _ _ _ ha, Function.extend_apply' _ _ _ ha]
          show (0 : UnivExt lam κ X) = UnivExt.of i₀ (0 : X)
          rw [hof0]
      show UnivExt.of i₀ (lsumOf h z)
        = sumOf (κ := κ) hg (fun i => UnivExt.of (lam := lam) i₀ (z i))
      rw [KMonoid.sumOf_eq_extend hg g, hfam, hgen (Function.extend g z 0)]
      -- both sides are classes of families with small support and equal sums
      refine UnivExt.mk_eq_mk.mpr ?_
      have hlam0 := LMonoid.aleph0_le (lam := lam) (X := X)
      have hsingle : #({i₀} : Set (Idx κ)) < lam := by
        rw [Cardinal.mk_singleton]; exact lt_of_lt_of_le one_lt_aleph0 hlam0
      have hrange : #(Set.range g : Set (Idx κ)) < lam := by
        rw [Cardinal.mk_range_eq g g.injective]; exact h
      refine isBraided_of_small_sets hsingle hrange (fun i hi => if_neg (fun hc => hi hc))
        (fun j hj => Function.extend_apply' z (0 : Idx κ → X) j (fun ⟨i, hi⟩ => hj ⟨i, hi⟩)) ?_
      let : Unique ({i₀} : Set (Idx κ)) := Set.uniqueSingleton i₀
      rw [lsumOf_unique hsingle
        (fun i : ({i₀} : Set (Idx κ)) => (if (i : Idx κ) = i₀ then lsumOf h z else 0))]
      have hdef : ((default : ({i₀} : Set (Idx κ))) : Idx κ) = i₀ := rfl
      rw [hdef, if_pos rfl]
      have hcomp : (fun j : Set.range g => Function.extend g z 0 (j : Idx κ))
          ∘ (Equiv.ofInjective (g : ι → Idx κ) g.injective) = z := by
        funext i
        exact g.injective.extend_apply z 0 i
      rw [lsumOf_equiv hrange h (Equiv.ofInjective (g : ι → Idx κ) g.injective)
        (fun j : Set.range g => Function.extend g z 0 (j : Idx κ)), hcomp]
    · -- `Ĥ` is generated by the image of `X`
      intro q
      exact ⟨UnivExt.rep q, by rw [hgen (UnivExt.rep q), UnivExt.mk_rep]⟩
    · -- families with equal `κ`-sums are braided
      intro x y hxy
      rw [hgen x, hgen y] at hxy
      exact UnivExt.mk_eq_mk.mp hxy
  exact ⟨UnivExt lam κ X, inst, UnivExt.of i₀, UnivExt.of_injective hlam hlk hred i₀, hbraided,
    hbraided.isUniversalKExtension hlk⟩

/-- **Theorem 3.12** for `λ > ℵ₀`, exactly as printed in the paper: there the hypothesis added
to `theorem_3_12` is automatic, since a `λ⁻`-monoid with `ℵ₀ < λ` is reduced by
`LMonoid.isConical` (the analogue of Lemma 2.8(1) for `λ⁻`-monoids).

So the deviation from the paper is confined to `λ = ℵ₀`, where a `λ⁻`-monoid is an arbitrary
commutative monoid and the hypothesis is genuinely necessary — see
`isConical_of_isUniversalKExtension` and the counterexample `ℤ` below. -/
theorem theorem_3_12_of_aleph0_lt (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ) (hlam0 : ℵ₀ < lam)
    (X : Type v) [LMonoid lam X] :
    ∃ (Hh : Type (max u v)) (_ : KMonoid κ Hh) (f : X → Hh),
      Function.Injective f ∧
      IsBraidedOver lam κ X Hh hlk f ∧
      IsUniversalKExtension lam κ X Hh hlk f :=
  theorem_3_12 hlam hlk X (LMonoid.isConical hlam0)

/-- **Theorem 3.12 as an equivalence**: a universal `κ`-extension of a reduced `λ⁻`-monoid `X` is
`λ⁻`-braided over `X`.  Together with `IsBraidedOver.isUniversalKExtension` this is the paper's
remark after Definition 3.11 that "`Ĥ` is `λ⁻`-braided over `H`" and "`Ĥ` is the universal
`κ`-extension of `H`" are two descriptions of the same thing.

Proof: `theorem_3_12` produces *some* extension that is both braided and universal, uniqueness of
universal extensions identifies it with the given one, and braidedness transports along that
isomorphism (`IsBraidedOver.of_iso`).

The universe `Type (max u v)` is where `theorem_3_12` puts its extension, and uniqueness compares
two extensions in the same universe; for `X : Type u` this is no restriction, and for
`X : Type (u+1)` — the case of `F_κ` and its powers — it reads `Type (u+1)`. -/
theorem isBraidedOver_of_isUniversalKExtension (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ)
    {X : Type v} [LMonoid lam X] (hred : IsConical X) {H : Type (max u v)} [KMonoid κ H]
    {f : X → H} (hu : IsUniversalKExtension.{u, v, max u v, max u v} lam κ X H hlk f) :
    IsBraidedOver lam κ X H hlk f := by
  obtain ⟨Hh, _, g, _, hgbr, hgu⟩ := theorem_3_12 hlam hlk X hred
  obtain ⟨e, ⟨hehom, hecomm, hebij⟩, -⟩ := isUniversalKExtension_unique hlk hgu hu
  exact hgbr.of_iso hlk hehom hebij hecomm

/-- Conversely, a `λ⁻`-monoid admitting a universal `κ`-extension into which it embeds must
be reduced; so the hypothesis added in `theorem_3_12` cannot be dropped. -/
theorem isConical_of_isUniversalKExtension {X : Type v} {Hh : Type w}
    [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ Order.succ κ) {f : X → Hh}
    (hf : Function.Injective f) (hhom : IsLHom hlk f) : IsConical X :=
  LMonoid.isConical_of_injective (lam := lam) (κ := κ) f hf hhom.1
    (fun a b => IsLHom.map_add hlk hhom a b)

/-- A concrete counterexample to Theorem 3.12 as printed: `ℤ` is an `ℵ₀⁻`-monoid (i.e. a
commutative monoid) that is not reduced, hence embeds into no `κ`-monoid.

Note that the `ℵ₀⁻`-monoid structure on `ULift ℤ` has to be the canonical one of
`LMonoid.ofAddCommMonoid`: for an arbitrary `LMonoid ℵ₀ (ULift ℤ)` instance the underlying
addition is arbitrary as well, and then `1 + (-1) = 0` is not available. -/
example (hlk : (ℵ₀ : Cardinal.{u}) ≤ Order.succ κ) {Hh : Type w} [KMonoid κ Hh]
    (f : ULift.{u} ℤ → Hh) (hf : Function.Injective f)
    (hhom : letI := LMonoid.ofAddCommMonoid (ULift.{u} ℤ); IsLHom hlk f) : False := by
  let := LMonoid.ofAddCommMonoid (ULift.{u} ℤ)
  have hcon := isConical_of_isUniversalKExtension (lam := ℵ₀) hlk hf hhom
  have h0 : (⟨1⟩ : ULift.{u} ℤ) + ⟨(-1 : ℤ)⟩ = 0 := by
    apply ULift.ext
    show (1 : ℤ) + (-1) = 0
    ring
  have h1 := congrArg ULift.down (hcon ⟨1⟩ ⟨(-1 : ℤ)⟩ h0).1
  exact one_ne_zero h1

end KappaMonoid
