/-
**Lemma 5.2**(1)-(5), with the fibre and block machinery the proofs run on.  Pure monoid theory:
no module, no axiom.
-/
import KappaMonoid.TwoGen.Prelim
import KappaMonoid.ForMathlib.NatBlocks

universe u v

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

variable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]

/-! ## Lemma 5.2 (`easyfactlemma1`)

Five basic facts about forms and braiding.  Parts (1), (2) and (5) are cheap; (3) is the longest
proof in the section and (4) is its counterpart for incomparable generators. -/

section Lemma52

variable (x₁ x₂ : H)

/-- In the setting of §5 the generators are nonzero: a zero generator could be dropped, making `H`
cyclic.  This is what supplies the non-degeneracy hypotheses of Lemma 5.2(1). -/
theorem ne_zero_of_not_cyclic (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (hnc : ∀ x : H, ¬ KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x} : Set H)) :
    x₁ ≠ 0 ∧ x₂ ≠ 0 := by
  have key : ∀ a b : H, a = 0 → KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({a, b} : Set H) →
      KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({b} : Set H) := by
    intro a b ha hab
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hab]
    refine KMonoid.kclosure_le (fun y hy => ?_) (KMonoid.isKSubmonoid_kclosure _ _)
    rcases hy with rfl | hy
    · rw [ha]
      exact (KMonoid.isKSubmonoid_kclosure (ℵ₀ : Cardinal.{u}) ({b} : Set H)).zero_mem
    · exact KMonoid.subset_kclosure hy
  refine ⟨fun h => hnc x₂ (key x₁ x₂ h hgen), fun h => hnc x₁ (key x₂ x₁ h ?_)⟩
  rwa [Set.pair_comm]

/-- `add (x₁ + x₂)` is reduced: it is a submonoid of a `κ`-monoid, and those are reduced by
Lemma 2.8(1). -/
theorem isConical_addOf :

    IsConical ↥(add((x₁ + x₂))) := by

  exact LMonoid.isConical_of_injective (lam := (ℵ₀ : Cardinal.{u})) (κ := (ℵ₀ : Cardinal.{u}))
    (fun y : ↥(add((x₁ + x₂))) => (y : H)) Subtype.val_injective rfl
    (fun _ _ => rfl)

/-- Inside `add (x₁ + x₂)` a form's family has the same support as in `H`. -/
theorem support_subtype_familyOfForm (F : Form)
    (hF : ∀ i, familyOfForm x₁ x₂ F i ∈ add((x₁ + x₂))) :

    Function.support (fun i => (⟨familyOfForm x₁ x₂ F i, hF i⟩ :
        ↥(add((x₁ + x₂))))) = Function.support (familyOfForm x₁ x₂ F) := by

  ext i
  exact ⟨fun hi hz => hi (Subtype.ext hz), fun hi hz => hi (congrArg Subtype.val hz)⟩

/-- The support of a form's family is contained in its slots. -/
theorem support_subset_slots (F : Form) :
    Function.support (familyOfForm x₁ x₂ F) ⊆ slots.{u} F := by
  intro i hi
  by_contra hni
  exact hi (familyOfForm_eq_zero_of_notMem_slots x₁ x₂ hni)

/-- The `add (x₁ + x₂)`-valued family of a *finite* form has support of size `< ℵ₀`. -/
theorem mk_support_subtype_lt {F : Form} (hF : F.IsFinite)
    (hFm : ∀ i, familyOfForm x₁ x₂ F i ∈ add((x₁ + x₂))) :

    #(Function.support (fun i => (⟨familyOfForm x₁ x₂ F i, hFm i⟩ :
        ↥(add((x₁ + x₂)))))) < (ℵ₀ : Cardinal.{u}) := by

  rw [support_subtype_familyOfForm x₁ x₂ F hFm]
  exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset (support_subset_slots x₁ x₂ F))
    (mk_slots_lt hF)

/-- **Lemma 5.2(1)**: an infinite and a finite form cannot be braided.

**The non-degeneracy hypotheses are needed**: with `x₁ = 0` the infinite form `(ℵ₀, 0)` has the
identically zero family, which *is* braided with the finite form `(0, 0)`.  In §5 they come free
from non-cyclicity — see `ne_zero_of_not_cyclic`.

Proof: the finite form's family has finite support, so by the converse of Lemma 3.4(1)
(`IsBraided.mk_support_lt`, which needs reducedness of `add (x₁ + x₂)`) a braided partner has
finite support too; but an infinite form's family has infinite support. -/
theorem lemma_5_2_one (F G : Form) (hF : F.IsInfinite) (hG : G.IsFinite)
    (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0)
    (hFm : ∀ n, familyOfForm x₁ x₂ F n ∈ add((x₁ + x₂)))
    (hGm : ∀ n, familyOfForm x₁ x₂ G n ∈ add((x₁ + x₂))) :
    ¬ BraidedForms x₁ x₂ F G hFm hGm := by

  intro hbr
  have hbr' : IsBraided (ℵ₀ : Cardinal.{u})
      (fun i => (⟨familyOfForm x₁ x₂ F i, hFm i⟩ : ↥(add((x₁ + x₂)))))
      (fun i => (⟨familyOfForm x₁ x₂ G i, hGm i⟩ : ↥(add((x₁ + x₂))))) := hbr
  have hsuppF := hbr'.symm.mk_support_lt (isConical_addOf x₁ x₂)
    (mk_support_subtype_lt x₁ x₂ hG hGm)
  rw [support_subtype_familyOfForm x₁ x₂ F hFm] at hsuppF
  exact infinite_support_familyOfForm x₁ x₂ hF h₁ h₂
    (Cardinal.lt_aleph0_iff_set_finite.mp hsuppF)

/-- The sum of a finite form's family over its slots is the element the form represents. -/
theorem coe_lsumOf_slots {F : Form} (hF : F.IsFinite)
    (hFm : ∀ i, familyOfForm x₁ x₂ F i ∈ add((x₁ + x₂))) :

    ((LMonoid.lsumOf (lam := (ℵ₀ : Cardinal.{u})) (mk_slots_lt hF)
        (fun i : slots.{u} F => (⟨familyOfForm x₁ x₂ F i, hFm i⟩ :
          ↥(add((x₁ + x₂))))) :
        ↥(add((x₁ + x₂)))) : H) = eval x₁ x₂ F := by

  -- the coercion of a submonoid sum *is* the sum in `H` (`IsLSubset.coe_lsumOf` is `rfl`)
  show KMonoid.sumOf (κ := ℵ₀) ((mk_slots_lt hF).le.trans le_rfl)
      (fun i : slots.{u} F => familyOfForm x₁ x₂ F i) = eval x₁ x₂ F
  rw [← KMonoid.sumOf_eq_sumOf_subset mk_formIdx_le_aleph0 ((mk_slots_lt hF).le.trans le_rfl)
    (familyOfForm x₁ x₂ F) fun i hi => familyOfForm_eq_zero_of_notMem_slots x₁ x₂ hi]
  exact sumOf_familyOfForm x₁ x₂ F

/-- **Lemma 5.2(2)**: two finite forms of the same element are braided over `add (x₁ + x₂)`.

Both families are supported on finitely many slots and have the same sum there, which is
`isBraided_of_small_sets`. -/
theorem lemma_5_2_two (F G : Form) (hF : F.IsFinite) (hG : G.IsFinite)
    (heq : eval x₁ x₂ F = eval x₁ x₂ G)
    (hFm : ∀ n, familyOfForm x₁ x₂ F n ∈ add((x₁ + x₂)))
    (hGm : ∀ n, familyOfForm x₁ x₂ G n ∈ add((x₁ + x₂))) :
    BraidedForms x₁ x₂ F G hFm hGm := by

  exact isBraided_of_small_sets (mk_slots_lt hF) (mk_slots_lt hG)
    (fun i hi => Subtype.ext (familyOfForm_eq_zero_of_notMem_slots x₁ x₂ hi))
    (fun i hi => Subtype.ext (familyOfForm_eq_zero_of_notMem_slots x₁ x₂ hi))
    (Subtype.ext (by rw [coe_lsumOf_slots x₁ x₂ hF hFm, coe_lsumOf_slots x₁ x₂ hG hGm]; exact heq))

/-! ### Fibres of a level function on `FormIdx`

`IsBraided.of_levels` (Braiding.lean) reduces building a braiding to a pair of *level functions*
`FormIdx → ℕ` with finite fibres and two block equations.  A level function on `FormIdx` is a
`Sum.elim` of two level functions on `Nats`, its fibre splits accordingly, and the families of §5
are constant on each half — so every block sum is `(#fibre) • x₁ + (#fibre) • x₂`.  These are the
counts that come up: an interval fibre `j / d = k` has `d` elements, a singleton fibre one, and the
`X₁`-slots of a finite form are `{j < A}`. -/

section Fibres

/-- A subset of `Nats` cut out by a subset of `ℕ` is its image. -/
theorem nats_setOf (T : Set ℕ) : {j : Nats.{u} | j.down ∈ T} = ULift.up '' T := by
  ext ⟨j⟩
  refine ⟨fun h => ⟨j, h, rfl⟩, ?_⟩
  rintro ⟨j', hj', hje⟩
  have hj : j' = j := congrArg ULift.down hje
  subst hj
  exact hj'

theorem ncard_nats_setOf (T : Set ℕ) : ({j : Nats.{u} | j.down ∈ T}).ncard = T.ncard := by
  rw [nats_setOf]
  exact Set.ncard_image_of_injective T (fun a b hab => congrArg ULift.down hab)

theorem finite_nats_setOf {T : Set ℕ} (hT : T.Finite) : ({j : Nats.{u} | j.down ∈ T}).Finite := by
  rw [nats_setOf]; exact hT.image _

/-- The fibre of a level function on `FormIdx` splits into its two halves. -/
theorem fiber_elim (f g : Nats.{u} → ℕ) (k : ℕ) :
    {i : FormIdx.{u} | Sum.elim f g i = k}
      = Sum.inl '' {j : Nats.{u} | f j = k} ∪ Sum.inr '' {j : Nats.{u} | g j = k} := by
  ext i
  rcases i with j | j <;> simp

theorem finite_fiber_elim {f g : Nats.{u} → ℕ} {k : ℕ}
    (hf : {j : Nats.{u} | f j = k}.Finite) (hg : {j : Nats.{u} | g j = k}.Finite) :
    {i : FormIdx.{u} | Sum.elim f g i = k}.Finite := by
  rw [fiber_elim]
  exact (hf.image _).union (hg.image _)

/-- **The block sum of a family constant on each half of `FormIdx`**: it is `#fibre` copies of the
value on the left half plus `#fibre` copies of the value on the right half. -/
theorem finsum_fiber_const {M : Type v} [AddCommMonoid M] {f g : Nats.{u} → ℕ} {k : ℕ}
    (hf : {j : Nats.{u} | f j = k}.Finite) (hg : {j : Nats.{u} | g j = k}.Finite)
    (F : FormIdx.{u} → M) {a b : M}
    (hfa : ∀ j ∈ {j : Nats.{u} | f j = k}, F (Sum.inl j) = a)
    (hgb : ∀ j ∈ {j : Nats.{u} | g j = k}, F (Sum.inr j) = b) :
    ∑ᶠ i ∈ {i : FormIdx.{u} | Sum.elim f g i = k}, F i
      = ({j : Nats.{u} | f j = k}).ncard • a + ({j : Nats.{u} | g j = k}).ncard • b := by
  classical
  have hdisj : Disjoint (Sum.inl '' {j : Nats.{u} | f j = k})
      (Sum.inr '' {j : Nats.{u} | g j = k}) := by
    refine Set.disjoint_left.mpr ?_
    rintro i ⟨j, -, rfl⟩ ⟨j', -, hj'⟩
    exact Sum.inl_ne_inr hj'.symm
  rw [fiber_elim, finsum_mem_union hdisj (hf.image _) (hg.image _),
    finsum_mem_image Sum.inl_injective.injOn, finsum_mem_image Sum.inr_injective.injOn,
    finsum_mem_congr rfl hfa, finsum_mem_congr rfl hgb,
    finsum_mem_const_finite hf, finsum_mem_const_finite hg]

end Fibres

/-! ### The fibre counts used by Lemma 5.2(3) -/

theorem ecmul_add (a b : ℕ∞) (x : H) : ecmul (a + b) x = ecmul a x + ecmul b x := by
  have hc : Cardinal.ofENat (a + b) = Cardinal.ofENat a + Cardinal.ofENat b := by simp
  have hle : Cardinal.ofENat a + Cardinal.ofENat b ≤ ℵ₀ := hc ▸ Cardinal.ofENat_le_aleph0 (a + b)
  rw [ecmul, ecmul, ecmul, KMonoid.cmul_congr hc _ hle,
    KMonoid.cmul_add (Cardinal.ofENat_le_aleph0 a) (Cardinal.ofENat_le_aleph0 b) hle]

theorem ecmul_one_add (a : ℕ∞) (x : H) : ecmul (1 + a) x = x + ecmul a x := by
  have hc : Cardinal.ofENat (1 + a) = 1 + Cardinal.ofENat a := by simp
  have hle : (1 : Cardinal.{u}) + Cardinal.ofENat a ≤ ℵ₀ := hc ▸ Cardinal.ofENat_le_aleph0 (1 + a)
  rw [ecmul, ecmul, KMonoid.cmul_congr hc _ hle,
    KMonoid.cmul_add (le_of_lt Cardinal.one_lt_aleph0) (Cardinal.ofENat_le_aleph0 a) hle,
    KMonoid.cmul_one]

theorem ecmul_natCast (k : ℕ) (x : H) : ecmul ((k : ℕ) : ℕ∞) x = k • x := by
  rw [ecmul, KMonoid.cmul_congr (by simp : Cardinal.ofENat ((k : ℕ) : ℕ∞) = ((k : ℕ) : Cardinal.{u}))
    _ (le_of_lt Cardinal.natCast_lt_aleph0)]
  exact KMonoid.cmul_natCast x k

/-- `add y` is closed under binary sums: `+` is a two-element `ℵ₀⁻`-sum. -/
theorem addOf_add_mem {y a b : H} (ha : a ∈ add(y))
    (hb : b ∈ add(y)) : a + b ∈ add(y) :=
  (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl y).add_mem le_rfl ha hb

theorem addOf_nsmul_mem {y a : H} (ha : a ∈ add(y)) (k : ℕ) :
    k • a ∈ add(y) :=
  (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl y).nsmul_mem le_rfl ha k

/-- `add a ⊆ add b` as soon as `a ∈ add b`. -/
theorem addOf_subset_of_mem {a b : H} (h : a ∈ add(b)) :
    add(a) ⊆ add(b) := by
  rintro y ⟨z, n, hzn⟩
  refine KMonoid.addOf_isSaturated b
    (KMonoid.cmul (κ := ℵ₀) (n : Cardinal.{u})
      (le_trans (le_of_lt Cardinal.natCast_lt_aleph0) le_rfl) a) ?_ y z hzn.symm
  rw [KMonoid.cmul_natCast]
  exact addOf_nsmul_mem h n

/-- The fibre at `0` of the level function that parks the first `A` slots on level `0`. -/
theorem levelA_fiber_zero (A : ℕ) :
    {j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = 0}
      = {j : Nats.{u} | j.down < A} := by
  ext ⟨j⟩
  by_cases h : j < A <;> simp [h]

/-- Its fibre at `k + 1` is the singleton `{A + k}`. -/
theorem levelA_fiber_succ (A k : ℕ) :
    {j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = k + 1}
      = {j : Nats.{u} | j.down = A + k} := by
  ext ⟨j⟩
  by_cases h : j < A <;> simp [h] <;> omega

theorem divsucc_fiber_zero (n : ℕ) : {j : Nats.{u} | j.down / n + 1 = 0} = ∅ := by
  ext ⟨j⟩; simp

theorem divsucc_fiber_succ (n k : ℕ) :
    {j : Nats.{u} | j.down / n + 1 = k + 1} = {j : Nats.{u} | j.down / n = k} := by
  ext ⟨j⟩; simp


theorem familyOfForm_inl (F : Form) (j : Nats.{u}) :
    familyOfForm x₁ x₂ F (Sum.inl j) = if ((j.down : ℕ) : ℕ∞) < F.1 then x₁ else 0 := rfl

theorem familyOfForm_inr (F : Form) (j : Nats.{u}) :
    familyOfForm x₁ x₂ F (Sum.inr j) = if ((j.down : ℕ) : ℕ∞) < F.2 then x₂ else 0 := rfl

/-- Every slot of every form lies in `add (x₁ + x₂)`. -/
theorem familyOfForm_mem (F : Form) (i : FormIdx.{u}) :
    familyOfForm x₁ x₂ F i ∈ add((x₁ + x₂)) := by
  have h₁ : x₁ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have h₂ : x₂ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  have h0 : (0 : H) ∈ add((x₁ + x₂)) :=
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)).zero_mem
  rcases i with j | j
  · rw [familyOfForm_inl]; split <;> assumption
  · rw [familyOfForm_inr]; split <;> assumption

theorem ncard_nats_div {d : ℕ} (hd : 0 < d) (k : ℕ) :
    ({j : Nats.{u} | j.down / d = k}).ncard = d :=
  (ncard_nats_setOf {n : ℕ | n / d = k}).trans (Nat.ncard_div_fiber hd k)

theorem finite_nats_div {d : ℕ} (hd : 0 < d) (k : ℕ) : ({j : Nats.{u} | j.down / d = k}).Finite :=
  finite_nats_setOf (Nat.finite_div_fiber hd k)

theorem ncard_nats_eq (k : ℕ) : ({j : Nats.{u} | j.down = k}).ncard = 1 :=
  (ncard_nats_setOf {k}).trans (Set.ncard_singleton k)

theorem finite_nats_eq (k : ℕ) : ({j : Nats.{u} | j.down = k}).Finite :=
  finite_nats_setOf (Set.finite_singleton k)

theorem ncard_nats_lt (A : ℕ) : ({j : Nats.{u} | j.down < A}).ncard = A :=
  (ncard_nats_setOf (Set.Iio A)).trans (Set.ncard_Iio_nat A)

theorem finite_nats_lt (A : ℕ) : ({j : Nats.{u} | j.down < A}).Finite :=
  finite_nats_setOf (Set.finite_Iio A)

/-- The coercion of a `finsum` over a finite set from `add (x₁ + x₂)` to `H`: the block sums of a
braiding built inside the submonoid may be computed in `H`. -/
theorem coe_finsum_mem {S : Set FormIdx.{u}} (hS : S.Finite) (f : FormIdx.{u} → H)
    (hf : ∀ i, f i ∈ add((x₁ + x₂))) :

    (((∑ᶠ i ∈ S, (⟨f i, hf i⟩ : ↥(add((x₁ + x₂))))) :
        ↥(add((x₁ + x₂)))) : H) = ∑ᶠ i ∈ S, f i := by

  exact AddMonoidHom.map_finsum_mem _
    ({ toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      ↥(add((x₁ + x₂))) →+ H) hS

/-- **The heart of Lemma 5.2(3)**: `α X₁ + ℵ₀ X₂` is braided with `ℵ₀ X₂`, for every `α ≤ ℵ₀`.

The paper writes down the partitions outright; here they are given as *level functions* on
`FormIdx`, one for each copy of `ℕ`, and fed to `IsBraided.of_levels`.

For `α = A` finite, `A x₁ ∈ add x₂` gives `A x₁ + t = n x₂` with `n ≥ 1`, and the levels are

    cI = (j ↦ if j < A then 0 else j - A + 1) ⊕ (j ↦ j / n + 1),   cJ = (j ↦ j) ⊕ (j ↦ j / n),
    u ≡ A x₁,   v 0 = 0,   v (k+1) = t,

so that level `0` of `I` collects exactly the `A` copies of `x₁` and every later level collects
`n` copies of `x₂`, which is `t + A x₁`.

For `α = ℵ₀` one first re-derives `m x₂ = (m'+1) x₁ + n' x₂` with `m'`, `n'` finite — this is where
`NoMixedForms` and the generation hypothesis enter, since `t = m' x₁ + n' x₂` would otherwise give
`m x₂` an infinite form alongside its finite one — and then the two families have *equal* block
sums, so `v ≡ 0`:

    cI = (j ↦ j / (m'+1)) ⊕ (j ↦ j / (n'+1)),   cJ = (j ↦ j) ⊕ (j ↦ j / m),   u ≡ m x₂.

**The generation hypothesis `hgen` is needed**: it is a standing assumption of §5, and the
`α = ℵ₀` case genuinely uses it. -/
theorem braidedForms_of_top (hmem : x₁ ∈ add(x₂)) (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H)) (α : ℕ∞)
    (hFm : ∀ n, familyOfForm x₁ x₂ (α, ⊤) n ∈ add((x₁ + x₂)))
    (hGm : ∀ n, familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) n ∈ add((x₁ + x₂))) :
    BraidedForms x₁ x₂ (α, ⊤) ((0 : ℕ∞), ⊤) hFm hGm := by
  classical

  have hx₁T : x₁ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  show IsBraided (ℵ₀ : Cardinal.{u})
    (fun i => (⟨familyOfForm x₁ x₂ (α, ⊤) i, hFm i⟩ : ↥(add((x₁ + x₂)))))
    (fun i => (⟨familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) i, hGm i⟩ :
      ↥(add((x₁ + x₂)))))
  -- a degenerate case: with `x₁ = 0` the two families are literally equal
  rcases eq_or_ne x₁ 0 with hx0 | hx0
  · have hfam : (fun i => (⟨familyOfForm x₁ x₂ (α, ⊤) i, hFm i⟩ :
        ↥(add((x₁ + x₂)))))
      = (fun i => (⟨familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) i, hGm i⟩ :
        ↥(add((x₁ + x₂))))) := by
      funext i
      refine Subtype.ext ?_
      rcases i with j | j
      · show familyOfForm x₁ x₂ (α, ⊤) (Sum.inl j)
          = familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) (Sum.inl j)
        rw [familyOfForm_inl, familyOfForm_inl]
        simp [hx0]
      · show familyOfForm x₁ x₂ (α, ⊤) (Sum.inr j)
          = familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) (Sum.inr j)
        rfl
    -- `IsBraided.refl` is `@[refl]`, so `rw` closes the goal
    rw [hfam]
  -- `x₁ + z = m₀ x₂` with `m₀ ≥ 1`
  obtain ⟨z, m₀, hz⟩ := hmem
  rw [KMonoid.cmul_natCast] at hz
  have hm₀ : m₀ ≠ 0 := by
    rintro rfl
    rw [zero_nsmul] at hz
    exact hx0 (KMonoid.isConical (ℵ₀ : Cardinal.{u}) H x₁ z hz).1
  rcases eq_or_ne α ⊤ with rfl | hα
  · -- **the case `α = ℵ₀`**: re-derive `m x₂ = (m'+1) x₁ + n' x₂` and match the block sums
    obtain ⟨G, hG⟩ := exists_form x₁ x₂ hgen z
    have hGfin : G.1 ≠ ⊤ ∧ G.2 ≠ ⊤ := by
      by_contra hcon
      refine hmix (m₀ • x₂) ⟨⟨(0, (m₀ : ℕ∞)), ⟨by simp, by simp⟩, ?_⟩, ⟨(1 + G.1, G.2), ?_, ?_⟩⟩
      · rw [eval, ecmul_zero, zero_add, ecmul_natCast]
      · rcases not_and_or.mp hcon with h | h
        · exact Or.inl (by rw [not_ne_iff.mp h]; exact add_top 1)
        · exact Or.inr (not_ne_iff.mp h)
      · rw [eval, ecmul_one_add, add_assoc, ← eval, hG, hz]
    obtain ⟨m', hm'⟩ : ∃ m' : ℕ, G.1 = (m' : ℕ∞) := ⟨G.1.toNat, (ENat.natCast_toNat hGfin.1).symm⟩
    obtain ⟨n', hn'⟩ : ∃ n' : ℕ, G.2 = (n' : ℕ∞) := ⟨G.2.toNat, (ENat.natCast_toNat hGfin.2).symm⟩
    -- `(m'+1) x₁ + (n'+1) x₂ = (m₀+1) x₂`
    have hkey : (m' + 1) • x₁ + (n' + 1) • x₂ = (m₀ + 1) • x₂ := by
      have hzval : z = m' • x₁ + n' • x₂ := by
        rw [← hG, eval, hm', hn', ecmul_natCast, ecmul_natCast]
      rw [succ_nsmul x₁ m', succ_nsmul x₂ n', succ_nsmul x₂ m₀, ← hz, hzval]
      abel
    have hmT : (m₀ + 1) • x₂ ∈ add((x₁ + x₂)) := addOf_nsmul_mem hx₂T _
    refine IsBraided.of_levels (Sum.inl (ULift.up 0))
      (Sum.elim (fun j => j.down / (m' + 1)) (fun j => j.down / (n' + 1)))
      (Sum.elim (fun j => j.down) (fun j => j.down / (m₀ + 1)))
      (fun k => finite_fiber_elim (finite_nats_div (Nat.succ_pos m') k)
        (finite_nats_div (Nat.succ_pos n') k))
      (fun k => finite_fiber_elim (finite_nats_eq k) (finite_nats_div (Nat.succ_pos m₀) k))
      (fun _ => ⟨(m₀ + 1) • x₂, hmT⟩) (fun _ => 0) rfl (fun k => ?_) (fun k => ?_)
    · refine Subtype.ext ?_
      rw [coe_finsum_mem x₁ x₂
          (finite_fiber_elim (finite_nats_div (Nat.succ_pos m') k)
            (finite_nats_div (Nat.succ_pos n') k)) _ hFm,
        finsum_fiber_const (a := x₁) (b := x₂) (finite_nats_div (Nat.succ_pos m') k)
          (finite_nats_div (Nat.succ_pos n') k) _
          (fun j _ => by rw [familyOfForm_inl]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ)))
          (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        ncard_nats_div (Nat.succ_pos m') k, ncard_nats_div (Nat.succ_pos n') k]
      show (m' + 1) • x₁ + (n' + 1) • x₂ = ((0 : ↥(add((x₁ + x₂)))) : H)
        + (m₀ + 1) • x₂
      rw [hkey]
      exact (zero_add _).symm
    · refine Subtype.ext ?_
      rw [coe_finsum_mem x₁ x₂
          (finite_fiber_elim (finite_nats_eq k) (finite_nats_div (Nat.succ_pos m₀) k)) _ hGm,
        finsum_fiber_const (a := (0 : H)) (b := x₂) (finite_nats_eq k)
          (finite_nats_div (Nat.succ_pos m₀) k) _
          (fun j _ => by rw [familyOfForm_inl]; exact if_neg (by simp))
          (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        ncard_nats_eq k, ncard_nats_div (Nat.succ_pos m₀) k, smul_zero, zero_add]
      show (m₀ + 1) • x₂ = ((0 : ↥(add((x₁ + x₂)))) : H) + (m₀ + 1) • x₂
      exact (zero_add _).symm
  -- **the case `α = A` finite**: the level-`0` block carries the `A` copies of `x₁`
  obtain ⟨A, rfl⟩ : ∃ A : ℕ, α = (A : ℕ∞) := ⟨α.toNat, (ENat.natCast_toNat hα).symm⟩
  set n : ℕ := A * m₀ + 1 with hndef
  set t : H := A • z + x₂ with htdef
  have hnt : A • x₁ + t = n • x₂ := by
    rw [htdef, hndef, ← add_assoc, ← smul_add, hz, smul_smul, succ_nsmul]
  have hAT : A • x₁ ∈ add((x₁ + x₂)) := addOf_nsmul_mem hx₁T _
  have htT : t ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (addOf_nsmul_mem hx₂T n) t (A • x₁)
      (by rw [← hnt]; exact add_comm _ _)
  have hnpos : 0 < n := Nat.succ_pos _
  refine IsBraided.of_levels (Sum.inl (ULift.up 0))
    (Sum.elim (fun j => if j.down < A then 0 else (j.down - A) + 1) (fun j => j.down / n + 1))
    (Sum.elim (fun j => j.down) (fun j => j.down / n))
    (fun k => ?_) (fun k => finite_fiber_elim (finite_nats_eq k) (finite_nats_div hnpos k))
    (fun _ => ⟨A • x₁, hAT⟩) (fun k => if k = 0 then 0 else ⟨t, htT⟩) (if_pos rfl)
    (fun k => ?_) (fun k => ?_)
  · rcases k with _ | K
    · exact finite_fiber_elim (by rw [levelA_fiber_zero]; exact finite_nats_lt A)
        (by rw [divsucc_fiber_zero]; exact Set.finite_empty)
    · exact finite_fiber_elim (by rw [levelA_fiber_succ]; exact finite_nats_eq (A + K))
        (by rw [divsucc_fiber_succ]; exact finite_nats_div hnpos K)
  · rcases k with _ | K
    · refine Subtype.ext ?_
      have hf : {j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = 0}.Finite := by
        rw [levelA_fiber_zero]; exact finite_nats_lt A
      have hg : {j : Nats.{u} | j.down / n + 1 = 0}.Finite := by
        rw [divsucc_fiber_zero]; exact Set.finite_empty
      rw [coe_finsum_mem x₁ x₂ (finite_fiber_elim hf hg) _ hFm,
        finsum_fiber_const (a := x₁) (b := x₂) hf hg _
          (fun j hj => by
            rw [levelA_fiber_zero] at hj
            rw [familyOfForm_inl]
            refine if_pos ?_
            show ((j.down : ℕ) : ℕ∞) < ((A : ℕ) : ℕ∞)
            exact_mod_cast (hj : (j.down : ℕ) < A))
          (fun j hj => by rw [divsucc_fiber_zero] at hj; exact absurd hj (Set.notMem_empty j)),
        show ({j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = 0}).ncard = A by
          rw [levelA_fiber_zero]; exact ncard_nats_lt A,
        show ({j : Nats.{u} | j.down / n + 1 = 0}).ncard = 0 by
          rw [divsucc_fiber_zero]; exact Set.ncard_empty _,
        zero_smul, add_zero]
      show A • x₁ = ((if (0 : ℕ) = 0 then (0 : ↥(add((x₁ + x₂))))
        else ⟨t, htT⟩ : ↥(add((x₁ + x₂)))) : H) + A • x₁
      rw [if_pos rfl]
      exact (zero_add _).symm
    · refine Subtype.ext ?_
      have hf : {j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = K + 1}.Finite := by
        rw [levelA_fiber_succ]; exact finite_nats_eq (A + K)
      have hg : {j : Nats.{u} | j.down / n + 1 = K + 1}.Finite := by
        rw [divsucc_fiber_succ]; exact finite_nats_div hnpos K
      rw [coe_finsum_mem x₁ x₂ (finite_fiber_elim hf hg) _ hFm,
        finsum_fiber_const (a := (0 : H)) (b := x₂) hf hg _
          (fun j hj => by
            rw [levelA_fiber_succ] at hj
            rw [familyOfForm_inl]
            refine if_neg ?_
            show ¬ (((j.down : ℕ) : ℕ∞) < ((A : ℕ) : ℕ∞))
            have hja : (j.down : ℕ) = A + K := hj
            rw [hja]
            exact_mod_cast Nat.not_lt.mpr (Nat.le_add_right A K))
          (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        show ({j : Nats.{u} | (if j.down < A then 0 else (j.down - A) + 1) = K + 1}).ncard = 1 by
          rw [levelA_fiber_succ]; exact ncard_nats_eq (A + K),
        show ({j : Nats.{u} | j.down / n + 1 = K + 1}).ncard = n by
          rw [divsucc_fiber_succ]; exact ncard_nats_div hnpos K,
        smul_zero, zero_add]
      show n • x₂ = ((if K + 1 = 0 then (0 : ↥(add((x₁ + x₂))))
        else ⟨t, htT⟩ : ↥(add((x₁ + x₂)))) : H) + A • x₁
      rw [if_neg (Nat.succ_ne_zero K)]
      show n • x₂ = t + A • x₁
      rw [← hnt]
      exact add_comm _ _
  · refine Subtype.ext ?_
    rw [coe_finsum_mem x₁ x₂ (finite_fiber_elim (finite_nats_eq k) (finite_nats_div hnpos k)) _ hGm,
      finsum_fiber_const (a := (0 : H)) (b := x₂) (finite_nats_eq k) (finite_nats_div hnpos k) _
        (fun j _ => by rw [familyOfForm_inl]; exact if_neg (by simp))
        (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
      ncard_nats_eq k, ncard_nats_div hnpos k, smul_zero, zero_add]
    show n • x₂ = ((if k + 1 = 0 then (0 : ↥(add((x₁ + x₂))))
      else ⟨t, htT⟩ : ↥(add((x₁ + x₂)))) : H) + A • x₁
    rw [if_neg (Nat.succ_ne_zero k)]
    show n • x₂ = t + A • x₁
    rw [← hnt]
    exact add_comm _ _

/-- **Lemma 5.2(3)**: if `x₁ ∈ add x₂` and no element has both a finite and an infinite form, then
`α X₁ + ℵ₀ X₂` and `β X₁ + ℵ₀ X₂` are braided, for all `α, β ≤ ℵ₀`.

As in the paper, symmetry and transitivity of the braiding relation (Lemma 3.8) reduce this to the
case `β = 0`, which is `braidedForms_of_top`. -/
theorem lemma_5_2_three (hmem : x₁ ∈ add(x₂)) (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H)) (α β : ℕ∞)
    (hFm : ∀ n, familyOfForm x₁ x₂ (α, ⊤) n ∈ add((x₁ + x₂)))
    (hGm : ∀ n, familyOfForm x₁ x₂ (β, ⊤) n ∈ add((x₁ + x₂))) :
    BraidedForms x₁ x₂ (α, ⊤) (β, ⊤) hFm hGm := by

  have hZm : ∀ n, familyOfForm x₁ x₂ ((0 : ℕ∞), ⊤) n ∈ add((x₁ + x₂)) :=
    fun n => familyOfForm_mem x₁ x₂ _ n
  exact IsBraided.trans_aleph0 (braidedForms_of_top x₁ x₂ hmem hmix hgen α hFm hZm)
    (IsBraided.symm (braidedForms_of_top x₁ x₂ hmem hmix hgen β hGm hZm))

/-! ### Extra bookkeeping for Lemma 5.2(4) -/

/-- The coercion `add (x₁ + x₂) → H` commutes with `nsmul`. -/
theorem coe_nsmul_addOf (k : ℕ) (a : ↥(add((x₁ + x₂)))) :

    ((k • a : ↥(add((x₁ + x₂)))) : H) = k • (a : H) := by

  induction k with
  | zero => rw [zero_nsmul, zero_nsmul]; rfl
  | succ p hp => rw [succ_nsmul, succ_nsmul, ← hp]; rfl

/-- The slots at which the family of `c X₁ + ℵ₀ X₂` takes the value `x₁`. -/
def oneSlots (c : ℕ) : Set FormIdx.{u} := Sum.inl '' {j : Nats.{u} | j.down < c}

theorem finite_oneSlots (c : ℕ) : (oneSlots.{u} c).Finite := (finite_nats_lt c).image _

theorem ncard_oneSlots (c : ℕ) : (oneSlots.{u} c).ncard = c := by
  rw [oneSlots, Set.ncard_image_of_injective _ Sum.inl_injective]
  exact ncard_nats_lt c

theorem familyOfForm_eq_of_mem_oneSlots {c : ℕ} {i : FormIdx.{u}} (hi : i ∈ oneSlots.{u} c) :
    familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i = x₁ := by
  obtain ⟨j, hj, rfl⟩ := hi
  rw [familyOfForm_inl]
  refine if_pos ?_
  show ((j.down : ℕ) : ℕ∞) < ((c : ℕ) : ℕ∞)
  exact_mod_cast hj

theorem familyOfForm_eq_of_notMem_oneSlots {c : ℕ} {i : FormIdx.{u}} (hi : i ∉ oneSlots.{u} c) :
    familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i = x₂ ∨ familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i = 0 := by
  rcases i with j | j
  · refine Or.inr ?_
    rw [familyOfForm_inl]
    refine if_neg ?_
    show ¬ (((j.down : ℕ) : ℕ∞) < ((c : ℕ) : ℕ∞))
    intro h
    exact hi ⟨j, by exact_mod_cast h, rfl⟩
  · refine Or.inl ?_
    rw [familyOfForm_inr]
    exact if_pos (WithTop.coe_lt_top (j.down : ℕ))

/-- **A block sum of the family of `c X₁ + ℵ₀ X₂`** over a finite set of slots containing all the
`x₁`-slots is `c x₁ + p x₂` for some finite `p`: the `x₁`-slots contribute exactly `c` copies and
every other slot carries `x₂` or `0`. -/
theorem exists_block_value {c : ℕ} {S : Set FormIdx.{u}} (hS : S.Finite)
    (hsub : oneSlots.{u} c ⊆ S)
    (hFm : ∀ i, familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i ∈ add((x₁ + x₂)))
    (hx₁T : x₁ ∈ add((x₁ + x₂)))
    (hx₂T : x₂ ∈ add((x₁ + x₂))) :

    ∃ p : ℕ, (∑ᶠ i ∈ S, (⟨familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i, hFm i⟩ :
        ↥(add((x₁ + x₂)))))
      = c • (⟨x₁, hx₁T⟩ : ↥(add((x₁ + x₂))))
        + p • (⟨x₂, hx₂T⟩ : ↥(add((x₁ + x₂)))) := by
  classical

  have hsplit : S = oneSlots.{u} c ∪ (S \ oneSlots.{u} c) := (Set.union_sdiff_cancel hsub).symm
  have hdisj : Disjoint (oneSlots.{u} c) (S \ oneSlots.{u} c) := Set.disjoint_sdiff_right
  have hdfin : (S \ oneSlots.{u} c).Finite := hS.subset Set.sdiff_subset
  obtain ⟨p, hp⟩ := exists_nsmul_finsum hdfin
    (fun i => (⟨familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i, hFm i⟩ :
      ↥(add((x₁ + x₂)))))
    (⟨x₂, hx₂T⟩ : ↥(add((x₁ + x₂))))
    (fun i (hi : i ∈ S \ oneSlots.{u} c) => by
      rcases familyOfForm_eq_of_notMem_oneSlots x₁ x₂ hi.2 with h | h
      · exact ⟨1, by rw [one_smul]; exact Subtype.ext h⟩
      · exact ⟨0, by rw [zero_smul]; exact Subtype.ext h⟩)
  refine ⟨p, ?_⟩
  rw [hsplit, finsum_mem_union hdisj (finite_oneSlots c) hdfin, hp,
    finsum_mem_congr rfl (fun i hi => (Subtype.ext (familyOfForm_eq_of_mem_oneSlots x₁ x₂ hi) :
      (⟨familyOfForm x₁ x₂ ((c : ℕ∞), ⊤) i, hFm i⟩ :
        ↥(add((x₁ + x₂)))) = ⟨x₁, hx₁T⟩)),
    finsum_mem_const_finite (finite_oneSlots c), ncard_oneSlots]

/-- **Lemma 5.2(4)**: for incomparable generators, a braiding of `m X₁ + ℵ₀ X₂` with
`n X₁ + ℵ₀ X₂` forces a finite relation `m x₁ + k x₂ = n x₁ + k' x₂`.

Paper proof, adapted to the block structure `ι × ℕ` of `BraidingData` — where the positions form
countably many `ω`-chains rather than one well-order, so the paper's single cut `μ ≤ α` becomes a
*rectangle*: choose a finite set `A` of chains and a level `K` such that every one of the finitely
many `x₁`-slots of either family lies in some `I (a,k)` resp. `J (a,k)` with `a ∈ A`, `k ≤ K`.
`BraidingData.telescope` then gives

    n x₁ + q x₂ = m x₁ + p x₂ + Σ_{a ∈ A} v (a, K+1),

because each of the two rectangles is a finite set of slots containing all the `x₁`-slots of its
family (`exists_block_value`).  Finally `I (a, K+1)` contains no `x₁`-slot at all, so
`v (a,K+1) + u (a,K+1)` is a finite multiple of `x₂`; hence `v (a,K+1) ∈ add x₂`, so its form has
zero `X₁`-coefficient (`x₁ ∉ add x₂`) and finite `X₂`-coefficient (`NoMixedForms`, applied to that
finite multiple of `x₂`).

**The generation hypothesis `hgen` is needed**: it is a standing assumption of §5, and the last
step uses it to write `v (a,K+1)` in a form at all. -/
theorem lemma_5_2_four (hmem : x₁ ∉ add(x₂)) (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H)) (m n : ℕ)
    (hFm : ∀ i, familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i ∈ add((x₁ + x₂)))
    (hGm : ∀ i, familyOfForm x₁ x₂ ((n : ℕ∞), ⊤) i ∈ add((x₁ + x₂)))
    (hbr : BraidedForms x₁ x₂ ((m : ℕ∞), ⊤) ((n : ℕ∞), ⊤) hFm hGm) :
    ∃ k k' : ℕ, eval x₁ x₂ ((m : ℕ∞), (k : ℕ∞)) = eval x₁ x₂ ((n : ℕ∞), (k' : ℕ∞)) := by
  classical

  have hx₁T : x₁ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  obtain ⟨D⟩ := hbr
  -- the finitely many `x₁`-slots of the two families, and the blocks holding them
  have hWfin : (oneSlots.{u} m ∪ oneSlots.{u} n).Finite :=
    (finite_oneSlots m).union (finite_oneSlots n)
  have hPPfin : ((fun i => IsBraided.blockOf D.I D.I_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
      ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)).Finite :=
    (hWfin.image _).union (hWfin.image _)
  have hAfin : (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
      ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))).Finite :=
    hPPfin.image _
  obtain ⟨K, hK⟩ := (hPPfin.image Prod.snd).bddAbove
  -- disjointness of the rectangle pieces
  have hdisjK : ∀ (P : FormIdx.{u} × ℕ → Set FormIdx.{u}),
      (∀ p q, p ≠ q → Disjoint (P p) (P q)) → ∀ a : FormIdx.{u},
        ((↑(Finset.range (K + 1)) : Set ℕ)).PairwiseDisjoint (fun k => P (a, k)) := by
    intro P hP a k _ k' _ hkk'
    exact hP (a, k) (a, k') fun h => hkk' (congrArg Prod.snd h)
  have hdisjA : ∀ (P : FormIdx.{u} × ℕ → Set FormIdx.{u}),
      (∀ p q, p ≠ q → Disjoint (P p) (P q)) →
      (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
        ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))).PairwiseDisjoint
        (fun a => ⋃ k ∈ (↑(Finset.range (K + 1)) : Set ℕ), P (a, k)) := by
    intro P hP a _ a' _ haa'
    refine Set.disjoint_left.mpr ?_
    intro i hi hi'
    obtain ⟨k, -, hk⟩ := Set.mem_iUnion₂.mp hi
    obtain ⟨k', -, hk'⟩ := Set.mem_iUnion₂.mp hi'
    exact Set.disjoint_left.mp (hP (a, k) (a', k') fun h => haa' (congrArg Prod.fst h)) hk hk'
  -- the two rectangles, as finite sets of slots
  have hrect : ∀ (P : FormIdx.{u} × ℕ → Set FormIdx.{u}),
      (∀ p, #(P p) < (ℵ₀ : Cardinal.{u})) →
      (⋃ a ∈ (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
        ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))),
        ⋃ k ∈ (↑(Finset.range (K + 1)) : Set ℕ), P (a, k)).Finite := by
    intro P hP
    exact hAfin.biUnion fun a _ => (Finset.range (K + 1)).finite_toSet.biUnion
      fun k _ => Cardinal.lt_aleph0_iff_set_finite.mp (hP (a, k))
  -- the rectangle sums are the double sums the telescoping identity speaks about
  have hrectsum : ∀ (P : FormIdx.{u} × ℕ → Set FormIdx.{u})
      (hPd : ∀ p q, p ≠ q → Disjoint (P p) (P q)) (hPs : ∀ p, #(P p) < (ℵ₀ : Cardinal.{u}))
      (f : FormIdx.{u} → ↥(add((x₁ + x₂)))),
      (∑ᶠ i ∈ (⋃ a ∈ (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) ''
          (oneSlots.{u} m ∪ oneSlots.{u} n)
          ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))),
          ⋃ k ∈ (↑(Finset.range (K + 1)) : Set ℕ), P (a, k)), f i)
        = ∑ᶠ a ∈ (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) ''
            (oneSlots.{u} m ∪ oneSlots.{u} n)
            ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))),
            ∑ k ∈ Finset.range (K + 1),
              LMonoid.lsumOf (lam := (ℵ₀ : Cardinal.{u})) (hPs (a, k)) (fun i : P (a, k) => f i) := by
    intro P hPd hPs f
    rw [finsum_mem_biUnion (hdisjA P hPd) hAfin
      (fun a _ => (Finset.range (K + 1)).finite_toSet.biUnion
        fun k _ => Cardinal.lt_aleph0_iff_set_finite.mp (hPs (a, k)))]
    refine finsum_mem_congr rfl fun a _ => ?_
    rw [finsum_mem_biUnion (hdisjK P hPd a) (Finset.range (K + 1)).finite_toSet
      (fun k _ => Cardinal.lt_aleph0_iff_set_finite.mp (hPs (a, k))), finsum_mem_coe_finset]
    exact Finset.sum_congr rfl fun k _ => (LMonoid.lsumOf_eq_finsum (hPs (a, k)) f).symm
  -- the rectangles cover the `x₁`-slots
  have hcover : ∀ (P : FormIdx.{u} × ℕ → Set FormIdx.{u}) (hcov : (⋃ p, P p) = Set.univ),
      ((fun i => IsBraided.blockOf P hcov i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
        ⊆ (fun i => IsBraided.blockOf D.I D.I_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)
          ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n)) →
      ∀ c : ℕ, oneSlots.{u} c ⊆ oneSlots.{u} m ∪ oneSlots.{u} n →
      oneSlots.{u} c ⊆ ⋃ a ∈ (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) ''
        (oneSlots.{u} m ∪ oneSlots.{u} n)
        ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))),
        ⋃ k ∈ (↑(Finset.range (K + 1)) : Set ℕ), P (a, k) := by
    intro P hcov hsub c hc i hi
    have hpp : IsBraided.blockOf P hcov i ∈ (fun i => IsBraided.blockOf D.I D.I_cover i) ''
        (oneSlots.{u} m ∪ oneSlots.{u} n)
        ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n) :=
      hsub ⟨i, hc hi, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨(IsBraided.blockOf P hcov i).1, ⟨_, hpp, rfl⟩, ?_⟩
    refine Set.mem_iUnion₂.mpr ⟨(IsBraided.blockOf P hcov i).2, ?_, ?_⟩
    · simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (hK ⟨_, hpp, rfl⟩)
    · rw [Prod.mk.eta]
      exact IsBraided.mem_blockOf P hcov i
  -- the two block values
  obtain ⟨p, hp⟩ := exists_block_value x₁ x₂ (hrect D.I D.I_small)
    (hcover D.I D.I_cover Set.subset_union_left m Set.subset_union_left) hFm hx₁T hx₂T
  obtain ⟨q, hq⟩ := exists_block_value x₁ x₂ (hrect D.J D.J_small)
    (hcover D.J D.J_cover Set.subset_union_right n Set.subset_union_right) hGm hx₁T hx₂T
  -- the surviving `v`-terms are finite multiples of `x₂`
  have hV : ∃ r : ℕ, (∑ᶠ a ∈ (Prod.fst '' ((fun i => IsBraided.blockOf D.I D.I_cover i) ''
      (oneSlots.{u} m ∪ oneSlots.{u} n)
      ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n))),
      D.v (a, K + 1)) = r • (⟨x₂, hx₂T⟩ : ↥(add((x₁ + x₂)))) := by
    refine exists_nsmul_finsum hAfin _ _ fun a _ => ?_
    -- no `x₁`-slot survives past level `K`
    have hno : ∀ i ∈ D.I (a, K + 1), familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i = x₂
        ∨ familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i = 0 := by
      intro i hi
      refine familyOfForm_eq_of_notMem_oneSlots x₁ x₂ fun hone => ?_
      have hb : IsBraided.blockOf D.I D.I_cover i = (a, K + 1) := IsBraided.blockOf_eq D.I_disjoint D.I_cover hi
      have hpp : IsBraided.blockOf D.I D.I_cover i ∈ (fun i => IsBraided.blockOf D.I D.I_cover i) ''
          (oneSlots.{u} m ∪ oneSlots.{u} n)
          ∪ (fun i => IsBraided.blockOf D.J D.J_cover i) '' (oneSlots.{u} m ∪ oneSlots.{u} n) :=
        Set.mem_union_left _ ⟨i, Set.mem_union_left _ hone, rfl⟩
      have := hK (Set.mem_image_of_mem Prod.snd hpp)
      rw [hb] at this
      omega
    -- so the block sums to a finite multiple of `x₂`
    obtain ⟨r', hr'⟩ := exists_nsmul_finsum
      (Cardinal.lt_aleph0_iff_set_finite.mp (D.I_small (a, K + 1)))
      (fun i => (⟨familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i, hFm i⟩ :
        ↥(add((x₁ + x₂)))))
      (⟨x₂, hx₂T⟩ : ↥(add((x₁ + x₂))))
      (fun i hi => by
        rcases hno i hi with h | h
        · exact ⟨1, by rw [one_smul]; exact Subtype.ext h⟩
        · exact ⟨0, by rw [zero_smul]; exact Subtype.ext h⟩)
    have hblock : D.v (a, K + 1) + D.u (a, K + 1)
        = r' • (⟨x₂, hx₂T⟩ : ↥(add((x₁ + x₂)))) := by
      rw [← hr', ← LMonoid.lsumOf_eq_finsum (D.I_small (a, K + 1))]
      exact (D.hI (a, K + 1)).symm
    -- read the equation in `H` and use that `x₁ ∉ add x₂`
    have hblockH : (D.v (a, K + 1) : H) + (D.u (a, K + 1) : H) = r' • x₂ := by
      have := congrArg Subtype.val hblock
      rwa [coe_nsmul_addOf x₁ x₂ r' ⟨x₂, hx₂T⟩] at this
    have hvadd : (D.v (a, K + 1) : H) ∈ add(x₂) :=
      ⟨(D.u (a, K + 1) : H), r', by rw [KMonoid.cmul_natCast]; exact hblockH⟩
    obtain ⟨F, hF⟩ := exists_form x₁ x₂ hgen ((D.v (a, K + 1) : H))
    have hF1 : F.1 = 0 := by
      by_contra hne
      obtain ⟨w, hw⟩ := self_addLe_ecmul hne x₁
      exact hmem ⟨w + ecmul F.2 x₂ + (D.u (a, K + 1) : H), r', by
        rw [KMonoid.cmul_natCast, ← hblockH, ← hF, eval, ← hw]
        abel⟩
    have hF2 : F.2 ≠ ⊤ := by
      intro htop
      obtain ⟨G, hG⟩ := exists_form x₁ x₂ hgen ((D.u (a, K + 1) : H))
      refine hmix (r' • x₂) ⟨⟨(0, (r' : ℕ∞)), ⟨by simp, by simp⟩, ?_⟩, ⟨(G.1, ⊤), Or.inr rfl, ?_⟩⟩
      · rw [eval, ecmul_zero, zero_add, ecmul_natCast]
      · have hu : ecmul (⊤ : ℕ∞) x₂ + ecmul G.2 x₂ = ecmul (⊤ : ℕ∞) x₂ := by
          rw [← ecmul_add, top_add]
        calc eval x₁ x₂ (G.1, ⊤) = ecmul G.1 x₁ + ecmul (⊤ : ℕ∞) x₂ := rfl
          _ = ecmul G.1 x₁ + (ecmul (⊤ : ℕ∞) x₂ + ecmul G.2 x₂) := by rw [hu]
          _ = ecmul (⊤ : ℕ∞) x₂ + (ecmul G.1 x₁ + ecmul G.2 x₂) := by abel
          _ = eval x₁ x₂ F + eval x₁ x₂ G := by
                rw [eval, eval, hF1, htop, ecmul_zero, zero_add]
          _ = (D.v (a, K + 1) : H) + (D.u (a, K + 1) : H) := by rw [hF, hG]
          _ = r' • x₂ := hblockH
    obtain ⟨g, hg⟩ : ∃ g : ℕ, F.2 = (g : ℕ∞) := ⟨F.2.toNat, (ENat.natCast_toNat hF2).symm⟩
    refine ⟨g, Subtype.ext ?_⟩
    rw [coe_nsmul_addOf x₁ x₂ g ⟨x₂, hx₂T⟩]
    show (D.v (a, K + 1) : H) = g • x₂
    rw [← hF, eval, hF1, hg, ecmul_zero, zero_add, ecmul_natCast]
  obtain ⟨r, hr⟩ := hV
  -- telescope, and read off the finite relation
  have htel := D.telescope hAfin K
  rw [← hrectsum D.J D.J_disjoint D.J_small
      (fun i => (⟨familyOfForm x₁ x₂ ((n : ℕ∞), ⊤) i, hGm i⟩ :
        ↥(add((x₁ + x₂))))),
    ← hrectsum D.I D.I_disjoint D.I_small
      (fun i => (⟨familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i, hFm i⟩ :
        ↥(add((x₁ + x₂))))),
    hp, hq, hr] at htel
  have htelH : n • x₁ + q • x₂ = m • x₁ + p • x₂ + r • x₂ := by
    have hc : ((n • (⟨x₁, hx₁T⟩ : ↥(add((x₁ + x₂)))) :
          ↥(add((x₁ + x₂)))) : H)
        + ((q • (⟨x₂, hx₂T⟩ : ↥(add((x₁ + x₂)))) :
          ↥(add((x₁ + x₂)))) : H)
        = ((m • (⟨x₁, hx₁T⟩ : ↥(add((x₁ + x₂)))) :
            ↥(add((x₁ + x₂)))) : H)
          + ((p • (⟨x₂, hx₂T⟩ : ↥(add((x₁ + x₂)))) :
            ↥(add((x₁ + x₂)))) : H)
          + ((r • (⟨x₂, hx₂T⟩ : ↥(add((x₁ + x₂)))) :
            ↥(add((x₁ + x₂)))) : H) := congrArg Subtype.val htel
    rwa [coe_nsmul_addOf x₁ x₂ n ⟨x₁, hx₁T⟩, coe_nsmul_addOf x₁ x₂ q ⟨x₂, hx₂T⟩,
      coe_nsmul_addOf x₁ x₂ m ⟨x₁, hx₁T⟩, coe_nsmul_addOf x₁ x₂ p ⟨x₂, hx₂T⟩,
      coe_nsmul_addOf x₁ x₂ r ⟨x₂, hx₂T⟩] at hc
  refine ⟨p + r, q, ?_⟩
  rw [eval, eval, ecmul_natCast, ecmul_natCast, ecmul_natCast, ecmul_natCast, add_nsmul,
    ← add_assoc, ← htelH]

/-- **`ℵ₀ x₂` absorbs any number of copies of `x₁`** as soon as `x₁ ∈ add x₂`: from `x₁ + z = n x₂`
one gets `β x₁ ≼ ℵ₀ x₁ ≼ ℵ₀ (n x₂) = ℵ₀ x₂`, and Lemma 2.8(2) (`add_cmul_top_eq`) turns a summand of
`ℵ₀ x₂` into an absorbed one.  The degenerate case `n = 0` forces `x₁ = 0` by reducedness. -/
theorem cmul_top_absorb (h : x₁ ∈ add(x₂)) (β : ℕ∞) :
    ℵ₀∙x₂ + ecmul β x₁
      = ℵ₀∙x₂ := by
  obtain ⟨z, n, hzn⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `0 · x₂ = 0`, so `x₁ = 0` and there is nothing to absorb
    have h0 : x₁ + z = 0 := by
      rw [hzn, KMonoid.cmul_congr (by rw [Nat.cast_zero] : ((0 : ℕ) : Cardinal.{u}) = 0) _ zero_le,
        KMonoid.cmul_zero_cardinal]
    rw [(KMonoid.isConical (ℵ₀ : Cardinal.{u}) H x₁ z h0).1, ecmul, KMonoid.cmul_zero, add_zero]
  · -- `ℵ₀ · n = ℵ₀`
    have hmul : (ℵ₀ : Cardinal.{u}) * ((n : ℕ) : Cardinal.{u}) = ℵ₀ :=
      Cardinal.mul_eq_left le_rfl (le_of_lt Cardinal.natCast_lt_aleph0)
        (by exact_mod_cast hn.ne')
    have hnκ : ((n : ℕ) : Cardinal.{u}) ≤ ℵ₀ := le_of_lt Cardinal.natCast_lt_aleph0
    -- `ℵ₀ x₁ + ℵ₀ z = ℵ₀ (x₁ + z) = ℵ₀ (n x₂) = ℵ₀ x₂`
    have hstep : ℵ₀∙x₁ + ℵ₀∙z
        = ℵ₀∙x₂ := by
      rw [← KMonoid.cmul_top_distrib, hzn, KMonoid.cmul_cmul le_rfl hnκ (le_of_eq hmul),
        KMonoid.cmul_congr hmul (le_of_eq hmul) le_rfl x₂]
    -- so `β x₁ ≼ ℵ₀ x₁ ≼ ℵ₀ x₂`
    obtain ⟨w, hw⟩ : ecmul β x₁ ≼ ℵ₀∙x₂ :=
      AddLe.trans
        (KMonoid.cmul_le_cmul (Cardinal.ofENat_le_aleph0 β) le_rfl
          (Cardinal.ofENat_le_aleph0 β) x₁)
        ⟨ℵ₀∙z, hstep⟩
    rw [add_comm]
    exact KMonoid.add_cmul_top_eq hw

/-- **Lemma 5.2(5)**: if `H` is braided over `add (x₁ + x₂)`, then `x₁ ∈ add x₂` exactly when
`ℵ₀ (x₁ + x₂) = ℵ₀ x₂`.

Forward is `cmul_top_absorb`: `ℵ₀ x₂` swallows `ℵ₀ x₁`.

Backward is where the work is.  The paper's "we conclude that there exist positive integers `m`,
`n`" hides a block induction, which the formal proof runs explicitly.  Braid the constant families
`(x₁ + x₂)` and `(x₂)` — they have the same `ℵ₀`-sum by hypothesis — and let `k` be the least
level of the block `a` whose `I`-piece is nonempty.  Below `k` the `I`-pieces are empty, so
`v + u = 0` there and reducedness of `H` kills both; the `J`-equation one level down then reads
`v (a,k) = r x₂` with `r = #J (a,k-1)` finite (and `v (a,0) = 0` when `k = 0`).  The two braiding
equations at level `k` now give

    m (x₁ + x₂) = r x₂ + u (a,k)    and    u (a,k) + v (a,k+1) = s x₂,

with `m = #I (a,k) ≥ 1` and `s = #J (a,k)`, so `x₁ ≼ m (x₁ + x₂) ≼ (r + s) x₂`. -/
theorem lemma_5_2_five
    (hbr :
      IsBraidedOver ℵ₀ ℵ₀ ↥(add((x₁ + x₂))) H le_rfl (fun y => (y : H))) :
    x₁ ∈ add(x₂) ↔
      ℵ₀∙(x₁ + x₂) = ℵ₀∙x₂ := by
  classical

  constructor
  · -- `ℵ₀ (x₁ + x₂) = ℵ₀ x₁ + ℵ₀ x₂ = ℵ₀ x₂`
    intro h
    rw [KMonoid.cmul_top_distrib, add_comm]
    have habs := cmul_top_absorb x₁ x₂ h ⊤
    rwa [ecmul_top] at habs
  intro heq
  -- the two constant families, in `add (x₁ + x₂)`
  have hx12 : x₁ + x₂ ∈ add((x₁ + x₂)) := KMonoid.self_mem_addOf _
  have hx2 : x₂ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ hx12 x₂ x₁ (add_comm x₁ x₂)
  have hsum : (KMonoid.ksum (κ := ℵ₀) fun _ : Idx (ℵ₀ : Cardinal.{u}) => x₁ + x₂)
      = KMonoid.ksum (κ := ℵ₀) fun _ : Idx (ℵ₀ : Cardinal.{u}) => x₂ := by
    rw [ksum_const, ksum_const]; exact heq
  obtain ⟨D⟩ := hbr.braided (fun _ => ⟨x₁ + x₂, hx12⟩) (fun _ => ⟨x₂, hx2⟩) hsum
  -- the braiding equations, read in `H` (the coercion of a `λ⁻`-sum *is* the ambient sum)
  have hIcoe : ∀ q : Idx (ℵ₀ : Cardinal.{u}) × ℕ,
      KMonoid.sumOf (κ := ℵ₀) (D.I_small q).le (fun _ : D.I q => x₁ + x₂)
        = ((D.v q : H) + (D.u q : H)) := fun q => congrArg Subtype.val (D.hI q)
  have hJcoe : ∀ (b : Idx (ℵ₀ : Cardinal.{u})) (j : ℕ),
      KMonoid.sumOf (κ := ℵ₀) (D.J_small (b, j)).le (fun _ : D.J (b, j) => x₂)
        = ((D.v (b, j + 1) : H) + (D.u (b, j) : H)) :=
    fun b j => congrArg Subtype.val (D.hJ (b, j))
  -- some block has a nonempty `I`-piece; take the least level of that block at which it does
  obtain ⟨i₀⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  obtain ⟨⟨a, k₀⟩, hp⟩ : ∃ q, i₀ ∈ D.I q :=
    Set.mem_iUnion.mp (by rw [D.I_cover]; trivial)
  have hex : ∃ k : ℕ, (D.I (a, k)).Nonempty := ⟨k₀, ⟨i₀, hp⟩⟩
  obtain ⟨k, hk, hlow⟩ : ∃ k : ℕ, (D.I (a, k)).Nonempty ∧ ∀ j < k, D.I (a, j) = ∅ :=
    ⟨Nat.find hex, Nat.find_spec hex,
      fun j hj => Set.not_nonempty_iff_eq_empty.mp (Nat.find_min hex hj)⟩
  -- below level `k` both braiding families vanish, by reducedness
  have hzero : ∀ j < k, (D.v (a, j) : H) = 0 ∧ (D.u (a, j) : H) = 0 := by
    intro j hj
    obtain ⟨m, hm, hmsum⟩ := sumOf_const_finite (D.I_small (a, j)) (x₁ + x₂)
    have hm0 : m = 0 := by
      have : ((m : ℕ) : Cardinal.{u}) = 0 := by rw [← hm, hlow j hj]; simp
      exact_mod_cast this
    refine KMonoid.isConical (ℵ₀ : Cardinal.{u}) H _ _ ?_
    rw [← hIcoe (a, j), hmsum, hm0, zero_nsmul]
  -- so `v (a,k)` is a finite multiple of `x₂`
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (D.v (a, k) : H) = r • x₂ := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact ⟨0, by rw [D.v_limit a, zero_nsmul]; rfl⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    obtain ⟨s, _, hssum⟩ := sumOf_const_finite (D.J_small (a, j)) x₂
    have hj := hJcoe a j
    rw [hssum, (hzero j (Nat.lt_succ_self j)).2, add_zero] at hj
    exact ⟨s, hj.symm⟩
  -- and `u (a,k)` is a summand of a finite multiple of `x₂`
  obtain ⟨s, _, hssum⟩ := sumOf_const_finite (D.J_small (a, k)) x₂
  have hu : (D.u (a, k) : H) + (D.v (a, k + 1) : H) = s • x₂ := by
    have h := hJcoe a k
    rw [hssum] at h
    rw [h]
    exact add_comm _ _
  -- the `I`-equation at level `k`, with `m ≥ 1` copies of `x₁ + x₂`
  obtain ⟨m, hmcard, hmsum⟩ := sumOf_const_finite (D.I_small (a, k)) (x₁ + x₂)
  have hIeq : m • (x₁ + x₂) = r • x₂ + (D.u (a, k) : H) := by
    rw [← hmsum, hIcoe (a, k), hr]
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [h0, Nat.cast_zero] at hmcard
    exact Cardinal.mk_ne_zero_iff.mpr hk.to_subtype hmcard
  -- read off `x₁ + z = (r + s) x₂`
  refine ⟨x₂ + m' • (x₁ + x₂) + (D.v (a, k + 1) : H), r + s, ?_⟩
  have hsplit : x₁ + (x₂ + m' • (x₁ + x₂)) = (m' + 1) • (x₁ + x₂) := by
    rw [succ_nsmul, ← add_assoc]
    exact add_comm _ _
  rw [KMonoid.cmul_natCast, add_nsmul]
  calc x₁ + (x₂ + m' • (x₁ + x₂) + (D.v (a, k + 1) : H))
      = (x₁ + (x₂ + m' • (x₁ + x₂))) + (D.v (a, k + 1) : H) := (add_assoc _ _ _).symm
    _ = (m' + 1) • (x₁ + x₂) + (D.v (a, k + 1) : H) := by rw [hsplit]
    _ = (r • x₂ + (D.u (a, k) : H)) + (D.v (a, k + 1) : H) := by rw [hIeq]
    _ = r • x₂ + ((D.u (a, k) : H) + (D.v (a, k + 1) : H)) := add_assoc _ _ _
    _ = r • x₂ + s • x₂ := by rw [hu]

end Lemma52

end TwoGen

end KappaMonoid
