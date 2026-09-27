/-
**Section 5: Theorem 5.3**, the main result of the section: a non-cyclic `ℵ₀`-monoid on two
generators is `V^{ℵ₀}(R)` for a hereditary ring exactly when conditions (i), (ii) and (iii) hold
for both orderings of the generators.

Forward (`theorem_5_3_forward`): Lemma 5.1 gives the braiding, (iii) is Lemma 5.2(1), (ii) is Lemma
5.2(4), and (i) is the counting argument `mem_addOf_of_braidedForms_top`.

Backward (`theorem_5_3_backward`): `braidedForms_of_conditions` runs the paper's four-case split on
forms, and `exists_braided_form` reduces an *arbitrary* family over `add (x₁ + x₂)` to a form family
— the step the paper compresses into "hence `add (x₁ + x₂) = ⟨x₁, x₂⟩`".  Corollary 4.7(1) then
realises `H`, which is where the Bergman–Dicks theorem enters.
-/
import KappaMonoid.TwoGen.Lemma51
import KappaMonoid.TwoGen.Lemma52

universe u v

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

-- The cardinal universe is pinned to `H`'s: `§5` fixes `κ = ℵ₀` and works in a single universe, and
-- leaving `ℵ₀`'s universe to be auto-bound makes two occurrences in one statement refer to
-- *different* universes (trap 5 of `CLAUDE.md`).
variable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]

/-! ## Theorem 5.3 (`hereditarycasecor`)

The main result of the section. -/

section Theorem53

variable (x₁ x₂ : H)

/-- Condition (i) of Theorem 5.3, for the ordered pair `(a, b)` of generators. -/
def Cond1 (a b : H) : Prop :=
  ∀ n : ℕ, n • a + ℵ₀∙b = ℵ₀∙a + ℵ₀∙b → ℵ₀∙b = ℵ₀∙a + ℵ₀∙b ∧ a ∈ add(b)

/-- Condition (ii) of Theorem 5.3, for the ordered pair `(a, b)` of generators. -/
def Cond2 (a b : H) : Prop :=
  a ∉ add(b) →
    ∀ m n : ℕ, eval a b ((m : ℕ∞), ⊤) = eval a b ((n : ℕ∞), ⊤) →
      ∃ k k' : ℕ, eval a b ((m : ℕ∞), (k : ℕ∞)) = eval a b ((n : ℕ∞), (k' : ℕ∞))

/-! ### Moving between `FormIdx` and `Idx ℵ₀`

`BraidedForms` compares families indexed by `FormIdx`, while `IsBraidedOver.braided` speaks about
families indexed by `Idx ℵ₀`.  Both index types are countable, and `IsBraided.comp_equiv` moves a
braiding across the identification. -/

/-- A fixed identification of the slots of a form with the index type of an `ℵ₀`-sum. -/
noncomputable def formIdxEquiv : FormIdx.{u} ≃ Idx (ℵ₀ : Cardinal.{u}) :=
  (Cardinal.eq.mp (mk_formIdx.{u}.trans (mk_Idx (ℵ₀ : Cardinal.{u})).symm)).some

/-- The `ℵ₀`-sum of a form's family, read along `formIdxEquiv`, is the element the form
represents. -/
theorem ksum_familyOfForm (F : Form) :
    KMonoid.ksum (κ := ℵ₀) (fun i => familyOfForm x₁ x₂ F (formIdxEquiv.{u}.symm i))
      = eval x₁ x₂ F := by
  rw [← sumOf_familyOfForm x₁ x₂ F, ← KMonoid.sumOf_Idx]
  exact (KMonoid.sumOf_equiv mk_formIdx_le_aleph0 (le_of_eq (mk_Idx _))
    formIdxEquiv.{u}.symm (familyOfForm x₁ x₂ F)).symm

/-- **Two forms of the same element are braided**, as soon as `H` is braided over `add (x₁ + x₂)`.
This is what turns the hypothesis of Theorem 5.3's forward direction into the input of Lemma
5.2. -/
theorem braidedForms_of_braidedOver
    (hbr :
      IsBraidedOver ℵ₀ ℵ₀ ↥(add((x₁ + x₂))) H (Order.le_succ ℵ₀) (fun y => (y : H)))
    (F G : Form) (heq : eval x₁ x₂ F = eval x₁ x₂ G)
    (hFm : ∀ i, familyOfForm x₁ x₂ F i ∈ add((x₁ + x₂)))
    (hGm : ∀ i, familyOfForm x₁ x₂ G i ∈ add((x₁ + x₂))) :
    BraidedForms x₁ x₂ F G hFm hGm := by

  have hsum : (KMonoid.ksum (κ := ℵ₀) fun i =>
        ((⟨familyOfForm x₁ x₂ F (formIdxEquiv.{u}.symm i), hFm _⟩ :
          ↥(add((x₁ + x₂)))) : H))
      = KMonoid.ksum (κ := ℵ₀) fun i =>
        ((⟨familyOfForm x₁ x₂ G (formIdxEquiv.{u}.symm i), hGm _⟩ :
          ↥(add((x₁ + x₂)))) : H) := by
    rw [show (fun i => ((⟨familyOfForm x₁ x₂ F (formIdxEquiv.{u}.symm i), hFm _⟩ :
        ↥(add((x₁ + x₂)))) : H))
      = (fun i => familyOfForm x₁ x₂ F (formIdxEquiv.{u}.symm i)) from rfl,
      show (fun i => ((⟨familyOfForm x₁ x₂ G (formIdxEquiv.{u}.symm i), hGm _⟩ :
        ↥(add((x₁ + x₂)))) : H))
      = (fun i => familyOfForm x₁ x₂ G (formIdxEquiv.{u}.symm i)) from rfl,
      ksum_familyOfForm, ksum_familyOfForm]
    exact heq
  have h := (hbr.braided _ _ hsum).comp_equiv formIdxEquiv.{u}
  show IsBraided (ℵ₀ : Cardinal.{u}) _ _
  convert h using 2 <;> simp

/-- `NoMixedForms` does not depend on the order of the generators. -/
theorem eval_swap (a b : H) (F : Form) : eval a b F = eval b a (F.2, F.1) := by
  rw [eval, eval, add_comm]

/-- Having no mixed forms does not depend on the order of the two generators. -/
theorem noMixedForms_swap (h : NoMixedForms x₁ x₂) : NoMixedForms x₂ x₁ := by
  rintro y ⟨⟨F, hF, hFe⟩, ⟨G, hG, hGe⟩⟩
  exact h y ⟨⟨(F.2, F.1), ⟨hF.2, hF.1⟩, by rw [← hFe, eval_swap]⟩,
    ⟨(G.2, G.1), by rcases hG with h | h; exacts [Or.inr h, Or.inl h], by rw [← hGe, eval_swap]⟩⟩

/-- The two orderings of the generators give the same `add (x₁ + x₂)`. -/
theorem addOf_add_swap : add((x₂ + x₁)) = add((x₁ + x₂)) := by
  rw [add_comm]

/-- **The counting step of Theorem 5.3(i)**.

If a form with finitely many copies of `x₁` is braided with `ℵ₀ X₁ + ℵ₀ X₂`, then `x₁ ∈ add x₂`.

This is the paper's "all but finitely many blocks sum to `|I_μ| x_j`, while the other form has
infinitely many copies of `x_i`".  Only finitely many `I`-blocks meet the `x₁`-slots of the finite
form, but infinitely many `J`-blocks meet the `x₁`-slots of `ℵ₀ X₁ + ℵ₀ X₂` (each block is finite).
So some position `p` has `x₁` inside `J p` while neither `I p` nor `I (p+1)` meets an `x₁`-slot;
then `u p` and `v (p+1)` are both summands of finite multiples of `x₂`, and

    x₁ ≼ Σ_{J p} y = v (p+1) + u p ≼ (r + r') x₂. -/
theorem mem_addOf_of_braidedForms_top (n : ℕ)
    (hFm : ∀ i, familyOfForm x₁ x₂ ((n : ℕ∞), ⊤) i ∈ add((x₁ + x₂)))
    (hGm : ∀ i, familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) i ∈ add((x₁ + x₂)))
    (hbr : BraidedForms x₁ x₂ ((n : ℕ∞), ⊤) ((⊤ : ℕ∞), ⊤) hFm hGm) :
    x₁ ∈ add(x₂) := by
  classical

  have hx₂T : x₂ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  obtain ⟨D⟩ := hbr
  -- the `I`-blocks meeting an `x₁`-slot of the finite form, and their `bsucc`-predecessors
  have hBad : ((fun i => IsBraided.blockOf D.I D.I_cover i) '' oneSlots.{u} n).Finite :=
    (finite_oneSlots n).image _
  have hBad' : (((fun i => IsBraided.blockOf D.I D.I_cover i) '' oneSlots.{u} n)
      ∪ bsucc ⁻¹' ((fun i => IsBraided.blockOf D.I D.I_cover i) '' oneSlots.{u} n)).Finite :=
    hBad.union (hBad.preimage (Function.Injective.injOn bsucc_injective))
  -- the `J`-blocks meeting an `x₁`-slot of `ℵ₀ X₁ + ℵ₀ X₂`: infinitely many
  have hWinf : (Set.range (Sum.inl : Nats.{u} → FormIdx.{u})).Infinite :=
    Set.infinite_of_injective_forall_mem (f := fun j : Nats.{u} => (Sum.inl j : FormIdx.{u}))
      (fun a b hab => by simpa using hab) (fun j => Set.mem_range_self j)
  have hGoodinf : ((fun i => IsBraided.blockOf D.J D.J_cover i) ''
      (Set.range (Sum.inl : Nats.{u} → FormIdx.{u}))).Infinite := by
    intro hfin
    refine hWinf ?_
    refine Set.Finite.subset (hfin.biUnion fun p _ =>
      Cardinal.lt_aleph0_iff_set_finite.mp (D.J_lt p)) fun i hi => ?_
    exact Set.mem_biUnion (Set.mem_image_of_mem _ hi) (IsBraided.mem_blockOf D.J D.J_cover i)
  obtain ⟨p, hpGood, hpBad⟩ := (hGoodinf.sdiff hBad').nonempty
  -- at `p` and at `p + 1` the `I`-blocks carry only `x₂`
  have hIblock : ∀ q : FormIdx.{u} × ℕ,
      q ∉ (fun i => IsBraided.blockOf D.I D.I_cover i) '' oneSlots.{u} n →
      ∃ r : ℕ, D.v q + D.u q = r • (⟨x₂, hx₂T⟩ : ↥(add((x₁ + x₂)))) := by
    intro q hq
    obtain ⟨r, hr⟩ := exists_nsmul_finsum (Cardinal.lt_aleph0_iff_set_finite.mp (D.I_lt q))
      (fun i => (⟨familyOfForm x₁ x₂ ((n : ℕ∞), ⊤) i, hFm i⟩ :
        ↥(add((x₁ + x₂)))))
      (⟨x₂, hx₂T⟩ : ↥(add((x₁ + x₂))))
      (fun i hi => by
        have hone : i ∉ oneSlots.{u} n := fun hmem =>
          hq ⟨i, hmem, IsBraided.blockOf_eq D.I_disjoint D.I_cover hi⟩
        rcases familyOfForm_eq_of_notMem_oneSlots x₁ x₂ hone with h | h
        · exact ⟨1, by rw [one_smul]; exact Subtype.ext h⟩
        · exact ⟨0, by rw [zero_smul]; exact Subtype.ext h⟩)
    exact ⟨r, by rw [← hr, ← LMonoid.lsumOf_eq_finsum (D.I_lt q)]; exact (D.hI q).symm⟩
  obtain ⟨r, hr⟩ := hIblock p fun h => hpBad (Set.mem_union_left _ h)
  obtain ⟨r', hr'⟩ := hIblock (bsucc p) fun h => hpBad (Set.mem_union_right _ h)
  -- and `x₁` is a summand of the `J`-block at `p`
  obtain ⟨i₀, hi₀J, hi₀W⟩ : ∃ i, i ∈ D.J p ∧ i ∈ Set.range (Sum.inl : Nats.{u} → FormIdx.{u}) := by
    obtain ⟨i, hiW, hip⟩ := hpGood
    exact ⟨i, hip ▸ IsBraided.mem_blockOf D.J D.J_cover i, hiW⟩
  obtain ⟨j, rfl⟩ := hi₀W
  obtain ⟨c, hc⟩ := exists_add_eq_finsum_mem (Cardinal.lt_aleph0_iff_set_finite.mp (D.J_lt p))
    (fun i => (⟨familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) i, hGm i⟩ :
      ↥(add((x₁ + x₂))))) hi₀J
  have hJp : (∑ᶠ i ∈ D.J p, (⟨familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) i, hGm i⟩ :
      ↥(add((x₁ + x₂))))) = D.v (bsucc p) + D.u p := by
    rw [← LMonoid.lsumOf_eq_finsum (D.J_lt p)]
    exact D.hJ p
  rw [hJp] at hc
  -- read the whole thing in `H`
  have hval : (familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) (Sum.inl j)) = x₁ := by
    rw [familyOfForm_inl]
    exact if_pos (WithTop.coe_lt_top (j.down : ℕ))
  have hcH : x₁ + (c : H) = (D.v (bsucc p) : H) + (D.u p : H) := by
    have hcc : ((⟨familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) (Sum.inl j), hGm _⟩ :
          ↥(add((x₁ + x₂)))) : H) + (c : H)
        = (D.v (bsucc p) : H) + (D.u p : H) := congrArg Subtype.val hc
    rwa [show ((⟨familyOfForm x₁ x₂ ((⊤ : ℕ∞), ⊤) (Sum.inl j), hGm _⟩ :
      ↥(add((x₁ + x₂)))) : H) = x₁ from hval] at hcc
  have hrH : (D.v p : H) + (D.u p : H) = r • x₂ := by
    have := congrArg Subtype.val hr
    rwa [coe_nsmul_addOf x₁ x₂ r ⟨x₂, hx₂T⟩] at this
  have hr'H : (D.v (bsucc p) : H) + (D.u (bsucc p) : H) = r' • x₂ := by
    have := congrArg Subtype.val hr'
    rwa [coe_nsmul_addOf x₁ x₂ r' ⟨x₂, hx₂T⟩] at this
  refine ⟨(c : H) + (D.u (bsucc p) : H) + (D.v p : H), r' + r, ?_⟩
  rw [KMonoid.cmul_natCast, add_nsmul, ← hr'H, ← hrH]
  calc x₁ + ((c : H) + (D.u (bsucc p) : H) + (D.v p : H))
      = (x₁ + (c : H)) + (D.u (bsucc p) : H) + (D.v p : H) := by abel
    _ = ((D.v (bsucc p) : H) + (D.u p : H)) + (D.u (bsucc p) : H) + (D.v p : H) := by rw [hcH]
    _ = ((D.v (bsucc p) : H) + (D.u (bsucc p) : H)) + ((D.v p : H) + (D.u p : H)) := by abel

/-- Condition (i) of Theorem 5.3 holds as soon as `H` is braided over `add (x₁ + x₂)`: the
counting step gives `x₁ ∈ add x₂`, and then `ℵ₀ x₂` absorbs `ℵ₀ x₁`. -/
theorem cond1_of_braidedOver
    (hbr :
      IsBraidedOver ℵ₀ ℵ₀ ↥(add((x₁ + x₂))) H (Order.le_succ ℵ₀) (fun y => (y : H))) :
    Cond1 x₁ x₂ := by
  intro n hn
  have heval : eval x₁ x₂ ((n : ℕ∞), ⊤) = eval x₁ x₂ ((⊤ : ℕ∞), ⊤) := by
    show ecmul ((n : ℕ) : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂ = ecmul (⊤ : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂
    rw [ecmul_natCast, ecmul_top, ecmul_top]
    exact hn
  have hmem : x₁ ∈ add(x₂) :=
    mem_addOf_of_braidedForms_top x₁ x₂ n (familyOfForm_mem x₁ x₂ _) (familyOfForm_mem x₁ x₂ _)
      (braidedForms_of_braidedOver x₁ x₂ hbr _ _ heval _ _)
  refine ⟨?_, hmem⟩
  have habs := cmul_top_absorb x₁ x₂ hmem ⊤
  rw [ecmul_top] at habs
  exact habs.symm.trans (add_comm _ _)

/-- **Theorem 5.3, forward direction**: if `H ≅ V^{ℵ₀}(R)` for a ring whose projectives are direct
sums of finitely generated modules, then the three conditions hold for both orderings of the
generators.

The hypothesis is the paper's own: Theorem 5.3 is stated for a ring whose projective modules are
direct sums of finitely generated modules, which is `EveryProjectiveIsSumOfFG`; hereditary rings
appear only in its closing "in fact" sentence.  Corollary 5.5(2) applies this direction to a ring
known only to have its countably (non finitely) generated projectives free, which suffices by
Kaplansky's theorem (`everyProjectiveIsSumOfFG_of_free`).

Lemma 5.1 supplies the braiding over `add (x₁ + x₂)`; (iii) is then Lemma 5.2(1), (ii) is Lemma
5.2(4), and (i) is `cond1_of_braidedOver`. -/
theorem theorem_5_3_forward (R : Type u) [Ring R] (hfg : EveryProjectiveIsSumOfFG R)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H))
    (e : V(R).carrier → H)
    (hhom : letI := V(R).instKMonoid le_rfl; KMonoid.IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) :
    Cond1 x₁ x₂ ∧ Cond1 x₂ x₁ ∧ Cond2 x₁ x₂ ∧ Cond2 x₂ x₁ ∧ NoMixedForms x₁ x₂ := by
  classical

  -- invert the isomorphism and feed Lemma 5.1
  obtain ⟨e', hleft, hright⟩ : ∃ g : H → V(R).carrier,
      Function.LeftInverse g e ∧ Function.RightInverse g e :=
    ⟨(Equiv.ofBijective e hbij).symm, (Equiv.ofBijective e hbij).left_inv,
      (Equiv.ofBijective e hbij).right_inv⟩
  have hbrH := lemma_5_1 R hfg x₁ x₂ hgen hnoncyclic e' (hhom.inv hbij hright)
    ⟨hright.injective, hleft.surjective⟩
  have hgen' : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₂, x₁} : Set H) := by
    rwa [Set.pair_comm]
  have hbrH' := IsBraidedOver.of_set_eq Cardinal.isRegular_aleph0
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₂ + x₁))
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)) (addOf_add_swap x₁ x₂) hbrH
  have hne := ne_zero_of_not_cyclic x₁ x₂ hgen hnoncyclic
  -- (iii): a finite and an infinite form of the same element would be braided
  have hmix : NoMixedForms x₁ x₂ := by
    rintro y ⟨⟨F, hF, hFe⟩, ⟨G, hG, hGe⟩⟩
    exact lemma_5_2_one x₁ x₂ G F hG hF hne.1 hne.2
      (familyOfForm_mem x₁ x₂ G) (familyOfForm_mem x₁ x₂ F)
      (braidedForms_of_braidedOver x₁ x₂ hbrH G F (hGe.trans hFe.symm) _ _)
  refine ⟨cond1_of_braidedOver x₁ x₂ hbrH, cond1_of_braidedOver x₂ x₁ hbrH',
    fun hnotmem m n heq => ?_, fun hnotmem m n heq => ?_, hmix⟩
  · exact lemma_5_2_four x₁ x₂ hnotmem hmix hgen m n
      (familyOfForm_mem x₁ x₂ _) (familyOfForm_mem x₁ x₂ _)
      (braidedForms_of_braidedOver x₁ x₂ hbrH _ _ heq
        (familyOfForm_mem x₁ x₂ _) (familyOfForm_mem x₁ x₂ _))
  · exact lemma_5_2_four x₂ x₁ hnotmem (noMixedForms_swap x₁ x₂ hmix) hgen' m n
      (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _)
      (braidedForms_of_braidedOver x₂ x₁ hbrH' _ _ heq
        (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _))

/-! ### The four cases of Theorem 5.3's backward direction -/

/-- Braidedness of two families over a `λ⁻`-closed subset depends only on the subset: two proofs
that the same set is closed give definitionally equal monoid structures (trap 13). -/
theorem isBraided_base_eq {S T : Set H} (hS : IsLSubset (ℵ₀ : Cardinal.{u}) (Order.le_succ ℵ₀) S)
    (hT : IsLSubset (ℵ₀ : Cardinal.{u}) (Order.le_succ ℵ₀) T) (hST : S = T) {ι : Type u} (f g : ι → H)
    (hfS : ∀ i, f i ∈ S) (hgS : ∀ i, g i ∈ S) (hfT : ∀ i, f i ∈ T) (hgT : ∀ i, g i ∈ T)
    (h : letI := hS.lmonoid Cardinal.isRegular_aleph0
      IsBraided ℵ₀ (fun i => (⟨f i, hfS i⟩ : ↥S)) (fun i => (⟨g i, hgS i⟩ : ↥S))) :
    letI := hT.lmonoid Cardinal.isRegular_aleph0
    IsBraided ℵ₀ (fun i => (⟨f i, hfT i⟩ : ↥T)) (fun i => (⟨g i, hgT i⟩ : ↥T)) := by
  subst hST
  exact h

/-- Swapping the generators swaps the two halves of `FormIdx` and the two coefficients. -/
theorem braidedForms_swap {F G : Form}
    (hFm : ∀ i, familyOfForm x₂ x₁ F i ∈ add((x₂ + x₁)))
    (hGm : ∀ i, familyOfForm x₂ x₁ G i ∈ add((x₂ + x₁)))
    (h : BraidedForms x₂ x₁ F G hFm hGm)
    (hFm' : ∀ i, familyOfForm x₁ x₂ (F.2, F.1) i ∈ add((x₁ + x₂)))
    (hGm' : ∀ i, familyOfForm x₁ x₂ (G.2, G.1) i ∈ add((x₁ + x₂))) :
    BraidedForms x₁ x₂ (F.2, F.1) (G.2, G.1) hFm' hGm' := by

  have hmemF : ∀ i, familyOfForm x₂ x₁ F i ∈ add((x₁ + x₂)) := by
    intro i
    rw [← addOf_add_swap x₁ x₂]
    exact hFm i
  have hmemG : ∀ i, familyOfForm x₂ x₁ G i ∈ add((x₁ + x₂)) := by
    intro i
    rw [← addOf_add_swap x₁ x₂]
    exact hGm i
  have hbase : IsBraided (ℵ₀ : Cardinal.{u})
      (fun i => (⟨familyOfForm x₂ x₁ F i, hmemF i⟩ : ↥(add((x₁ + x₂)))))
      (fun i => (⟨familyOfForm x₂ x₁ G i, hmemG i⟩ : ↥(add((x₁ + x₂))))) :=
    isBraided_base_eq (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₂ + x₁))
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)) (addOf_add_swap x₁ x₂)
      (familyOfForm x₂ x₁ F) (familyOfForm x₂ x₁ G) hFm hGm hmemF hmemG h
  have h' := hbase.comp_equiv (Equiv.sumComm Nats.{u} Nats.{u})
  have hEq : ∀ (K : Form) (hK : ∀ i, familyOfForm x₂ x₁ K i ∈ add((x₁ + x₂)))
      (hK' : ∀ i, familyOfForm x₁ x₂ (K.2, K.1) i ∈ add((x₁ + x₂))),
      (fun i => (⟨familyOfForm x₂ x₁ K ((Equiv.sumComm Nats.{u} Nats.{u}) i), hK _⟩ :
          ↥(add((x₁ + x₂)))))
        = (fun i => (⟨familyOfForm x₁ x₂ (K.2, K.1) i, hK' i⟩ :
          ↥(add((x₁ + x₂))))) := by
    intro K hK hK'
    funext i
    refine Subtype.ext ?_
    rcases i with j | j <;> rfl
  rw [hEq F hmemF hFm', hEq G hmemG hGm'] at h'
  exact h'

/-- **A finite relation gives a braiding of the two infinite forms**: if
`m x₁ + k x₂ = m' x₁ + k' x₂` with all four finite, then `m X₁ + ℵ₀ X₂` and `m' X₁ + ℵ₀ X₂` are
braided.  Block `0` holds the `m` copies of `x₁` and the first `k` copies of `x₂` against the `m'`
copies and the first `k'`; every later block matches one copy of `x₂` against one copy of `x₂`.
This is the paper's "from this we can easily construct a braiding". -/
theorem braidedForms_of_finite_relation (m k m' k' : ℕ)
    (hrel : eval x₁ x₂ ((m : ℕ∞), (k : ℕ∞)) = eval x₁ x₂ ((m' : ℕ∞), (k' : ℕ∞)))
    (hFm : ∀ i, familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i ∈ add((x₁ + x₂)))
    (hGm : ∀ i, familyOfForm x₁ x₂ ((m' : ℕ∞), ⊤) i ∈ add((x₁ + x₂))) :
    BraidedForms x₁ x₂ ((m : ℕ∞), ⊤) ((m' : ℕ∞), ⊤) hFm hGm := by
  classical

  have hx₁T : x₁ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  have hbase : (m • x₁ + k • x₂) ∈ add((x₁ + x₂)) :=
    addOf_add_mem (addOf_nsmul_mem hx₁T m) (addOf_nsmul_mem hx₂T k)
  -- the two level functions: the finite parts on level `0`, then one copy of `x₂` per level
  have hfin : ∀ (c : ℕ) (l : ℕ),
      {j : Nats.{u} | (if j.down < c then 0 else (j.down - c) + 1) = l}.Finite := by
    intro c l
    rcases l with _ | L
    · rw [levelA_fiber_zero]; exact finite_nats_lt c
    · rw [levelA_fiber_succ]; exact finite_nats_eq (c + L)
  refine IsBraided.of_levels (Sum.inl (ULift.up 0))
    (Sum.elim (fun j => if j.down < m then 0 else (j.down - m) + 1)
      (fun j => if j.down < k then 0 else (j.down - k) + 1))
    (Sum.elim (fun j => if j.down < m' then 0 else (j.down - m') + 1)
      (fun j => if j.down < k' then 0 else (j.down - k') + 1))
    (fun l => finite_fiber_elim (hfin m l) (hfin k l))
    (fun l => finite_fiber_elim (hfin m' l) (hfin k' l))
    (fun l => if l = 0 then ⟨m • x₁ + k • x₂, hbase⟩ else ⟨x₂, hx₂T⟩) (fun _ => 0) rfl
    (fun l => ?_) (fun l => ?_)
  · refine Subtype.ext ?_
    rw [coe_finsum_mem x₁ x₂ (finite_fiber_elim (hfin m l) (hfin k l)) _ hFm]
    rcases l with _ | L
    · rw [finsum_fiber_const (a := x₁) (b := x₂) (hfin m 0) (hfin k 0) _
        (fun j hj => by
          rw [levelA_fiber_zero] at hj
          rw [familyOfForm_inl]
          refine if_pos ?_
          show ((j.down : ℕ) : ℕ∞) < ((m : ℕ) : ℕ∞)
          exact_mod_cast (hj : (j.down : ℕ) < m))
        (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        show ({j : Nats.{u} | (if j.down < m then 0 else (j.down - m) + 1) = 0}).ncard = m by
          rw [levelA_fiber_zero]; exact ncard_nats_lt m,
        show ({j : Nats.{u} | (if j.down < k then 0 else (j.down - k) + 1) = 0}).ncard = k by
          rw [levelA_fiber_zero]; exact ncard_nats_lt k]
      exact (zero_add _).symm
    · rw [finsum_fiber_const (a := (0 : H)) (b := x₂) (hfin m (L + 1)) (hfin k (L + 1)) _
        (fun j hj => by
          rw [levelA_fiber_succ] at hj
          rw [familyOfForm_inl]
          refine if_neg ?_
          show ¬ (((j.down : ℕ) : ℕ∞) < ((m : ℕ) : ℕ∞))
          have hja : (j.down : ℕ) = m + L := hj
          rw [hja]
          exact_mod_cast Nat.not_lt.mpr (Nat.le_add_right m L))
        (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        show ({j : Nats.{u} | (if j.down < k then 0 else (j.down - k) + 1) = L + 1}).ncard = 1 by
          rw [levelA_fiber_succ]; exact ncard_nats_eq (k + L),
        smul_zero, zero_add, one_smul]
      exact (zero_add _).symm
  · refine Subtype.ext ?_
    rw [coe_finsum_mem x₁ x₂ (finite_fiber_elim (hfin m' l) (hfin k' l)) _ hGm]
    rcases l with _ | L
    · rw [finsum_fiber_const (a := x₁) (b := x₂) (hfin m' 0) (hfin k' 0) _
        (fun j hj => by
          rw [levelA_fiber_zero] at hj
          rw [familyOfForm_inl]
          refine if_pos ?_
          show ((j.down : ℕ) : ℕ∞) < ((m' : ℕ) : ℕ∞)
          exact_mod_cast (hj : (j.down : ℕ) < m'))
        (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        show ({j : Nats.{u} | (if j.down < m' then 0 else (j.down - m') + 1) = 0}).ncard = m' by
          rw [levelA_fiber_zero]; exact ncard_nats_lt m',
        show ({j : Nats.{u} | (if j.down < k' then 0 else (j.down - k') + 1) = 0}).ncard = k' by
          rw [levelA_fiber_zero]; exact ncard_nats_lt k']
      have hrel' : m • x₁ + k • x₂ = m' • x₁ + k' • x₂ := by
        have h0 := hrel
        rwa [eval, eval, ecmul_natCast, ecmul_natCast, ecmul_natCast, ecmul_natCast] at h0
      exact hrel'.symm.trans (zero_add _).symm
    · rw [finsum_fiber_const (a := (0 : H)) (b := x₂) (hfin m' (L + 1)) (hfin k' (L + 1)) _
        (fun j hj => by
          rw [levelA_fiber_succ] at hj
          rw [familyOfForm_inl]
          refine if_neg ?_
          show ¬ (((j.down : ℕ) : ℕ∞) < ((m' : ℕ) : ℕ∞))
          have hja : (j.down : ℕ) = m' + L := hj
          rw [hja]
          exact_mod_cast Nat.not_lt.mpr (Nat.le_add_right m' L))
        (fun j _ => by rw [familyOfForm_inr]; exact if_pos (WithTop.coe_lt_top (j.down : ℕ))),
        show ({j : Nats.{u} | (if j.down < k' then 0 else (j.down - k') + 1) = L + 1}).ncard = 1 by
          rw [levelA_fiber_succ]; exact ncard_nats_eq (k' + L),
        smul_zero, zero_add, one_smul]
      exact (zero_add _).symm

/-- `ℵ₀` copies of `x` absorb any smaller number of copies. -/
theorem ecmul_add_cmul_top (a : ℕ∞) (x : H) :
    ecmul a x + ℵ₀∙x = ℵ₀∙x := by
  obtain ⟨w, hw⟩ : ecmul a x ≼ ℵ₀∙x :=
    KMonoid.cmul_le_cmul (Cardinal.ofENat_le_aleph0 a) le_rfl (Cardinal.ofENat_le_aleph0 a) x
  exact KMonoid.add_cmul_top_eq hw

/-- `ℵ₀ x + ℵ₀ x = ℵ₀ x`. -/
theorem cmul_top_add_self (x : H) :
    ℵ₀∙x + ℵ₀∙x
      = ℵ₀∙x :=
  KMonoid.add_cmul_top_eq (add_zero _)

/-- **The case `β = β' = ℵ₀` of Theorem 5.3's backward direction.**  If `x₁ ∈ add x₂` this is
Lemma 5.2(3).  Otherwise both `X₁`-coefficients must be finite — an infinite one against a finite
one would make condition (i) produce `x₁ ∈ add x₂` — and condition (ii) supplies the finite
relation that `braidedForms_of_finite_relation` turns into a braiding. -/
theorem braidedForms_of_snd_top (hc1 : Cond1 x₁ x₂) (hc2 : Cond2 x₁ x₂)
    (hmix : NoMixedForms x₁ x₂) (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (α β : ℕ∞) (heq : eval x₁ x₂ (α, ⊤) = eval x₁ x₂ (β, ⊤))
    (hFm : ∀ i, familyOfForm x₁ x₂ (α, ⊤) i ∈ add((x₁ + x₂)))
    (hGm : ∀ i, familyOfForm x₁ x₂ (β, ⊤) i ∈ add((x₁ + x₂))) :
    BraidedForms x₁ x₂ (α, ⊤) (β, ⊤) hFm hGm := by

  by_cases hmem : x₁ ∈ add(x₂)
  · exact lemma_5_2_three x₁ x₂ hmem hmix hgen α β hFm hGm
  -- an infinite coefficient against a finite one would force `x₁ ∈ add x₂`
  have hkey : ∀ (d : ℕ), eval x₁ x₂ ((⊤ : ℕ∞), ⊤) = eval x₁ x₂ ((d : ℕ∞), ⊤) → False := by
    intro d hd
    refine hmem (hc1 d ?_).2
    have h0 : ecmul ((d : ℕ) : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂
        = ecmul (⊤ : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂ := hd.symm
    rwa [ecmul_natCast, ecmul_top, ecmul_top] at h0
  rcases eq_or_ne α ⊤ with rfl | hα
  · rcases eq_or_ne β ⊤ with rfl | hβ
    · exact IsBraided.refl _
    · obtain ⟨d, rfl⟩ : ∃ d : ℕ, β = (d : ℕ∞) := ⟨β.toNat, (ENat.natCast_toNat hβ).symm⟩
      exact absurd heq (fun h => hkey d h)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, α = (m : ℕ∞) := ⟨α.toNat, (ENat.natCast_toNat hα).symm⟩
    rcases eq_or_ne β ⊤ with rfl | hβ
    · exact absurd heq.symm (fun h => hkey m h)
    · obtain ⟨m', rfl⟩ : ∃ m' : ℕ, β = (m' : ℕ∞) := ⟨β.toNat, (ENat.natCast_toNat hβ).symm⟩
      obtain ⟨k, k', hrel⟩ := hc2 hmem m m' heq
      exact braidedForms_of_finite_relation x₁ x₂ m k m' k' hrel hFm hGm

/-- **The mixed case of Theorem 5.3's backward direction**: `α X₁ + ℵ₀ X₂` against
`ℵ₀ X₁ + n X₂`.  Adding `ℵ₀ x₁` to both sides puts condition (i) for the pair `(x₂, x₁)` in
force, giving `x₂ ∈ add x₁`; adding `ℵ₀ x₂` instead gives `x₁ ∈ add x₂` when `α` is finite.  Both
forms are then braided with `ℵ₀ X₁ + ℵ₀ X₂` by Lemma 5.2(3), and the paper's "transitivity and
symmetry" finishes. -/
theorem braidedForms_of_mixed (hc1 : Cond1 x₁ x₂) (hc1' : Cond1 x₂ x₁)
    (hmix : NoMixedForms x₁ x₂) (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (α : ℕ∞) (n : ℕ) (heq : eval x₁ x₂ (α, ⊤) = eval x₁ x₂ ((⊤ : ℕ∞), (n : ℕ∞)))
    (hFm : ∀ i, familyOfForm x₁ x₂ (α, ⊤) i ∈ add((x₁ + x₂)))
    (hGm : ∀ i, familyOfForm x₁ x₂ ((⊤ : ℕ∞), (n : ℕ∞)) i ∈ add((x₁ + x₂))) :
    BraidedForms x₁ x₂ (α, ⊤) ((⊤ : ℕ∞), (n : ℕ∞)) hFm hGm := by

  have hgen' : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₂, x₁} : Set H) := by
    rwa [Set.pair_comm]
  have hmix' := noMixedForms_swap x₁ x₂ hmix
  have heval : ecmul α x₁ + ℵ₀∙x₂
      = ℵ₀∙x₁ + ecmul ((n : ℕ) : ℕ∞) x₂ := by
    have h0 := heq
    rwa [eval, eval, ecmul_top, ecmul_top] at h0
  -- `x₂ ∈ add x₁`, by adding `ℵ₀ x₁` to both sides
  have hx₂ : x₂ ∈ add(x₁) := by
    refine (hc1' n ?_).2
    have h1 : ℵ₀∙x₁ + (ecmul α x₁
          + ℵ₀∙x₂)
        = ℵ₀∙x₁ + (ℵ₀∙x₁
          + ecmul ((n : ℕ) : ℕ∞) x₂) := by rw [heval]
    rw [← add_assoc, add_comm (ℵ₀∙x₁) (ecmul α x₁),
      ecmul_add_cmul_top, ← add_assoc, cmul_top_add_self] at h1
    rw [ecmul_natCast] at h1
    rw [add_comm (n • x₂), ← h1, add_comm]
  -- the second form is braided with `ℵ₀ X₁ + ℵ₀ X₂`
  have hG : BraidedForms x₁ x₂ ((⊤ : ℕ∞), (n : ℕ∞)) ((⊤ : ℕ∞), (⊤ : ℕ∞))
      hGm (familyOfForm_mem x₁ x₂ _) :=
    braidedForms_swap x₁ x₂ (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _)
      (lemma_5_2_three x₂ x₁ hx₂ hmix' hgen' ((n : ℕ) : ℕ∞) (⊤ : ℕ∞)
        (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _)) hGm (familyOfForm_mem x₁ x₂ _)
  -- and so is the first
  have hF : BraidedForms x₁ x₂ (α, ⊤) ((⊤ : ℕ∞), (⊤ : ℕ∞)) hFm (familyOfForm_mem x₁ x₂ _) := by
    rcases eq_or_ne α ⊤ with rfl | hα
    · exact IsBraided.refl _
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, α = (m : ℕ∞) := ⟨α.toNat, (ENat.natCast_toNat hα).symm⟩
    refine lemma_5_2_three x₁ x₂ ?_ hmix hgen _ _ _ _
    refine (hc1 m ?_).2
    have h1 : (ecmul ((m : ℕ) : ℕ∞) x₁ + ℵ₀∙x₂)
        = (ℵ₀∙x₁ + ecmul ((n : ℕ) : ℕ∞) x₂)
          + ℵ₀∙x₂ := by
      rw [← heval, add_assoc, cmul_top_add_self]
    rw [add_assoc, ecmul_add_cmul_top, ecmul_natCast] at h1
    exact h1
  exact IsBraided.trans_aleph0 hF (IsBraided.symm hG)

/-- **Theorem 5.3's backward direction, at the level of forms**: under conditions (i)–(iii), two
forms representing the same element are braided.  This is the paper's four-case split. -/
theorem braidedForms_of_conditions (hc1 : Cond1 x₁ x₂) (hc1' : Cond1 x₂ x₁)
    (hc2 : Cond2 x₁ x₂) (hc2' : Cond2 x₂ x₁) (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (F G : Form) (heq : eval x₁ x₂ F = eval x₁ x₂ G)
    (hFm : ∀ i, familyOfForm x₁ x₂ F i ∈ add((x₁ + x₂)))
    (hGm : ∀ i, familyOfForm x₁ x₂ G i ∈ add((x₁ + x₂))) :
    BraidedForms x₁ x₂ F G hFm hGm := by

  have hgen' : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₂, x₁} : Set H) := by
    rwa [Set.pair_comm]
  have hmix' := noMixedForms_swap x₁ x₂ hmix
  -- by condition (iii) the two forms are finite or infinite together
  by_cases hFfin : F.IsFinite
  · have hGfin : G.IsFinite := by
      by_contra hG
      have hGinf : G.IsInfinite := by
        by_contra h
        exact hG ((Form.not_isInfinite_iff G).mp h)
      exact hmix (eval x₁ x₂ F) ⟨⟨F, hFfin, rfl⟩, ⟨G, hGinf, heq.symm⟩⟩
    exact lemma_5_2_two x₁ x₂ F G hFfin hGfin heq hFm hGm
  have hFinf : F.IsInfinite := by
    by_contra h
    exact hFfin ((Form.not_isInfinite_iff F).mp h)
  have hGinf : G.IsInfinite := by
    by_contra h
    have hGfin : G.IsFinite := (Form.not_isInfinite_iff G).mp h
    exact hmix (eval x₁ x₂ G) ⟨⟨G, hGfin, rfl⟩, ⟨F, hFinf, heq⟩⟩
  obtain ⟨a, b⟩ := F
  obtain ⟨c, d⟩ := G
  rcases eq_or_ne b ⊤ with rfl | hb
  · rcases eq_or_ne d ⊤ with rfl | hd
    · exact braidedForms_of_snd_top x₁ x₂ hc1 hc2 hmix hgen a c heq hFm hGm
    · -- `d` finite, so `c = ⊤`
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = (n : ℕ∞) := ⟨d.toNat, (ENat.natCast_toNat hd).symm⟩
      have hc : c = ⊤ := by rcases hGinf with h | h; exacts [h, absurd h (by simp)]
      subst hc
      exact braidedForms_of_mixed x₁ x₂ hc1 hc1' hmix hgen a n heq hFm hGm
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = (n : ℕ∞) := ⟨b.toNat, (ENat.natCast_toNat hb).symm⟩
    have ha : a = ⊤ := by rcases hFinf with h | h; exacts [h, absurd h (by simp)]
    subst ha
    rcases eq_or_ne d ⊤ with rfl | hd
    · exact IsBraided.symm (braidedForms_of_mixed x₁ x₂ hc1 hc1' hmix hgen c n heq.symm hGm hFm)
    · -- both `X₂`-coefficients finite, so both `X₁`-coefficients are `⊤`: the swapped case
      obtain ⟨n', rfl⟩ : ∃ n' : ℕ, d = (n' : ℕ∞) := ⟨d.toNat, (ENat.natCast_toNat hd).symm⟩
      have hc : c = ⊤ := by rcases hGinf with h | h; exacts [h, absurd h (by simp)]
      subst hc
      refine braidedForms_swap x₁ x₂ (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _)
        (braidedForms_of_snd_top x₂ x₁ hc1' hc2' hmix' hgen' ((n : ℕ) : ℕ∞) ((n' : ℕ) : ℕ∞)
          ?_ (familyOfForm_mem x₂ x₁ _) (familyOfForm_mem x₂ x₁ _)) hFm hGm
      rw [eval_swap x₂ x₁, eval_swap x₂ x₁]
      exact heq

/-! ### Cutting the slots of a form into the blocks of a sequence of partial sums

The backward direction of Theorem 5.3 must braid an *arbitrary* family over `add (x₁ + x₂)` with a
family of generators — the step the paper compresses into "hence `add (x₁ + x₂) = ⟨x₁, x₂⟩`".  Each
member of the family is a finite form `c k · x₁ + d k · x₂`, and the slots of the total form have to
be cut into consecutive blocks of `c k` copies of `x₁` and `d k` copies of `x₂`.  `Nat.blockIdx` is that
cut: for the partial sums `s` of `c`, it sends `j` to the `k` with `s k ≤ j < s (k+1)`. -/

section Blocks

/-- A `finsum` over the fibre of a level function on `FormIdx` splits into its two halves. -/
theorem finsum_fiber_elim_split {M : Type v} [AddCommMonoid M] {f g : Nats.{u} → ℕ} {k : ℕ}
    (hf : {j : Nats.{u} | f j = k}.Finite) (hg : {j : Nats.{u} | g j = k}.Finite)
    (F : FormIdx.{u} → M) :
    ∑ᶠ i ∈ {i : FormIdx.{u} | Sum.elim f g i = k}, F i
      = (∑ᶠ j ∈ {j : Nats.{u} | f j = k}, F (Sum.inl j))
        + (∑ᶠ j ∈ {j : Nats.{u} | g j = k}, F (Sum.inr j)) := by
  classical
  have hdisj : Disjoint (Sum.inl '' {j : Nats.{u} | f j = k})
      (Sum.inr '' {j : Nats.{u} | g j = k}) := by
    refine Set.disjoint_left.mpr ?_
    rintro i ⟨j, -, rfl⟩ ⟨j', -, hj'⟩
    exact Sum.inl_ne_inr hj'.symm
  rw [fiber_elim, finsum_mem_union hdisj (hf.image _) (hg.image _),
    finsum_mem_image Sum.inl_injective.injOn, finsum_mem_image Sum.inr_injective.injOn]

/-- **The block sum of a form's slots.**  On the fibre of `Nat.blockIdx` at `k` the family of a form
with `A` copies of `v` takes the value `v` exactly on `[s k, s (k+1))` — the leftover slot carries
`0`, since it lies beyond every `s l` — so the block sums to `s (k+1) - s k` copies of `v`. -/
theorem finsum_blockIdx_fibre {s : ℕ → ℕ} (hs : Monotone s) (hs0 : s 0 = 0) {A : ℕ∞}
    (hA : ∀ j : ℕ, ((j : ℕ) : ℕ∞) < A ↔ ∃ l, j < s l) (v : H) (k : ℕ) :
    (∑ᶠ j ∈ {j : Nats.{u} | Nat.blockIdx s j.down = k},
        (if ((j.down : ℕ) : ℕ∞) < A then v else 0)) = (s (k + 1) - s k) • v := by
  classical
  have hset : {j : Nats.{u} | Nat.blockIdx s j.down = k}
      = {j : Nats.{u} | j.down ∈ Set.Ico (s k) (s (k + 1))}
        ∪ {j : Nats.{u} | j.down ∈ {j | (¬ ∃ l, j < s l) ∧ j = k}} := by
    ext j
    show Nat.blockIdx s j.down = k ↔ _
    rw [show (Nat.blockIdx s j.down = k) ↔ j.down ∈ {j : ℕ | Nat.blockIdx s j = k} from Iff.rfl,
      Nat.blockIdx_fibre hs hs0]
    exact Iff.rfl
  have hfin₁ : {j : Nats.{u} | j.down ∈ Set.Ico (s k) (s (k + 1))}.Finite :=
    finite_nats_setOf (Set.finite_Ico _ _)
  have hfin₂ : {j : Nats.{u} | j.down ∈ {j | (¬ ∃ l, j < s l) ∧ j = k}}.Finite :=
    finite_nats_setOf ((Set.finite_singleton k).subset fun j hj => hj.2)
  have hdisj : Disjoint {j : Nats.{u} | j.down ∈ Set.Ico (s k) (s (k + 1))}
      {j : Nats.{u} | j.down ∈ {j | (¬ ∃ l, j < s l) ∧ j = k}} := by
    refine Set.disjoint_left.mpr fun j hj hj' => ?_
    exact hj'.1 ⟨k + 1, hj.2⟩
  rw [hset, finsum_mem_union hdisj hfin₁ hfin₂,
    finsum_mem_congr rfl (fun j hj => if_pos ((hA j.down).mpr ⟨k + 1, hj.2⟩) :
      ∀ j ∈ {j : Nats.{u} | j.down ∈ Set.Ico (s k) (s (k + 1))},
        (if ((j.down : ℕ) : ℕ∞) < A then v else 0) = v),
    finsum_mem_congr rfl (fun j hj => if_neg (fun hlt => hj.1 ((hA j.down).mp hlt)) :
      ∀ j ∈ {j : Nats.{u} | j.down ∈ {j | (¬ ∃ l, j < s l) ∧ j = k}},
        (if ((j.down : ℕ) : ℕ∞) < A then v else 0) = 0),
    finsum_mem_const_finite hfin₁, finsum_mem_zero, add_zero, ncard_nats_setOf,
    Set.ncard_Ico_nat]

end Blocks

/-- A fixed identification of the index type of an `ℵ₀`-sum with `ℕ`. -/
noncomputable def idxEquivNats : Idx (ℵ₀ : Cardinal.{u}) ≃ Nats.{u} :=
  (Cardinal.eq.mp ((mk_Idx (ℵ₀ : Cardinal.{u})).trans mk_nats.{u}.symm)).some

/-- **Every element of `add (x₁ + x₂)` has a finite form**, given condition (iii).

It is a summand of some `n (x₁ + x₂)`, which has the finite form `(n, n)`; a form of the sum is the
sum of forms of the parts, so an infinite form of the summand would give `n (x₁ + x₂)` an infinite
form alongside its finite one.  This is the paper's "elements of `add (x₁ + x₂)` can only have
finite forms". -/
theorem exists_finite_form_of_mem (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    {y : H} (hy : y ∈ add((x₁ + x₂))) :
    ∃ F : Form, F.IsFinite ∧ eval x₁ x₂ F = y := by
  obtain ⟨z, n, hzn⟩ := hy
  obtain ⟨F, hF⟩ := exists_form x₁ x₂ hgen y
  obtain ⟨G, hG⟩ := exists_form x₁ x₂ hgen z
  refine ⟨F, ?_, hF⟩
  by_contra hFfin
  have hFinf : F.IsInfinite := by
    by_contra h
    exact hFfin ((Form.not_isInfinite_iff F).mp h)
  -- the sum of the two forms evaluates to `n (x₁ + x₂)`, which also has the finite form `(n, n)`
  have hsum : eval x₁ x₂ (F.1 + G.1, F.2 + G.2) = n • x₁ + n • x₂ := by
    have h0 : y + z = n • x₁ + n • x₂ := by
      rw [hzn, KMonoid.cmul_natCast, smul_add]
    rw [eval, ecmul_add, ecmul_add, ← h0, ← hF, ← hG, eval, eval]
    abel
  have hfinite : HasFiniteForm x₁ x₂ (n • x₁ + n • x₂) := by
    refine ⟨(((n : ℕ) : ℕ∞), ((n : ℕ) : ℕ∞)), ⟨ENat.natCast_ne_top n, ENat.natCast_ne_top n⟩, ?_⟩
    rw [eval, ecmul_natCast, ecmul_natCast]
  have hinfinite : HasInfiniteForm x₁ x₂ (n • x₁ + n • x₂) := by
    refine ⟨(F.1 + G.1, F.2 + G.2), ?_, hsum⟩
    rcases hFinf with h | h
    · exact Or.inl (by rw [show (F.1 + G.1 : ℕ∞) = ⊤ + G.1 from by rw [h]]; exact top_add G.1)
    · exact Or.inr (by rw [show (F.2 + G.2 : ℕ∞) = ⊤ + G.2 from by rw [h]]; exact top_add G.2)
  exact hmix _ ⟨hfinite, hinfinite⟩

/-- **The refinement step of Theorem 5.3's backward direction.**

Every family over `add (x₁ + x₂)` is braided with the family of a single form: each member is a
finite form `c k · x₁ + d k · x₂`, and the slots of the total form `(A, B)` — where `A`, `B` are the
suprema of the partial sums — are cut into consecutive blocks of `c k` copies of `x₁` and `d k`
copies of `x₂` by `Nat.blockIdx`.  The family itself is cut into singletons, so the two block sums agree
and `IsBraided.of_levels` applies with `v ≡ 0`.

This is the step the paper compresses into "hence `add (x₁ + x₂) = ⟨x₁, x₂⟩`". -/
theorem exists_braided_form (hmix : NoMixedForms x₁ x₂)
    (hgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({x₁, x₂} : Set H))
    (a : Idx (ℵ₀ : Cardinal.{u}) → ↥(add((x₁ + x₂)))) :

    ∃ A B : ℕ∞, IsBraided ℵ₀ a
      (fun i => (⟨familyOfForm x₁ x₂ (A, B) (formIdxEquiv.{u}.symm i),
        familyOfForm_mem x₁ x₂ _ _⟩ : ↥(add((x₁ + x₂))))) := by
  classical

  -- a finite form for each member
  choose F hFfin hFeq using fun μ => exists_finite_form_of_mem x₁ x₂ hmix hgen (a μ).2
  set μof : ℕ → Idx (ℵ₀ : Cardinal.{u}) := fun k => idxEquivNats.{u}.symm (ULift.up k) with hμof
  set c : ℕ → ℕ := fun k => (F (μof k)).1.toNat with hc
  set d : ℕ → ℕ := fun k => (F (μof k)).2.toNat with hd
  set s : ℕ → ℕ := fun k => ∑ l ∈ Finset.range k, c l with hs
  set t : ℕ → ℕ := fun k => ∑ l ∈ Finset.range k, d l with ht
  have hsmono : Monotone s := by
    intro p q hpq
    exact Finset.sum_le_sum_of_subset
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hpq))
  have htmono : Monotone t := by
    intro p q hpq
    exact Finset.sum_le_sum_of_subset
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hpq))
  have hs0 : s 0 = 0 := by simp [hs]
  have ht0 : t 0 = 0 := by simp [ht]
  have hsstep : ∀ k, s (k + 1) - s k = c k := by
    intro k; rw [hs]; simp [Finset.sum_range_succ]
  have htstep : ∀ k, t (k + 1) - t k = d k := by
    intro k; rw [ht]; simp [Finset.sum_range_succ]
  set A : ℕ∞ := ⨆ l, ((s l : ℕ) : ℕ∞) with hAdef
  set B : ℕ∞ := ⨆ l, ((t l : ℕ) : ℕ∞) with hBdef
  have hA : ∀ j : ℕ, ((j : ℕ) : ℕ∞) < A ↔ ∃ l, j < s l := by
    intro j
    rw [hAdef, lt_iSup_iff]
    exact ⟨fun ⟨l, hl⟩ => ⟨l, by exact_mod_cast hl⟩, fun ⟨l, hl⟩ => ⟨l, by exact_mod_cast hl⟩⟩
  have hB : ∀ j : ℕ, ((j : ℕ) : ℕ∞) < B ↔ ∃ l, j < t l := by
    intro j
    rw [hBdef, lt_iSup_iff]
    exact ⟨fun ⟨l, hl⟩ => ⟨l, by exact_mod_cast hl⟩, fun ⟨l, hl⟩ => ⟨l, by exact_mod_cast hl⟩⟩
  refine ⟨A, B, ?_⟩
  set ψ : FormIdx.{u} → ℕ :=
    Sum.elim (fun j : Nats.{u} => Nat.blockIdx s j.down) (fun j : Nats.{u} => Nat.blockIdx t j.down) with hψ
  have hψfin : ∀ k, {p : FormIdx.{u} | ψ p = k}.Finite := fun k =>
    finite_fiber_elim (finite_nats_setOf (Nat.blockIdx_fibre_finite hsmono hs0 k))
      (finite_nats_setOf (Nat.blockIdx_fibre_finite htmono ht0 k))
  have hIfib : ∀ k : ℕ, {i : Idx (ℵ₀ : Cardinal.{u}) | (idxEquivNats.{u} i).down = k}
      = {μof k} := by
    intro k
    ext i
    show (idxEquivNats.{u} i).down = k ↔ i = μof k
    constructor
    · intro h
      show i = idxEquivNats.{u}.symm (ULift.up k)
      rw [← h]
      exact (idxEquivNats.{u}.symm_apply_apply i).symm
    · rintro rfl
      show (idxEquivNats.{u} (idxEquivNats.{u}.symm (ULift.up k))).down = k
      rw [Equiv.apply_symm_apply]
  have hJfib : ∀ k : ℕ,
      {i : Idx (ℵ₀ : Cardinal.{u}) | ψ (formIdxEquiv.{u}.symm i) = k}
        = formIdxEquiv.{u} '' {p : FormIdx.{u} | ψ p = k} := by
    intro k
    ext i
    constructor
    · intro h
      exact ⟨formIdxEquiv.{u}.symm i, h, formIdxEquiv.{u}.apply_symm_apply i⟩
    · rintro ⟨p, hp, rfl⟩
      show ψ (formIdxEquiv.{u}.symm (formIdxEquiv.{u} p)) = k
      rwa [formIdxEquiv.{u}.symm_apply_apply]
  refine IsBraided.of_levels (idxEquivNats.{u}.symm (ULift.up 0))
    (fun i => (idxEquivNats.{u} i).down) (fun i => ψ (formIdxEquiv.{u}.symm i))
    (fun k => by rw [hIfib k]; exact Set.finite_singleton _)
    (fun k => by rw [hJfib k]; exact (hψfin k).image _)
    (fun k => a (μof k)) (fun _ => 0) rfl (fun k => ?_) (fun k => ?_)
  · rw [hIfib k, finsum_mem_singleton]
    exact (zero_add _).symm
  · have hcongr : ∀ p ∈ {p : FormIdx.{u} | ψ p = k},
        (⟨familyOfForm x₁ x₂ (A, B) (formIdxEquiv.{u}.symm (formIdxEquiv.{u} p)),
            familyOfForm_mem x₁ x₂ _ _⟩ : ↥(add((x₁ + x₂))))
          = ⟨familyOfForm x₁ x₂ (A, B) p, familyOfForm_mem x₁ x₂ _ _⟩ :=
      fun p _ => Subtype.ext (by rw [Equiv.symm_apply_apply])
    rw [hJfib k, finsum_mem_image (Set.injOn_of_injective formIdxEquiv.{u}.injective),
      finsum_mem_congr rfl hcongr]
    refine Subtype.ext ?_
    have h1 : (∑ᶠ j ∈ {j : Nats.{u} | Nat.blockIdx s j.down = k},
        familyOfForm x₁ x₂ (A, B) (Sum.inl j)) = c k • x₁ := by
      rw [← hsstep k]
      exact finsum_blockIdx_fibre hsmono hs0 hA x₁ k
    have h2 : (∑ᶠ j ∈ {j : Nats.{u} | Nat.blockIdx t j.down = k},
        familyOfForm x₁ x₂ (A, B) (Sum.inr j)) = d k • x₂ := by
      rw [← htstep k]
      exact finsum_blockIdx_fibre htmono ht0 hB x₂ k
    rw [coe_finsum_mem x₁ x₂ (hψfin k) _ (familyOfForm_mem x₁ x₂ _), hψ,
      finsum_fiber_elim_split (finite_nats_setOf (Nat.blockIdx_fibre_finite hsmono hs0 k))
        (finite_nats_setOf (Nat.blockIdx_fibre_finite htmono ht0 k)), h1, h2]
    show c k • x₁ + d k • x₂ = (0 : H) + (a (μof k) : H)
    rw [zero_add, ← hFeq (μof k), eval,
      show (F (μof k)).1 = ((c k : ℕ) : ℕ∞) from (ENat.natCast_toNat (hFfin (μof k)).1).symm,
      show (F (μof k)).2 = ((d k : ℕ) : ℕ∞) from (ENat.natCast_toNat (hFfin (μof k)).2).symm,
      ecmul_natCast, ecmul_natCast]

/-- **Theorem 5.3, backward direction**: under the three conditions `H` is braided over
`add (x₁ + x₂)`, and Corollary 4.7(1) then realises it.

`exists_braided_form` replaces an arbitrary pair of families over `add (x₁ + x₂)` by a pair of
form families; Lemma 3.2 turns the hypothesis on their sums into an equality of the two forms'
values; and `braidedForms_of_conditions` braids those.  Transitivity finishes. -/
theorem theorem_5_3_backward (k : Type u) [Field k]
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hc1 : Cond1 x₁ x₂) (hc1' : Cond1 x₂ x₁) (hc2 : Cond2 x₁ x₂) (hc2' : Cond2 x₂ x₁)
    (hmix : NoMixedForms x₁ x₂) :
    ∃ (R : Type u) (_ : Ring R) (_ : Algebra k R) (_ : IsHereditary R),
      ∃ e : V(R).carrier → H,
        KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e := by
  classical

  let := KMonoid.toLMonoidOfLE H Cardinal.isRegular_aleph0 (Order.le_succ (ℵ₀ : Cardinal.{u}))
  refine corollary_4_7_one_forward le_rfl k (x₁ + x₂) ?_
  -- `add (x₁ + x₂)` contains both generators, hence generates `H`
  have hx₁T : x₁ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  have hTgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) (add((x₁ + x₂))) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hgen]
    refine KMonoid.kclosure_le ?_ (KMonoid.isKSubmonoid_kclosure _ _)
    rintro w (rfl | rfl)
    · exact KMonoid.subset_kclosure hx₁T
    · exact KMonoid.subset_kclosure hx₂T
  -- the inclusion is a homomorphism of `ℵ₀⁻`-monoids, so braided families keep their sums
  have hcoehom : IsLMonoidHom (ℵ₀ : Cardinal.{u})
      (fun y : ↥(add((x₁ + x₂))) => (y : H)) := fun {ι} h x => rfl
  have hksum : ∀ (y : Idx (ℵ₀ : Cardinal.{u}) → ↥(add((x₁ + x₂))))
      (C D : ℕ∞), IsBraided ℵ₀ y (fun i => (⟨familyOfForm x₁ x₂ (C, D) (formIdxEquiv.{u}.symm i),
        familyOfForm_mem x₁ x₂ _ _⟩ : ↥(add((x₁ + x₂))))) →
      KMonoid.ksum (κ := ℵ₀) (fun i => (y i : H)) = eval x₁ x₂ (C, D) := by
    intro y C D hy
    rw [← ksum_familyOfForm x₁ x₂ (C, D), ← KMonoid.sumOf_Idx, ← KMonoid.sumOf_Idx]
    exact sumOf_eq_of_isBraided Cardinal.isRegular_aleph0 (Order.le_succ (ℵ₀ : Cardinal.{u}))
      (le_of_eq (mk_Idx _)) _ _ (hy.map_lmonoidHom hcoehom)
  refine ⟨⟨rfl, fun {ι} h x => rfl⟩, Subtype.val_injective, fun h => ?_, fun a b hab => ?_⟩
  · obtain ⟨z, hzT, rfl⟩ := (KMonoid.mem_kclosure_iff
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)).zero_mem h).mp
      (KMonoid.kGenerates_iff.mp hTgen h)
    exact ⟨fun i => ⟨z i, hzT i⟩, rfl⟩
  · -- refine both families to form families, braid the forms, and compose
    obtain ⟨A, B, hA⟩ := exists_braided_form x₁ x₂ hmix hgen a
    obtain ⟨A', B', hB⟩ := exists_braided_form x₁ x₂ hmix hgen b
    have heval : eval x₁ x₂ (A, B) = eval x₁ x₂ (A', B') := by
      rw [← hksum a A B hA, ← hksum b A' B' hB]
      exact hab
    have hform := (braidedForms_of_conditions x₁ x₂ hc1 hc1' hc2 hc2' hmix hgen (A, B) (A', B')
      heval (familyOfForm_mem x₁ x₂ _) (familyOfForm_mem x₁ x₂ _)).comp_equiv formIdxEquiv.{u}.symm
    exact hA.trans_aleph0 (hform.trans_aleph0 hB.symm)

/-- **Theorem 5.3**: a non-cyclic `ℵ₀`-monoid on two generators is `V^{ℵ₀}(R)` for a hereditary
ring exactly when conditions (i), (ii) and (iii) hold for both orderings of the generators.

The paper's `1 ≤ i ≠ j ≤ 2` is rendered as a conjunction over the two orderings rather than as
`Fin 2` bookkeeping, which would cost more than it saves.

**The realizing ring is hereditary on both sides (`IsHereditary`), as the paper says** ("for a
hereditary ring").  No
condition on the projectives of `R` is carried alongside: the forward direction gets what it needs
from `Albrecht.exists_directSum_fg`.

Forward: Lemma 5.1 gives braidedness, then (iii) is 5.2(1), (ii) is 5.2(4), and (i) is the counting
argument.  Backward: `exists_braided_form` reduces arbitrary families to forms and
`braidedForms_of_conditions` runs the paper's four-case split; Corollary 4.7(1) then realises `H`,
which is where the Bergman–Dicks theorem enters. -/
theorem theorem_5_3 (k : Type u) [Field k]
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (∃ (R : Type u) (_ : Ring R) (_ : Algebra k R) (_ : IsHereditary R),
        ∃ e : V(R).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) ↔
      (Cond1 x₁ x₂ ∧ Cond1 x₂ x₁ ∧ Cond2 x₁ x₂ ∧ Cond2 x₂ x₁ ∧ NoMixedForms x₁ x₂) := by
  constructor
  · rintro ⟨R, _, -, _, e, hhom, hbij⟩
    exact theorem_5_3_forward x₁ x₂ R Albrecht.exists_directSum_fg hgen hnoncyclic e hhom hbij
  · rintro ⟨hc1, hc1', hc2, hc2', hmix⟩
    exact theorem_5_3_backward x₁ x₂ k hgen hc1 hc1' hc2 hc2' hmix

end Theorem53

end TwoGen

end KappaMonoid
