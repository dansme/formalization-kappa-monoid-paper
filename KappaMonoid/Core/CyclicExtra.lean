/-
Two complements to `Core/Cyclic.lean` (§2.2.1 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*):

* the remark before Lemma 2.15 that *the generator of a cyclic `κ`-monoid is always an
  order-unit*, `KMonoid.isOrderUnit_of_kGenerates`;
* the `κ`-sum half of Lemma 2.15.  The target `C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}` is given the obvious
  `κ`-sum `KMonoid.splitSum` — a family whose total size is finite is summed in `C₀`, any other
  family sums to its total size — and the bijection `equivFinitePartSumCard` of `Core/Cyclic.lean`
  is shown to be an isomorphism of `κ`-monoids, `KMonoid.lemma_2_15_kIso`.
-/
import KappaMonoid.Core.Cyclic
import KappaMonoid.ForMathlib.CardinalSum
import KappaMonoid.Core.AddOf

universe u v

open Cardinal

namespace KappaMonoid

namespace KMonoid

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-! ## The generator of a cyclic `κ`-monoid is an order-unit -/

/-- **§2.2.1, before Lemma 2.15**: *"The generator of a cyclic `κ`-monoid is always an
order-unit."*

Paper proof: every element is `α u` with `α ≤ κ` (`exists_cmul_of_kGenerates`), and
`α u ≼ κ u` because cardinal multiples are monotone in the cardinal (`cmul_le_cmul`). -/
theorem isOrderUnit_of_kGenerates {u : H} (hgen : KGenerates κ ({u} : Set H)) :
    IsOrderUnit (κ := κ) u := fun x => by
  obtain ⟨α, hα, rfl⟩ := exists_cmul_of_kGenerates hgen x
  exact cmul_le_cmul hα le_rfl hα u

/-! ## Lemma 2.15: the obvious `κ`-sum on `C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}` -/

theorem zero_mem_finitePart (u : H) : (0 : H) ∈ finitePart (κ := κ) u :=
  ⟨0, by rw [cmul_congr Nat.cast_zero _ zero_le, cmul_zero_cardinal]⟩

/-- The target of Lemma 2.15: `C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}`, with `C₀` the finite multiples of `u`. -/
abbrev Split (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (u : H) :=
  ↥(finitePart (κ := κ) u) ⊕ {α : Cardinal.{u} // ℵ₀ ≤ α ∧ α ≤ κ}

open Classical in
/-- The *size* of an element of `C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}`: `0` for `0`, `1` for the other
elements of `C₀` and `α` for `α`.  A family of such elements has finite total size exactly when
it consists of finitely many nonzero elements of `C₀`. -/
noncomputable def splitSize {u : H} : Split κ u → Cardinal.{u} :=
  Sum.elim (fun c => if (c : H) = 0 then 0 else 1) (fun a => (a : Cardinal.{u}))

/-- The `C₀`-component of an element of `C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}`, and `0` on the second
summand. -/
def splitLeft {u : H} : Split κ u → H := Sum.elim (fun c => (c : H)) (fun _ => 0)

theorem splitSize_le {u : H} (t : Split κ u) : splitSize t ≤ κ := by
  rcases t with c | a
  · classical
    show (if (c : H) = 0 then 0 else 1) ≤ κ
    split_ifs
    exacts [zero_le, le_trans (le_of_lt Cardinal.one_lt_aleph0) (aleph0_le (κ := κ) (H := H))]
  · exact a.2.2

theorem sum_splitSize_le {u : H} {ι : Type u} (hι : #ι ≤ κ) (t : ι → Split κ u) :
    Cardinal.sum (fun i => splitSize (t i)) ≤ κ := by
  refine (Cardinal.sum_le_mk_mul_iSup _).trans ?_
  calc #ι * ⨆ i, splitSize (t i) ≤ κ * κ :=
        mul_le_mul' hι (ciSup_le' fun i => splitSize_le (t i))
    _ = κ := Cardinal.mul_eq_self (aleph0_le (κ := κ) (H := H))

theorem finsum_splitLeft_mem {u : H} {ι : Type u} (t : ι → Split κ u) :
    ∑ᶠ i, splitLeft (t i) ∈ finitePart (κ := κ) u := by
  refine finsum_induction (· ∈ finitePart (κ := κ) u) (zero_mem_finitePart u)
    (fun a b ha hb => (lemma_2_15_add u).1 a ha b hb) fun i => ?_
  rcases t i with c | a
  exacts [c.2, zero_mem_finitePart u]

/-- **Lemma 2.15**, *"the obvious operation"*: the `κ`-sum on `C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}`.  Sizes
add: a family of finite total size (finitely many nonzero terms, all in `C₀`) is summed in the
monoid `C₀`, and any other family sums to its total size, an infinite cardinal `≤ κ`.

Only the additive monoid `C₀` enters the definition, not the rest of `H`. -/
noncomputable def splitSum {u : H} {ι : Type u} (hι : #ι ≤ κ) (t : ι → Split κ u) :
    Split κ u :=
  if hfin : Cardinal.sum (fun i => splitSize (t i)) < ℵ₀ then
    Sum.inl ⟨∑ᶠ i, splitLeft (t i), finsum_splitLeft_mem t⟩
  else Sum.inr ⟨Cardinal.sum (fun i => splitSize (t i)), not_lt.mp hfin, sum_splitSize_le hι t⟩

/-- **Lemma 2.15**, the sums: the bijection `equivFinitePartSumCard` carries the obvious sum
`splitSum` to the `κ`-sum of `H`.

Paper proof: write each term as `m_i u`.  If the total size is finite, finitely many terms are
nonzero and all lie in `C₀`, so the `κ`-sum is a finite sum in `C₀`.  Otherwise the sum is
`(Σ m_i) u` by Lemma 2.7(2), and `Σ m_i` is the total size: the finite `m_i ≠ 0` have size `1`,
and `size ≤ m_i ≤ ℵ₀ · size` termwise, while the total size is infinite. -/
theorem equivFinitePartSumCard_splitSum {u : H} (hu : IsFaithful (κ := κ) u)
    (hgen : KGenerates κ ({u} : Set H)) {ι : Type u} (hι : #ι ≤ κ) (t : ι → Split κ u) :
    equivFinitePartSumCard hu hgen (splitSum hι t)
      = ∑[≤ κ] i, equivFinitePartSumCard hu hgen (t i) := by
  classical
  set E := equivFinitePartSumCard hu hgen with hEdef
  have hEl : ∀ c, E (Sum.inl c) = (c : H) := fun _ => rfl
  have hEr : ∀ a : {α : Cardinal.{u} // ℵ₀ ≤ α ∧ α ≤ κ},
      E (Sum.inr a) = cmul (κ := κ) a a.2.2 u := fun _ => rfl
  unfold splitSum
  split_ifs with hfin
  · -- finite total size: finitely many nonzero terms, all in `C₀`
    rw [hEl]
    have hleft : ∀ i, E (t i) = splitLeft (t i) := by
      intro i
      have hle := Cardinal.le_sum (fun i => splitSize (t i)) i
      rcases hti : t i with c | a
      · rfl
      · rw [hti] at hle
        exact absurd (lt_of_le_of_lt (a.2.1.trans hle) hfin) (lt_irrefl _)
    simp only [hleft]
    have hsub : Function.support (fun i => splitLeft (t i))
        ⊆ Function.support (fun i => splitSize (t i)) := by
      intro i hi
      rcases hti : t i with c | a
      · have hc : (c : H) ≠ 0 := by
          intro h0; apply hi; show splitLeft (t i) = 0; rw [hti]; exact h0
        show splitSize (t i) ≠ 0
        rw [hti]
        show (if (c : H) = 0 then 0 else 1) ≠ 0
        rw [if_neg hc]
        exact one_ne_zero
      · show splitSize (t i) ≠ 0
        rw [hti]
        exact (lt_of_lt_of_le Cardinal.aleph0_pos a.2.1).ne'
    have hfinS : (Function.support fun i => splitLeft (t i)).Finite :=
      Cardinal.lt_aleph0_iff_set_finite.mp
        (((Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_support_le_sum _)).trans_lt hfin)
    have hκS : #(Function.support fun i => splitLeft (t i)) ≤ κ :=
      (Cardinal.lt_aleph0_iff_set_finite.mpr hfinS).le.trans (aleph0_le (κ := κ) (H := H))
    let _ : Fintype (Function.support fun i => splitLeft (t i)) := hfinS.fintype
    rw [sumOf_subtype_support (h := CardLE.mk' hι) _, sumOf_eq_sum (h := CardLE.mk' hκS), ← finsum_eq_sum_of_fintype,
      finsum_set_coe_eq_finsum_mem (f := fun i => splitLeft (t i)),
      finsum_mem_support (fun i => splitLeft (t i))]
  · -- infinite total size: write each term as `m_i u` with `size ≤ m_i ≤ ℵ₀ · size`
    rw [hEr]
    have hm : ∀ y : Split κ u, ∃ m : Cardinal.{u}, ∃ hm : m ≤ κ,
        E y = cmul (κ := κ) m hm u ∧ splitSize y ≤ m ∧ m ≤ splitSize y * ℵ₀ := by
      rintro (c | a)
      · by_cases hc : (c : H) = 0
        · have hsz : splitSize (Sum.inl c : Split κ u) = 0 := if_pos hc
          refine ⟨0, zero_le, ?_, hsz.le, zero_le⟩
          rw [hEl, hc, cmul_zero_cardinal]
        · have hsz : splitSize (Sum.inl c : Split κ u) = 1 := if_neg hc
          obtain ⟨n, hn⟩ := c.2
          have hn0 : (n : Cardinal.{u}) ≠ 0 := by
            intro h0
            apply hc
            rw [hn, cmul_congr h0 _ zero_le, cmul_zero_cardinal]
          refine ⟨n, _, hn, ?_, ?_⟩
          · rw [hsz]
            exact Cardinal.one_le_iff_ne_zero.mpr hn0
          · rw [hsz, one_mul]
            exact le_of_lt Cardinal.natCast_lt_aleph0
      · exact ⟨a, a.2.2, rfl, le_rfl, Cardinal.le_mul_right Cardinal.aleph0_ne_zero⟩
    choose m hmκ hEm hlo hhi using hm
    have hs0 : ℵ₀ ≤ Cardinal.sum (fun i => splitSize (t i)) := not_lt.mp hfin
    have hM : Cardinal.sum (fun i => m (t i)) = Cardinal.sum (fun i => splitSize (t i)) :=
      le_antisymm
        ((Cardinal.sum_le_sum _ _ fun i => hhi (t i)).trans_eq
          (by rw [Cardinal.sum_mul_const, Cardinal.mul_aleph0_eq hs0]))
        (Cardinal.sum_le_sum _ _ fun i => hlo (t i))
    rw [show (fun i => E (t i)) = fun i => cmul (κ := κ) (m (t i)) (hmκ (t i)) u from
        funext fun i => hEm (t i),
      ← cmul_sumOf_cardinal (hI := CardLE.mk' hι) (fun i => m (t i)) (fun i => hmκ (t i)) (hM.trans_le (sum_splitSize_le hι t))]
    exact cmul_congr hM.symm _ _ u

/-- The summation data of the obvious `κ`-sum.  Its axioms are checked by transport along the
bijection `equivFinitePartSumCard`, which is where faithfulness and generation are used. -/
noncomputable def splitSumData {u : H} (hu : IsFaithful (κ := κ) u)
    (hgen : KGenerates κ ({u} : Set H)) : SumData (Order.succ κ) (Split κ u) where
  isRegular := isRegular_succ' (H := H)
  sum := fun h t => splitSum (le_of_lt_succ h) t
  sum_congr := fun h h' e x => (equivFinitePartSumCard hu hgen).injective (by
    show equivFinitePartSumCard hu hgen (splitSum _ (x ∘ e))
      = equivFinitePartSumCard hu hgen (splitSum _ x)
    rw [equivFinitePartSumCard_splitSum, equivFinitePartSumCard_splitSum]
    exact (sumOf_equiv (h := ⟨h'⟩) (h' := ⟨h⟩) e (fun i => equivFinitePartSumCard hu hgen (x i))).symm)
  sum_unique := fun h x => (equivFinitePartSumCard hu hgen).injective (by
    show equivFinitePartSumCard hu hgen (splitSum _ x) = equivFinitePartSumCard hu hgen (x default)
    rw [equivFinitePartSumCard_splitSum, sumOf_unique (h := ⟨h⟩)])
  sum_sigma := fun {ι} {ρ} h hρ x hσ => (equivFinitePartSumCard hu hgen).injective (by
    show equivFinitePartSumCard hu hgen (splitSum _ fun i => splitSum _ (x i))
      = equivFinitePartSumCard hu hgen (splitSum _ fun p : (i : ι) × ρ i => x p.1 p.2)
    simp only [equivFinitePartSumCard_splitSum]
    exact sumOf_sigma (h := ⟨h⟩) (hρ := fun i => ⟨hρ i⟩) (fun i r => equivFinitePartSumCard hu hgen (x i r)))

/-- **Lemma 2.15**: `C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}` with the obvious operation `splitSum` is a
`κ`-monoid. -/
@[instance_reducible]
noncomputable def splitKMonoid {u : H} (hu : IsFaithful (κ := κ) u)
    (hgen : KGenerates κ ({u} : Set H)) : KMonoid κ (Split κ u) :=
  { toLMonoid := LMonoid.ofSumData (splitSumData hu hgen)
    aleph0_le := aleph0_le (κ := κ) (H := H) }

/-- The sums of `splitKMonoid` are the obvious ones. -/
theorem splitKMonoid_sumOf {u : H} (hu : IsFaithful (κ := κ) u)
    (hgen : KGenerates κ ({u} : Set H)) {ι : Type u} (hι : #ι ≤ κ) (t : ι → Split κ u) :
    letI := splitKMonoid hu hgen
    ∑[≤ κ] i, t i = splitSum hι t := rfl

/-- **Lemma 2.15**: a cyclic `κ`-monoid `H` generated by a faithful order-unit `u` is isomorphic,
as a `κ`-monoid, to `C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}` with the obvious operation: the bijection
`n u ↦ n u`, `α u ↦ α` of `equivFinitePartSumCard` (read backwards) is a `κ`-homomorphism in
both directions.

Paper proof: faithfulness makes `α ↦ α u` injective on infinite cardinals and keeps its image
disjoint from `C₀` (`lemma_2_15`); that the sums correspond is
`equivFinitePartSumCard_splitSum`. -/
theorem lemma_2_15_kIso {u : H} (hu : IsFaithful (κ := κ) u)
    (hgen : KGenerates κ ({u} : Set H)) :
    letI := splitKMonoid hu hgen
    IsKHom κ (equivFinitePartSumCard hu hgen) ∧ IsKHom κ (equivFinitePartSumCard hu hgen).symm ∧
      Function.Bijective (equivFinitePartSumCard hu hgen) := by
  let _ := splitKMonoid hu hgen
  have hE : IsKHom κ (equivFinitePartSumCard hu hgen) := by
    refine ⟨?_, fun x => ?_⟩
    · show equivFinitePartSumCard hu hgen (splitSum (mk_le_of_finite (H := H) PEmpty.{u + 1})
        (PEmpty.elim : PEmpty.{u + 1} → _)) = 0
      rw [equivFinitePartSumCard_splitSum,
        sumOf_of_isEmpty (h := CardLE.mk' (mk_le_of_finite (H := H) PEmpty.{u + 1}))]
    · show equivFinitePartSumCard hu hgen (splitSum (le_of_eq (mk_Idx κ)) x) = _
      rw [equivFinitePartSumCard_splitSum]
      rfl
  exact ⟨hE, hE.inv (equivFinitePartSumCard hu hgen).bijective
    (equivFinitePartSumCard hu hgen).rightInverse_symm, (equivFinitePartSumCard hu hgen).bijective⟩


section AddOfCard

variable {H' : Type u} [KMonoid κ H']

/-- **`add_λ(x) = add(⟨x⟩_λ)`** (tex 1783): the summands of `λx` are the summands of the elements of
`⟨x⟩_λ = {αx : α ≤ λ}` (a set already closed under finite sums), for infinite `λ ≤ κ`.

Paper proof: stated without proof.  If `y + z = αx` with `α ≤ λ`, then
`y + (z + λx) = (α + λ)x = λx`, since `α + λ = λ` for infinite `λ`; the converse takes `α = λ`. -/
theorem addOfCard_eq_add_closure {lam : Cardinal.{u}} (hlam0 : ℵ₀ ≤ lam) (hlam : lam ≤ κ)
    (x : H') :
    addOfCard (κ := κ) hlam x
      = {y | ∃ (z : H') (α : Cardinal.{u}) (hα : α ≤ lam),
          y + z = cmul (κ := κ) α (hα.trans hlam) x} := by
  ext y
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, lam, le_rfl, hz⟩
  · rintro ⟨z, α, hα, hz⟩
    have hαl : α + lam = lam := Cardinal.add_eq_right hlam0 hα
    refine ⟨z + cmul (κ := κ) lam hlam x, ?_⟩
    rw [← add_assoc, hz, ← cmul_add (hα.trans hlam) hlam (hαl.le.trans hlam)]
    exact cmul_congr hαl _ _ x

end AddOfCard

end KMonoid

end KappaMonoid
