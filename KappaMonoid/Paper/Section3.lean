/-
**Section 3 of the paper**: an index of its numbered results.

Each entry names the paper result, and the declaration that formalises it.  Unlike
`Paper/Section5.lean`, which restates §5 in the paper's own terms, this file is an index: the
`alias` checks that the declaration exists and carries the type it is claimed to have, and the
docstring says which paper result it stands for.  Follow the name to read the statement.

Results the development deliberately does not formalise are recorded at the foot of the file.
-/
import KappaMonoid.Modules.Corollary47
import KappaMonoid.Modules.Rings.Realisation
import KappaMonoid.Modules.Rings.Semisimple
import KappaMonoid.Examples
import KappaMonoid.Core.Cyclic
import KappaMonoid.Paper.Definition21

namespace KappaMonoid

namespace Paper

/-- **Definition 3.1(1)** — `KappaMonoid.IsBraided`, in `Braiding/Defs.lean`. -/
alias definition_3_1_1_IsBraided := KappaMonoid.IsBraided

/-- **Definition 3.1(2)** — `KappaMonoid.IsBraidedOver`, in `Braiding/Over.lean`. -/
alias definition_3_1_2_IsBraidedOver := KappaMonoid.IsBraidedOver

/-- **Lemma 3.2 (telescoping)** — `KappaMonoid.sumOf_eq_of_isBraided`, in `Braiding/Sums.lean`. -/
alias lemma_3_2_telescoping_sumOf_eq_of_isBraided := KappaMonoid.sumOf_eq_of_isBraided

/-- **Examples 3.3(2)** — `KappaMonoid.RTilde.instKMonoid`, in `Examples/Reals.lean`. -/
alias examples_3_3_2_instKMonoid := KappaMonoid.RTilde.instKMonoid

/-- **Examples 3.3(2)** — `KappaMonoid.RTilde.isBraidedOver_rtilde`, in `Examples/Reals.lean`. -/
alias examples_3_3_2_isBraidedOver_rtilde := KappaMonoid.RTilde.isBraidedOver_rtilde

/-- **Examples 3.3(2)** — `KappaMonoid.RTilde.not_isBraidedOver_rtilde_self`, in `Examples/Reals.lean`. -/
alias examples_3_3_2_not_isBraidedOver_rtilde_self := KappaMonoid.RTilde.not_isBraidedOver_rtilde_self

/-- **Examples 3.3(1)** — `KappaMonoid.isBraidedOver_withTop_nat`, in `Examples/NatBraiding.lean`. -/
alias examples_3_3_1_isBraidedOver_withTop_nat := KappaMonoid.isBraidedOver_withTop_nat

/-- **Examples 3.3(1)** — `KappaMonoid.isBraided_nat_of_infinite_support`, in `Examples/NatBraiding.lean`. -/
alias examples_3_3_1_isBraided_nat_of_infinite_support := KappaMonoid.isBraided_nat_of_infinite_support

/-- **Examples 3.3(2)** — `KappaMonoid.isBraided_nnreal_iff`, in `Examples/NNReal.lean`. -/
alias examples_3_3_2_isBraided_nnreal_iff := KappaMonoid.isBraided_nnreal_iff

/-- **Examples 3.3(2)** — `KappaMonoid.isBraided_nnreal_of_infinite_support`, in `Examples/NNReal.lean`. -/
alias examples_3_3_2_isBraided_nnreal_of_infinite_support := KappaMonoid.isBraided_nnreal_of_infinite_support

/-- **Examples 3.3(3)** — `KappaMonoid.isUniversalKExtension_ratSet`, in `Examples/Reals.lean`. -/
alias examples_3_3_3_isUniversalKExtension_ratSet := KappaMonoid.isUniversalKExtension_ratSet

/-- **Examples 3.3(3)** — `KappaMonoid.kclosure_ofReal_ratSet`, in `Examples/Reals.lean`. -/
alias examples_3_3_3_kclosure_ofReal_ratSet := KappaMonoid.kclosure_ofReal_ratSet

/-- **Examples 3.3(2)** — `KappaMonoid.not_isBraided_geom_two_geom`, in `Examples/NNReal.lean`. -/
alias examples_3_3_2_not_isBraided_geom_two_geom := KappaMonoid.not_isBraided_geom_two_geom

/-- **Examples 3.3(2)** — `KappaMonoid.not_isBraided_single2_geom`, in `Examples/NNReal.lean`. -/
alias examples_3_3_2_not_isBraided_single2_geom := KappaMonoid.not_isBraided_single2_geom

/-- **Examples 3.3(3)** — `KappaMonoid.ofReal_notMem_kclosure_of_not_mem_ratSet`, in `Examples/Reals.lean`. -/
alias examples_3_3_3_ofReal_notMem_kclosure_of_not_mem_ratSet := KappaMonoid.ofReal_notMem_kclosure_of_not_mem_ratSet

/-- **Lemma 3.4(4)** — `KappaMonoid.isBraided_iff_of_ne_aleph0`, in `Braiding/Sums.lean`. -/
alias lemma_3_4_4_isBraided_iff_of_ne_aleph0 := KappaMonoid.isBraided_iff_of_ne_aleph0

/-- **Lemma 3.4(1)** — `KappaMonoid.isBraided_of_small_support`, in `Braiding/Sums.lean`. -/
alias lemma_3_4_1_isBraided_of_small_support := KappaMonoid.isBraided_of_small_support

/-- **Definition 3.1(1) over an arbitrary limit well-order** — `KappaMonoid.BraidingDataOn`, in
`Braiding/WellOrder.lean`: the definition as the paper states it, with the successor and the limit
elements taken from an index structure `LimitSucc` rather than from the `ι × ℕ` normal form. -/
alias definition_3_1_1_BraidingDataOn := KappaMonoid.BraidingDataOn

/-- **Lemma 3.5** — `KappaMonoid.isBraidedOn_iff_isBraided`, in `Braiding/WellOrder.lean`:
braidedness with respect to any limit well-order on an index set of the same size as the family
index set is `IsBraided`.  This is what licenses the `ι × ℕ` normal form of `BraidingData`. -/
alias lemma_3_5_isBraidedOn_iff_isBraided := KappaMonoid.isBraidedOn_iff_isBraided

/-- **Lemma 3.5** as printed — `KappaMonoid.isBraidedOn_congr_self`, in
`Braiding/WellOrder.lean`: being `λ⁻`-braided does not depend on the choice of limit well-order. -/
alias lemma_3_5_isBraidedOn_congr_self := KappaMonoid.isBraidedOn_congr_self

/-- **Lemma 3.5** for a well-order given by the order instances on the index type —
`KappaMonoid.isBraidedOn_ofWellOrder_iff`, in `Braiding/WellOrder.lean`. -/
alias lemma_3_5_isBraidedOn_ofWellOrder_iff := KappaMonoid.isBraidedOn_ofWellOrder_iff

/-- **Lemma 3.6(1)** — `KappaMonoid.IsBraided.of_perm`, in `Braiding/Defs.lean`. -/
alias lemma_3_6_1_of_perm := KappaMonoid.IsBraided.of_perm

/-- **Lemma 3.6(2), reflexivity** — `KappaMonoid.IsBraided.refl`, in `Braiding/Defs.lean`. -/
alias lemma_3_6_2_reflexivity_refl := KappaMonoid.IsBraided.refl

/-- **Lemma 3.6(2), symmetry** — `KappaMonoid.IsBraided.symm`, in `Braiding/Defs.lean`. -/
alias lemma_3_6_2_symmetry_symm := KappaMonoid.IsBraided.symm

/-- **Lemma 3.7 (`λ = ℵ₀`)** — `KappaMonoid.IsBraided.exists_aligned`, in `Braiding/TransAleph0.lean`. -/
alias lemma_3_7_exists_aligned := KappaMonoid.IsBraided.exists_aligned

/-- **Lemma 3.8's combinatorial core** — `KappaMonoid.IsBraided.of_aligned`, in `Braiding/TransAleph0.lean`. -/
alias lemma_3_8_s_combinatorial_core_of_aligned := KappaMonoid.IsBraided.of_aligned

/-- **Lemma 3.8, transitivity** — `KappaMonoid.IsBraided.trans`, in `Braiding/TransUncountable.lean`. -/
alias lemma_3_8_transitivity_trans := KappaMonoid.IsBraided.trans

/-- **Lemma 3.8** — `KappaMonoid.braidingSetoid`, in `Braiding/TransUncountable.lean`. -/
alias lemma_3_8_braidingSetoid := KappaMonoid.braidingSetoid

/-- **Proposition 3.10** — `KappaMonoid.extend_lhom`, in `Braiding/Prop310.lean`. -/
alias proposition_3_10_extend_lhom := KappaMonoid.extend_lhom

/-- **Definition 3.11** — `KappaMonoid.IsUniversalKExtension`, in `Braiding/Prop310.lean`. -/
alias definition_3_11_IsUniversalKExtension := KappaMonoid.IsUniversalKExtension

/-- **Theorem 3.12 as an equivalence** — `KappaMonoid.isBraidedOver_of_isUniversalKExtension`, in `Braiding/UnivExt.lean`. -/
alias theorem_3_12_as_an_equivalence_isBraidedOver_of_isUniversalKExtension := KappaMonoid.isBraidedOver_of_isUniversalKExtension

/-- **Theorem 3.12** — `KappaMonoid.theorem_3_12`, in `Braiding/UnivExt.lean`. -/
alias theorem_3_12_theorem_3_12 := KappaMonoid.theorem_3_12

/-- **Theorem 3.12** — `KappaMonoid.theorem_3_12_of_aleph0_lt`, in `Braiding/UnivExt.lean`. -/
alias theorem_3_12_theorem_3_12_of_aleph0_lt := KappaMonoid.theorem_3_12_of_aleph0_lt

/-- **Examples 3.13** — `KappaMonoid.RTilde.isUniversalKExtension_rtilde`, in `Examples/Reals.lean`. -/
alias examples_3_13_isUniversalKExtension_rtilde := KappaMonoid.RTilde.isUniversalKExtension_rtilde

/-- **Examples 3.13** — `KappaMonoid.isUniversalKExtension_withTop_nat`, in `Examples/NatBraiding.lean`. -/
alias examples_3_13_isUniversalKExtension_withTop_nat := KappaMonoid.isUniversalKExtension_withTop_nat

/-- **Lemma 3.14(2)** — `KappaMonoid.isBraidedOver_of_isLSubmonoid`, in `Braiding/Saturated.lean`. -/
alias lemma_3_14_2_isBraidedOver_of_isLSubmonoid := KappaMonoid.isBraidedOver_of_isLSubmonoid

/-- **Lemma 3.14(1)** — `KappaMonoid.lemma_3_14_free`, in `Braiding/Saturated.lean`. -/
alias lemma_3_14_1_lemma_3_14_free := KappaMonoid.lemma_3_14_free

/-- **Lemma 3.14(2)** — `KappaMonoid.lemma_3_14_sub`, in `Braiding/Saturated.lean`. -/
alias lemma_3_14_2_lemma_3_14_sub := KappaMonoid.lemma_3_14_sub

/-- **Lemma 3.14(2)** — `KappaMonoid.lemma_3_14_sub_of_subset`, in `Braiding/Saturated.lean`. -/
alias lemma_3_14_2_lemma_3_14_sub_of_subset := KappaMonoid.lemma_3_14_sub_of_subset

/-- **Proposition 3.15(1)** — `KappaMonoid.prop_3_15_one`, in `Examples/Diophantine.lean`. -/
alias proposition_3_15_1_prop_3_15_one := KappaMonoid.prop_3_15_one

/-- **Proposition 3.15(2)** — `KappaMonoid.prop_3_15_two_of_ineqs_empty`, in
`Examples/Diophantine.lean`: for a system of equations and congruences, which is what the
proposition is stated for. -/
alias proposition_3_15_2_prop_3_15_two_of_ineqs_empty := KappaMonoid.prop_3_15_two_of_ineqs_empty

/-- **Proposition 3.15(2)**, generalised — `KappaMonoid.prop_3_15_two`, in
`Examples/Diophantine.lean`: the same conclusion for any system whose solution monoid is
saturated in `ℕ₀^n`, which is what the proof actually needs. -/
alias proposition_3_15_2_prop_3_15_two := KappaMonoid.prop_3_15_two

/-- **Example 3.16** — `KappaMonoid.example_3_16`, in `Examples/Diophantine.lean`. -/
alias example_3_16_example_3_16 := KappaMonoid.example_3_16

/-- **Example 3.17**, `H` is not saturated — `KappaMonoid.not_isSaturatedFin_ineqSystem`, in
`Examples/Diophantine.lean`. -/
alias example_3_17_not_saturated := KappaMonoid.not_isSaturatedFin_ineqSystem

/-- **Example 3.17**, the two families are not braided —
`KappaMonoid.not_isBraidedOver_ineqSystem`, in `Examples/Diophantine.lean`. -/
alias example_3_17_not_braided := KappaMonoid.not_isBraidedOver_ineqSystem

/-- **Example 3.17**: for `H = {(a,b) ∈ ℕ₀² : a ≤ b}` the monoid `H + ℵ₀H` is *not* the universal
`ℵ₀`-extension of `H` — `KappaMonoid.not_prop_3_15_two_ineqSystem`, in
`Examples/Diophantine.lean`.  This is why Proposition 3.15(2) excludes inequalities. -/
alias example_3_17_not_universal := KappaMonoid.not_prop_3_15_two_ineqSystem

/-- **Example 3.17**, the repair — `KappaMonoid.example_3_17_slack_iso`, in
`Examples/Diophantine.lean`: `H ≅ H' = {(a,b,c) ∈ ℕ₀³ : b = a + c}`, a system of equations, to
which Proposition 3.15(2) does apply. -/
alias example_3_17_slack_iso := KappaMonoid.example_3_17_slack_iso



/-! ## Not formalised, deliberately

* **Lemma 3.4(2)(3)**.  A braiding decomposes into a disjoint union of countable braidings, one per
  limit element, and conversely.  In the paper this is a step towards Lemma 3.5, which is proved
  here directly (`isBraidedOn_iff_isBraided`) from the `ω`-block decomposition of a limit
  well-order, so the intermediate statement is not needed.  See `README.md`, "The limit
  well-order".
* **Remark 3.9**.  Why transitivity of braiding is easy for `λ > ℵ₀`: the common coarsening of two
  partitions into `< λ`-sized pieces is again into `< λ`-sized pieces, by regularity.  A sketch
  motivating Lemma 3.8, whose proof is formalised in full (`IsBraided.trans`).
* **Remark 3.18**.  Saturated submonoids of `ℕ₀^n` are finitely generated reduced Krull monoids —
  a pointer to the literature, not a theorem of the paper. -/

end Paper

end KappaMonoid
