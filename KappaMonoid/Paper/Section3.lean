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

/-- **Examples 3.3(1)** — `KappaMonoid.isBraidedOver_withTop_nat`, in `Examples/Diophantine.lean`. -/
alias examples_3_3_1_isBraidedOver_withTop_nat := KappaMonoid.isBraidedOver_withTop_nat

/-- **Examples 3.3(1)** — `KappaMonoid.isBraided_nat_of_infinite_support`, in `Examples/Diophantine.lean`. -/
alias examples_3_3_1_isBraided_nat_of_infinite_support := KappaMonoid.isBraided_nat_of_infinite_support

/-- **Examples 3.3(2)** — `KappaMonoid.isBraided_nnreal_iff`, in `Examples/Reals.lean`. -/
alias examples_3_3_2_isBraided_nnreal_iff := KappaMonoid.isBraided_nnreal_iff

/-- **Examples 3.3(2)** — `KappaMonoid.isBraided_nnreal_of_infinite_support`, in `Examples/Reals.lean`. -/
alias examples_3_3_2_isBraided_nnreal_of_infinite_support := KappaMonoid.isBraided_nnreal_of_infinite_support

/-- **Examples 3.3(3)** — `KappaMonoid.isUniversalKExtension_ratSet`, in `Examples/Reals.lean`. -/
alias examples_3_3_3_isUniversalKExtension_ratSet := KappaMonoid.isUniversalKExtension_ratSet

/-- **Examples 3.3(3)** — `KappaMonoid.kclosure_ofReal_ratSet`, in `Examples/Reals.lean`. -/
alias examples_3_3_3_kclosure_ofReal_ratSet := KappaMonoid.kclosure_ofReal_ratSet

/-- **Examples 3.3(2)** — `KappaMonoid.not_isBraided_geom_two_geom`, in `Examples/Reals.lean`. -/
alias examples_3_3_2_not_isBraided_geom_two_geom := KappaMonoid.not_isBraided_geom_two_geom

/-- **Examples 3.3(2)** — `KappaMonoid.not_isBraided_single2_geom`, in `Examples/Reals.lean`. -/
alias examples_3_3_2_not_isBraided_single2_geom := KappaMonoid.not_isBraided_single2_geom

/-- **Examples 3.3(3)** — `KappaMonoid.ofReal_notMem_kclosure_of_not_mem_ratSet`, in `Examples/Reals.lean`. -/
alias examples_3_3_3_ofReal_notMem_kclosure_of_not_mem_ratSet := KappaMonoid.ofReal_notMem_kclosure_of_not_mem_ratSet

/-- **Lemma 3.4(4)** — `KappaMonoid.isBraided_iff_of_ne_aleph0`, in `Braiding/Sums.lean`. -/
alias lemma_3_4_4_isBraided_iff_of_ne_aleph0 := KappaMonoid.isBraided_iff_of_ne_aleph0

/-- **Lemma 3.4(1)** — `KappaMonoid.isBraided_of_small_support`, in `Braiding/Sums.lean`. -/
alias lemma_3_4_1_isBraided_of_small_support := KappaMonoid.isBraided_of_small_support

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

/-- **Proposition 3.9** — `KappaMonoid.extend_lhom`, in `Braiding/Prop39.lean`. -/
alias proposition_3_9_extend_lhom := KappaMonoid.extend_lhom

/-- **Definition 3.10** — `KappaMonoid.IsUniversalKExtension`, in `Braiding/Prop39.lean`. -/
alias definition_3_10_IsUniversalKExtension := KappaMonoid.IsUniversalKExtension

/-- **Theorem 3.11 as an equivalence** — `KappaMonoid.isBraidedOver_of_isUniversalKExtension`, in `Braiding/UnivExt.lean`. -/
alias theorem_3_11_as_an_equivalence_isBraidedOver_of_isUniversalKExtension := KappaMonoid.isBraidedOver_of_isUniversalKExtension

/-- **Theorem 3.11** — `KappaMonoid.theorem_3_11`, in `Braiding/UnivExt.lean`. -/
alias theorem_3_11_theorem_3_11 := KappaMonoid.theorem_3_11

/-- **Theorem 3.11** — `KappaMonoid.theorem_3_11_of_aleph0_lt`, in `Braiding/UnivExt.lean`. -/
alias theorem_3_11_theorem_3_11_of_aleph0_lt := KappaMonoid.theorem_3_11_of_aleph0_lt

/-- **Examples 3.12** — `KappaMonoid.RTilde.isUniversalKExtension_rtilde`, in `Examples/Reals.lean`. -/
alias examples_3_12_isUniversalKExtension_rtilde := KappaMonoid.RTilde.isUniversalKExtension_rtilde

/-- **Examples 3.12** — `KappaMonoid.isUniversalKExtension_withTop_nat`, in `Examples/Diophantine.lean`. -/
alias examples_3_12_isUniversalKExtension_withTop_nat := KappaMonoid.isUniversalKExtension_withTop_nat

/-- **Lemma 3.13(2)** — `KappaMonoid.isBraidedOver_of_isLSubmonoid`, in `Braiding/Saturated.lean`. -/
alias lemma_3_13_2_isBraidedOver_of_isLSubmonoid := KappaMonoid.isBraidedOver_of_isLSubmonoid

/-- **Lemma 3.13(1)** — `KappaMonoid.lemma_3_13_free`, in `Braiding/Saturated.lean`. -/
alias lemma_3_13_1_lemma_3_13_free := KappaMonoid.lemma_3_13_free

/-- **Lemma 3.13(2)** — `KappaMonoid.lemma_3_13_sub`, in `Braiding/Saturated.lean`. -/
alias lemma_3_13_2_lemma_3_13_sub := KappaMonoid.lemma_3_13_sub

/-- **Lemma 3.13(2)** — `KappaMonoid.lemma_3_13_sub_of_subset`, in `Braiding/Saturated.lean`. -/
alias lemma_3_13_2_lemma_3_13_sub_of_subset := KappaMonoid.lemma_3_13_sub_of_subset

/-- **Proposition 3.14(1)** — `KappaMonoid.prop_3_14_one`, in `Examples/Diophantine.lean`. -/
alias proposition_3_14_1_prop_3_14_one := KappaMonoid.prop_3_14_one

/-- **Proposition 3.14(2)** — `KappaMonoid.prop_3_14_two`, in `Examples/Diophantine.lean`. -/
alias proposition_3_14_2_prop_3_14_two := KappaMonoid.prop_3_14_two

/-- **Proposition 3.14(2) for a system of equations and congruences** — `KappaMonoid.prop_3_14_two_of_ineqs_empty`, in `Examples/Diophantine.lean`. -/
alias proposition_3_14_2_for_a_system_of_equations_and_congruences_prop_3_14_two_of_ineqs_empty := KappaMonoid.prop_3_14_two_of_ineqs_empty

/-- **Example 3.15** — `KappaMonoid.example_3_15`, in `Examples/Diophantine.lean`. -/
alias example_3_15_example_3_15 := KappaMonoid.example_3_15


/-! ## Not formalised, deliberately

* **Lemma 3.4(2)(3)** and **Lemma 3.5**.  A braiding decomposes into countable braidings and
  conversely, and the relation does not depend on the chosen limit well-order.  The `ι × ℕ` normal
  form of `BraidingData` *is* their content: restating them would mean reintroducing abstract
  limit well-orders purely to prove they do not matter.  See `README.md`, "The limit well-order".
* **Remark 3.16**.  Saturated submonoids of `ℕ₀^n` are finitely generated reduced Krull monoids —
  a pointer to the literature, not a theorem of the paper.
* The braiding half of the counterexample to Proposition 3.14(2): only the failure of saturation
  is formalised (`not_isSaturatedFin_ineqSystem`), the braiding computation being recorded in its
  docstring. -/

end Paper

end KappaMonoid
