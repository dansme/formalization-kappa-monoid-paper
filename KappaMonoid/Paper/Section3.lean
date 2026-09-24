/-
**Section 3 of the paper**: an index of its numbered results.

Each entry names the paper result, and the declaration that formalises it.  Unlike
`Paper/Section5.lean`, which restates §5 in the paper's own terms, this file is an index: the
`alias` checks only that the declaration exists — it copies the target's type, so it does not check
what that type is — and the docstring says which paper result it stands for.  Follow the name, or
`#check` the alias, to read the statement.

Results the development deliberately does not formalise are recorded at the foot of the file.
-/
import KappaMonoid.Modules.Corollary47
import KappaMonoid.Modules.Rings.Realisation
import KappaMonoid.Modules.Rings.Semisimple
import KappaMonoid.Examples
import KappaMonoid.Braiding.Components
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

/-- **Examples 3.3(1)**, the characterization — `KappaMonoid.isBraided_nat_iff`: two families in
`ℕ₀` are braided iff both have finite support and equal sums, or both have infinite support. -/
alias examples_3_3_1_isBraided_nat_iff := KappaMonoid.isBraided_nat_iff

/-- **Examples 3.3(2)** — `KappaMonoid.isBraided_nnreal_iff`, in `Examples/NNReal.lean`. -/
alias examples_3_3_2_isBraided_nnreal_iff := KappaMonoid.isBraided_nnreal_iff

/-- **Examples 3.3(2)** — `KappaMonoid.isBraided_nnreal_of_infinite_support`, in `Examples/NNReal.lean`. -/
alias examples_3_3_2_isBraided_nnreal_of_infinite_support := KappaMonoid.isBraided_nnreal_of_infinite_support

/-- **Examples 3.3(3)** — `KappaMonoid.isUniversalKExtension_ratSet`, in `Examples/Reals.lean`. -/
alias examples_3_3_3_isUniversalKExtension_ratSet := KappaMonoid.isUniversalKExtension_ratSet

/-- **Examples 3.3(3)** — `KappaMonoid.kclosure_ofReal_ratSet`, in `Examples/Reals.lean`. -/
alias examples_3_3_3_kclosure_ofReal_ratSet := KappaMonoid.kclosure_ofReal_ratSet

/-- **Examples 3.3(3)**: `ℚ≥0 ∪ ℝ̃>0 ∪ {∞}` is `ℵ₀⁻`-braided over `ℚ≥0` —
`KappaMonoid.isBraidedOver_ratReachable`, in `Examples/RealsExtra.lean`. -/
alias examples_3_3_3_isBraidedOver_ratReachable := KappaMonoid.isBraidedOver_ratReachable

/-- **Examples 3.3(2)** — `KappaMonoid.not_isBraided_geom_two_geom`, in `Examples/NNReal.lean`. -/
alias examples_3_3_2_not_isBraided_geom_two_geom := KappaMonoid.not_isBraided_geom_two_geom

/-- **Examples 3.3(2)** — `KappaMonoid.not_isBraided_single2_geom`, in `Examples/NNReal.lean`. -/
alias examples_3_3_2_not_isBraided_single2_geom := KappaMonoid.not_isBraided_single2_geom

/-- **Examples 3.3(2)** — `KappaMonoid.not_isBraidedOver_ennreal`: `ℝ≥0∞` is not `ℵ₀⁻`-braided
over `ℝ≥0`. -/
alias examples_3_3_2_not_isBraidedOver_ennreal := KappaMonoid.not_isBraidedOver_ennreal

/-- **Examples 3.3(2)** — `KappaMonoid.not_isBraidedOver_trivExt_nnreal`: neither is the trivial
`ℵ₀`-extension of `ℝ≥0`. -/
alias examples_3_3_2_not_isBraidedOver_trivExt_nnreal :=
  KappaMonoid.not_isBraidedOver_trivExt_nnreal

/-- **Examples 3.3(3)** — `KappaMonoid.ofReal_notMem_kclosure_of_not_mem_ratSet`, in `Examples/Reals.lean`. -/
alias examples_3_3_3_ofReal_notMem_kclosure_of_not_mem_ratSet := KappaMonoid.ofReal_notMem_kclosure_of_not_mem_ratSet

/-- **Lemma 3.4(4)** — `KappaMonoid.isBraided_iff_of_ne_aleph0`, in `Braiding/Sums.lean`. -/
alias lemma_3_4_4_isBraided_iff_of_ne_aleph0 := KappaMonoid.isBraided_iff_of_ne_aleph0

/-- **Lemma 3.4(1)** — `KappaMonoid.isBraided_of_small_support`, in `Braiding/Sums.lean`. -/
alias lemma_3_4_1_isBraided_of_small_support := KappaMonoid.isBraided_of_small_support

/-- **Lemma 3.4(2)** — `KappaMonoid.BraidingData.isBraided_block`, in `Braiding/WellOrder.lean`:
the restriction of a braiding to one `ω`-block of the well-order, padded by zeroes, is again a
braiding. -/
alias lemma_3_4_2_isBraided_block := KappaMonoid.BraidingData.isBraided_block

/-- **Lemma 3.4(3)** — `KappaMonoid.isBraided_of_blocks`, in `Braiding/WellOrder.lean`: the
converse, a family of block braidings indexed by a pair of indexed partitions assembles into one
braiding.  The paper's "there exists a limit well-order on `κ`" is discharged by Lemma 3.5. -/
alias lemma_3_4_3_isBraided_of_blocks := KappaMonoid.isBraided_of_blocks

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

/-- **Lemma 3.7** — `KappaMonoid.IsBraided.exists_aligned_cumulative`, in
`Braiding/TransUncountable.lean`: the statement as printed, `⋃_{ν ≤ μ} J_ν ⊆ ⋃_{ν ≤ μ} J'_ν ⊆
⋃_{ν ≤ μ+1} J_ν`, for the normal-form limit well-order `kOrd` on `ι × ℕ` (order type `ω · #ι`), not
for an arbitrary limit well-order on `κ`. -/
alias lemma_3_7_exists_aligned_cumulative := KappaMonoid.IsBraided.exists_aligned_cumulative

/-- **Lemma 3.7**, block-by-block form — `KappaMonoid.IsBraided.exists_aligned_of_data`, in
`Braiding/TransUncountable.lean`. -/
alias lemma_3_7_exists_aligned_of_data := KappaMonoid.IsBraided.exists_aligned_of_data

/-- **Lemma 3.7 (`λ = ℵ₀`)** — `KappaMonoid.IsBraided.exists_aligned`, in `Braiding/TransAleph0.lean`:
the transfinite recursion of the paper's proof, which is what the countable case needs. -/
alias lemma_3_7_exists_aligned := KappaMonoid.IsBraided.exists_aligned

/-- **Lemma 3.7 (`λ > ℵ₀`)** — `KappaMonoid.IsBraided.exists_aligned_eq_of_ne_aleph0`: for
uncountable `λ` the two partitions of the middle family can even be taken equal. -/
alias lemma_3_7_exists_aligned_eq_of_ne_aleph0 :=
  KappaMonoid.IsBraided.exists_aligned_eq_of_ne_aleph0

/-- **Lemma 3.8 (`λ = ℵ₀`)**, the combinatorial core of the proof — `KappaMonoid.IsBraided.of_aligned`,
in `Braiding/TransAleph0.lean`.  Stated only for `λ = ℵ₀`; transitivity for every `λ` is
`IsBraided.trans` below. -/
alias lemma_3_8_core_of_aligned := KappaMonoid.IsBraided.of_aligned

/-- **Lemma 3.8, transitivity** — `KappaMonoid.IsBraided.trans`, in `Braiding/TransUncountable.lean`. -/
alias lemma_3_8_transitivity_trans := KappaMonoid.IsBraided.trans

/-- **Remark 3.9** — `KappaMonoid.exists_common_coarsening`, in `Braiding/TransUncountable.lean`:
for regular uncountable `λ`, two partitions into pieces of size `< λ` have a common coarsening that
is again one, which is why transitivity is easy above `ℵ₀`. -/
alias remark_3_9_exists_common_coarsening := KappaMonoid.exists_common_coarsening

/-- **Remark 3.9**, the graph — `KappaMonoid.ccomp`: the connected components of the relation
"lie in a common piece of either partition". -/
alias remark_3_9_ccomp := KappaMonoid.ccomp

/-- **Remark 3.9**, the cardinality bound — `KappaMonoid.mk_ccomp_lt`: regularity of the
uncountable `λ` keeps the components of size `< λ`. -/
alias remark_3_9_mk_ccomp_lt := KappaMonoid.mk_ccomp_lt

/-- **Remark 3.9**, the conclusion — `KappaMonoid.IsBraided.trans_of_ne_aleph0`. -/
alias remark_3_9_trans_of_ne_aleph0 := KappaMonoid.IsBraided.trans_of_ne_aleph0

/-- **Remark 3.9**: the sets of the common coarsening *are* the connected components —
`KappaMonoid.remark_3_9`, in `Braiding/Components.lean`, for regular uncountable `λ` as in the paper.
The partition is indexed by `ι × ℕ`, so its sets are the nonempty pieces. -/
alias remark_3_9_remark_3_9 := KappaMonoid.remark_3_9

/-- **Remark 3.9**: `ccomp` is the connected component of the paper's graph —
`KappaMonoid.mem_ccomp_iff_reflTransGen`. -/
alias remark_3_9_mem_ccomp_iff_reflTransGen := KappaMonoid.mem_ccomp_iff_reflTransGen

/-- **Remark 3.9**: the components form the finest common coarsening —
`KappaMonoid.ccomp_subset_of_coarsening`. -/
alias remark_3_9_ccomp_subset_of_coarsening := KappaMonoid.ccomp_subset_of_coarsening

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

/-- **Examples 3.13**, third entry: `ℚ̂≥0 ≅ ℚ≥0 ∪ ℝ̃>0 ∪ {∞}` —
`KappaMonoid.isUniversalKExtension_ratSet`, in `Examples/Reals.lean`.  Its extension is the
`ℵ₀`-closure of `ℚ≥0` in `ℝ≥0 ∪ ℝ̃>0 ∪ {∞}`; that this closure is `ℚ≥0 ∪ ℝ̃>0 ∪ {∞}` is
`kclosure_ofReal_ratSet`, next.  The same declarations are Examples 3.3(3). -/
alias examples_3_13_isUniversalKExtension_ratSet := KappaMonoid.isUniversalKExtension_ratSet

/-- **Examples 3.13**, third entry, the carrier — `KappaMonoid.kclosure_ofReal_ratSet`, in
`Examples/Reals.lean`: the `ℵ₀`-closure of `ℚ≥0` is `ℚ≥0 ∪ ℝ̃>0 ∪ {∞}`. -/
alias examples_3_13_kclosure_ofReal_ratSet := KappaMonoid.kclosure_ofReal_ratSet

/-- **Lemma 3.14(1)**
 — `KappaMonoid.lemma_3_14_free`, in `Braiding/Saturated.lean`. -/
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

/-- **Before Proposition 3.15** (tex 1444): inequalities become equations with slack variables —
`KappaMonoid.LinSystem.withSlackEquiv`, in `Examples/DiophantineExtra.lean`, an isomorphism of the
solution monoids in `ℕ₀^n` and `ℕ₀^{n+k}`; `LinSystem.exists_withSlack_iso` for finitely many
inequalities. -/
alias before_prop_3_15_withSlackEquiv := KappaMonoid.LinSystem.withSlackEquiv

/-- **Before Proposition 3.15**: an equation is two inequalities —
`KappaMonoid.LinSystem.solutions_eqsAsIneqs`, at every `κ`. -/
alias before_prop_3_15_solutions_eqsAsIneqs := KappaMonoid.LinSystem.solutions_eqsAsIneqs

/-- **Before Proposition 3.15** (tex 1448): a `κ`-submonoid of `F_κ^n` cut out by equations need not
be saturated — `KappaMonoid.not_isSaturated_diagSystem`. -/
alias before_prop_3_15_not_isSaturated_diagSystem := KappaMonoid.not_isSaturated_diagSystem

/-- **Example 3.16** — `KappaMonoid.example_3_16`, in `Examples/Diophantine.lean`.  It is stated for the
set `H + ℵ₀H` (`alephExt`); that this set is the universal `ℵ₀`-extension `Ĥ` is
`prop_3_15_two_of_ineqs_empty` applied to `diagSystem`. -/
alias example_3_16_example_3_16 := KappaMonoid.example_3_16

/-- **Example 3.16**: `Ĥ = {(n,n)} ∪ {(ℵ₀,ℵ₀)} ≅ F_ℵ₀` — `KappaMonoid.example_3_16_iso`, with the carrier
`KappaMonoid.mem_alephExt_diagSystem_iff`, in `Examples/DiophantineExtra.lean`. -/
alias example_3_16_iso := KappaMonoid.example_3_16_iso

/-- **Example 3.16**: the solutions of `2x = x + y` in `F_ℵ₀²` are
`{(n,n)} ∪ {(ℵ₀,n)} ∪ {(ℵ₀,ℵ₀)}` — `KappaMonoid.mem_doubleSystem_solutions_iff`. -/
alias example_3_16_mem_doubleSystem_solutions_iff := KappaMonoid.mem_doubleSystem_solutions_iff

/-- **Example 3.17**, `H` is not saturated — `KappaMonoid.not_isSaturatedFin_ineqSystem`, in
`Examples/Diophantine.lean`. -/
alias example_3_17_not_saturated := KappaMonoid.not_isSaturatedFin_ineqSystem

/-- **Example 3.17**, `H + ℵ₀H` is not braided over `H` —
`KappaMonoid.not_isBraidedOver_ineqSystem`, in `Examples/Diophantine.lean`.  The witnesses are the
constant families `(1,1)` and `(1,2)`, not the paper's pair `(0,1),(1,1),…` and `(1,1),…`. -/
alias example_3_17_not_braided := KappaMonoid.not_isBraidedOver_ineqSystem

/-- **Example 3.17**: for `H = {(a,b) ∈ ℕ₀² : a ≤ b}` the monoid `H + ℵ₀H` is *not* the universal
`ℵ₀`-extension of `H` — `KappaMonoid.not_prop_3_15_two_ineqSystem`, in
`Examples/Diophantine.lean`.  This is why Proposition 3.15(2) excludes inequalities. -/
alias example_3_17_not_universal := KappaMonoid.not_prop_3_15_two_ineqSystem

/-- **Example 3.17**, the repair — `KappaMonoid.example_3_17_slack_iso`, in
`Examples/Diophantine.lean`: `H ≅ H' = {(a,b,c) ∈ ℕ₀³ : b = a + c}`, a system of equations, to
which Proposition 3.15(2) does apply. -/
alias example_3_17_slack_iso := KappaMonoid.example_3_17_slack_iso

/-- **Example 3.17**, the paper's own pair `(0,1),(1,1),…` and `(1,1),…`: equal sums `(ℵ₀,ℵ₀)`, not
braided — `KappaMonoid.example_3_17_families`, in `Examples/DiophantineExtra.lean`.  The
exceptional index is an arbitrary `idx0 : Idx ℵ₀` rather than `0 ∈ ℕ`. -/
alias example_3_17_families := KappaMonoid.example_3_17_families

/-- **Example 3.17**: `Ĥ = H' + ℵ₀H'`, pulled back along `H ≅ H'`, is the universal `ℵ₀`-extension
of `H` — `KappaMonoid.isUniversalKExtension_slackSystem_alephExt` (and the braiding
`isBraidedOver_slackSystem_alephExt`). -/
alias example_3_17_isUniversalKExtension_slack :=
  KappaMonoid.isUniversalKExtension_slackSystem_alephExt

/-- **Example 3.17**, the listings: `ℵ₀H` — `KappaMonoid.example_3_17_alephPart_ineq`. -/
alias example_3_17_alephPart_ineq := KappaMonoid.example_3_17_alephPart_ineq

/-- **Example 3.17**, the listings: `H + ℵ₀H` — `KappaMonoid.example_3_17_alephExt_ineq`. -/
alias example_3_17_alephExt_ineq := KappaMonoid.example_3_17_alephExt_ineq

/-- **Example 3.17**, the listings: `ℵ₀H'` — `KappaMonoid.example_3_17_alephPart_slack`. -/
alias example_3_17_alephPart_slack := KappaMonoid.example_3_17_alephPart_slack

/-- **Example 3.17**, the listings: `Ĥ' = H' + ℵ₀H'` — `KappaMonoid.example_3_17_alephExt_slack`. -/
alias example_3_17_alephExt_slack := KappaMonoid.example_3_17_alephExt_slack

/-- **Example 3.17**, closing sentence: the slack forms of the paper's pair sum to `(ℵ₀,ℵ₀,1)` and
`(ℵ₀,ℵ₀,0)`, so `Ĥ` tells them apart — `KappaMonoid.example_3_17_slack_sums`. -/
alias example_3_17_slack_sums := KappaMonoid.example_3_17_slack_sums



/-! ## Not formalised, deliberately

* **Remark 3.18**.  Saturated submonoids of `ℕ₀^n` are finitely generated reduced Krull monoids;
  conversely every finitely generated reduced Krull monoid is a Diophantine monoid
  (Chapman–Krause–Oeljeklaus, Theorem 3.1); so Proposition 3.15 determines the universal
  `κ`-extensions of finitely generated reduced Krull monoids; and a note on terminology.  Background
  and a citation, with an informal consequence; nothing later in the paper depends on it. -/

end Paper

end KappaMonoid
