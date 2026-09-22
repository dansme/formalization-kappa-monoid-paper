/-
**Section 2 of the paper**: an index of its numbered results.

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

/-- **Examples 2.3(2)** — `KappaMonoid.ENNRealExample.instKMonoid`, in `Examples/ENNReal.lean`. -/
alias examples_2_3_2_instKMonoid := KappaMonoid.ENNRealExample.instKMonoid

/-- **Examples 2.3(3)** — `KappaMonoid.Fcard.instKMonoid`, in `Core/Cardinal.lean`. -/
alias examples_2_3_3_instKMonoid := KappaMonoid.Fcard.instKMonoid

/-- **Examples 2.3(1)** — `KappaMonoid.TrivExt.instKMonoid`, in `Examples/TrivExt.lean`. -/
alias examples_2_3_1_instKMonoid := KappaMonoid.TrivExt.instKMonoid

/-- **Definition 2.4(1)** — `KappaMonoid.FreeMod.freeClass`, in `Modules/Rings/FreeModules.lean`. -/
alias definition_2_4_1_freeClass := KappaMonoid.FreeMod.freeClass

/-- **Definition 2.4(2)** — `KappaMonoid.projClass`, in `Modules/Projective.lean`. -/
alias definition_2_4_2_projClass := KappaMonoid.projClass

/-- **Lemma 2.5** — `KappaMonoid.KMonoid.ofBare`, in `Core/Bare.lean`. -/
alias lemma_2_5_ofBare := KappaMonoid.KMonoid.ofBare

/-- **Lemma 2.5** — `KappaMonoid.SumData.addCommMonoid`, in `Core/SumData.lean`. -/
alias lemma_2_5_addCommMonoid := KappaMonoid.SumData.addCommMonoid

/-- **Definition 2.6** — `KappaMonoid.LMonoid.lcmul`, in `Core/LMonoid.lean`. -/
alias definition_2_6_lcmul := KappaMonoid.LMonoid.lcmul

/-- **Lemma 2.7(2) for a two-term sum of cardinals** — `KappaMonoid.KMonoid.cmul_add`, in `Core/KMonoid.lean`. -/
alias lemma_2_7_2_for_a_two_term_sum_of_cardinals_cmul_add := KappaMonoid.KMonoid.cmul_add

/-- **Lemma 2.7(4)** — `KappaMonoid.KMonoid.cmul_cmul`, in `Core/KMonoid.lean`. -/
alias lemma_2_7_companion_cmul_cmul := KappaMonoid.KMonoid.cmul_cmul

/-- **Lemma 2.7(1), second half** — `KappaMonoid.KMonoid.cmul_one`, in `Core/KMonoid.lean`. -/
alias lemma_2_7_1_second_half_cmul_one := KappaMonoid.KMonoid.cmul_one

/-- **Lemma 2.7(3)** — `KappaMonoid.KMonoid.cmul_sumOf`, in `Core/KMonoid.lean`. -/
alias lemma_2_7_3_cmul_sumOf := KappaMonoid.KMonoid.cmul_sumOf

/-- **Lemma 2.7(2)** — `KappaMonoid.KMonoid.cmul_sumOf_cardinal`, in `Core/KMonoid.lean`. -/
alias lemma_2_7_2_cmul_sumOf_cardinal := KappaMonoid.KMonoid.cmul_sumOf_cardinal

/-- **Lemma 2.7(2)** — `KappaMonoid.LMonoid.lcmul_add`, in `Core/LMonoid.lean`. -/
alias lemma_2_7_2_lcmul_add := KappaMonoid.LMonoid.lcmul_add

/-- **Lemma 2.7(3)** — `KappaMonoid.LMonoid.lcmul_lsumOf`, in `Core/LMonoid.lean`. -/
alias lemma_2_7_3_lcmul_lsumOf := KappaMonoid.LMonoid.lcmul_lsumOf

/-- **Lemma 2.7(2)** — `KappaMonoid.LMonoid.lcmul_lsumOf_cardinal`, in `Core/LMonoid.lean`. -/
alias lemma_2_7_2_lcmul_lsumOf_cardinal := KappaMonoid.LMonoid.lcmul_lsumOf_cardinal

/-- **Lemma 2.7(1)** — `KappaMonoid.LMonoid.lcmul_one`, in `Core/LMonoid.lean`. -/
alias lemma_2_7_1_lcmul_one := KappaMonoid.LMonoid.lcmul_one

/-- **Lemma 2.7(1)** — `KappaMonoid.LMonoid.lcmul_zero_cardinal`, in `Core/LMonoid.lean`. -/
alias lemma_2_7_1_lcmul_zero_cardinal := KappaMonoid.LMonoid.lcmul_zero_cardinal

/-- **Lemma 2.8(2)** — `KappaMonoid.KMonoid.add_cmul_top_eq`, in `Core/KMonoid.lean`. -/
alias lemma_2_8_2_add_cmul_top_eq := KappaMonoid.KMonoid.add_cmul_top_eq

/-- **Lemma 2.8(2), the key idempotence step of the swindle** — `KappaMonoid.KMonoid.add_cmul_top_self`, in `Core/KMonoid.lean`. -/
alias lemma_2_8_2_the_key_idempotence_step_of_the_swindle_add_cmul_top_self := KappaMonoid.KMonoid.add_cmul_top_self

/-- **Lemma 2.8(1)** — `KappaMonoid.KMonoid.isConical`, in `Core/KMonoid.lean`. -/
alias lemma_2_8_1_isConical := KappaMonoid.KMonoid.isConical

/-- **Lemma 2.8(2)** — `KappaMonoid.LMonoid.add_lcmul_eq`, in `Core/LMonoid.lean`. -/
alias lemma_2_8_2_add_lcmul_eq := KappaMonoid.LMonoid.add_lcmul_eq

/-- **Proposition 2.9(2)** — `KappaMonoid.exists_unique_lift`, in `Core/Free.lean`. -/
alias proposition_2_9_2_exists_unique_lift := KappaMonoid.exists_unique_lift

/-- **Proposition 2.9(2)** — `KappaMonoid.hom_ext`, in `Core/Free.lean`. -/
alias proposition_2_9_2_hom_ext := KappaMonoid.hom_ext

/-- **Proposition 2.9(2)** — `KappaMonoid.isLMonoidHom_lift`, in `Core/Free.lean`. -/
alias proposition_2_9_2_isLMonoidHom_lift := KappaMonoid.isLMonoidHom_lift

/-- **Proposition 2.9(1)** — `KappaMonoid.isLSubmonoid_FreeL`, in `Core/Free.lean`. -/
alias proposition_2_9_1_isLSubmonoid_FreeL := KappaMonoid.isLSubmonoid_FreeL

/-- **Proposition 2.9(2)** — `KappaMonoid.lift_iota`, in `Core/Free.lean`. -/
alias proposition_2_9_2_lift_iota := KappaMonoid.lift_iota

/-- **Definition 2.10(1)** — `KappaMonoid.KMonoid.IsAlphaGenerated`, in `Core/KMonoid.lean`. -/
alias definition_2_10_1_IsAlphaGenerated := KappaMonoid.KMonoid.IsAlphaGenerated

/-- **Definition 2.10(2)** — `KappaMonoid.KMonoid.IsCyclicKMonoid`, in `Core/KMonoid.lean`. -/
alias definition_2_10_2_IsCyclicKMonoid := KappaMonoid.KMonoid.IsCyclicKMonoid

/-- **Definition 2.10(1)** — `KappaMonoid.isAlphaGenerated_iff`, in `Core/Free.lean`. -/
alias definition_2_10_1_isAlphaGenerated_iff := KappaMonoid.isAlphaGenerated_iff

/-- **Definition 2.11** — `KappaMonoid.AddLe`, in `Core/OrderUnit.lean`. -/
alias definition_2_11_AddLe := KappaMonoid.AddLe

/-- **Definition 2.12(2)** — `KappaMonoid.KMonoid.IsFaithful`, in `Core/OrderUnit.lean`. -/
alias definition_2_12_2_IsFaithful := KappaMonoid.KMonoid.IsFaithful

/-- **Definition 2.12(1)** — `KappaMonoid.KMonoid.IsOrderUnit`, in `Core/OrderUnit.lean`. -/
alias definition_2_12_1_IsOrderUnit := KappaMonoid.KMonoid.IsOrderUnit

/-- **Example 2.13** — `KappaMonoid.Projective.isFaithful_unitClass`, in `Modules/Rings/ProjOrderUnit.lean`. -/
alias example_2_13_isFaithful_unitClass := KappaMonoid.Projective.isFaithful_unitClass

/-- **Example 2.13** — `KappaMonoid.Projective.isOrderUnit_unitClass`, in `Modules/Rings/ProjOrderUnit.lean`. -/
alias example_2_13_isOrderUnit_unitClass := KappaMonoid.Projective.isOrderUnit_unitClass

/-- **Lemma 2.14** — `KappaMonoid.KMonoid.eq_cmul_top_of_add`, in `Core/OrderUnit.lean`. -/
alias lemma_2_14_eq_cmul_top_of_add := KappaMonoid.KMonoid.eq_cmul_top_of_add

/-- **Lemma 2.15** — `KappaMonoid.KMonoid.lemma_2_15`, in `Core/Cyclic.lean`: the disjointness
and the parametrisation. -/
alias lemma_2_15_lemma_2_15 := KappaMonoid.KMonoid.lemma_2_15

/-- **Lemma 2.15**, the bijection — `KappaMonoid.KMonoid.equivFinitePartSumCard`. -/
alias lemma_2_15_equivFinitePartSumCard := KappaMonoid.KMonoid.equivFinitePartSumCard

/-- **Lemma 2.15**, *"with the obvious operation"* — `KappaMonoid.KMonoid.lemma_2_15_add`, the
three rules that determine the operation on `C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}`. -/
alias lemma_2_15_lemma_2_15_add := KappaMonoid.KMonoid.lemma_2_15_add

/-- **Proposition 2.16** — `KappaMonoid.prop_2_16`, in `Modules/Rings/Realisation.lean`. -/
alias proposition_2_16_prop_2_16 := KappaMonoid.prop_2_16

/-- **Proposition 2.17(1)** — `KappaMonoid.prop_2_17_one`, in `Modules/Rings/Semisimple.lean`. -/
alias proposition_2_17_1_prop_2_17_one := KappaMonoid.prop_2_17_one

/-- **Proposition 2.17(2)** — `KappaMonoid.simpleListPi`, in `Modules/Rings/Semisimple.lean`. -/
alias proposition_2_17_2_simpleListPi := KappaMonoid.simpleListPi

/-- **Proposition 2.17(2)** — `KappaMonoid.prop_2_17_two`, in `Modules/Rings/Semisimple.lean`:
for every `n` there is a semisimple ring `R` with `V^κ(R) ≅ F_κ^n`. -/
alias proposition_2_17_2_prop_2_17_two := KappaMonoid.prop_2_17_two

/-- **Remark 2.19** — `KappaMonoid.LMonoid.ofLE`, in `Core/LMonoid.lean`. -/
alias remark_2_19_ofLE := KappaMonoid.LMonoid.ofLE


/-! ## Not formalised

Nothing: every numbered result of §2 is above.  Definition 2.18 (`λ⁻`-monoids) and Remark 2.19
(`κ`-monoids are the `λ⁻`-monoids for `λ = κ⁺`) are the classes `LMonoid`/`KMonoid` and
`LMonoid.ofLE` themselves, so they appear as definitions rather than as results. -/

end Paper

end KappaMonoid
