/-
**The axiom provenance of the headline results, as checked claims.**

CI refuses a change to the *set* of `axiom` declarations under `KappaMonoid/`, but says nothing
about who depends on them: a proof that quietly started using Bergman–Dicks would pass.  The
provenance paragraphs of `README.md` say it in prose, and prose drifts.  Every line below is
checked by the build.

`propext`, `Classical.choice` and `Quot.sound` are permitted everywhere and never listed, so an
empty list means *"this result rests on nothing but Lean's own foundation"*.

The lists were computed with `#print axioms`, not guessed.  Two of them are worth reading twice:

* `corollary_4_5_three` is axiom-free — it takes "every projective is a sum of finitely generated
  ones" as a hypothesis, rather than quoting Albrecht's theorem for it.
* `kaplansky` is axiom-free too, since Kaplansky's theorem is proved in
  `ForMathlib/Kaplansky.lean`.
-/
import KappaMonoid.Meta.AxiomAudit
import KappaMonoid.Paper.Section2
import KappaMonoid.Paper.Section3
import KappaMonoid.Paper.Section4
import KappaMonoid.Paper.Section5
import KappaMonoid.Paper.Section5Extra

namespace KappaMonoid

/-! ## §2 — Proposition 2.16 reaches Bergman–Dicks through Leavitt's theorem -/

#assert_axioms prop_2_16 [bergmanDicksData]
#assert_axioms prop_2_17_one []
#assert_axioms Projective.isFaithful_unitClass []
#assert_axioms Projective.isOrderUnit_unitClass []
#assert_axioms Projective.isFaithful_of_isProgenerator []
#assert_axioms Projective.exists_add_eq_nsmul_of_isProgenerator []
#assert_axioms Projective.part_unitClass_eq_of_aleph0_le []
#assert_axioms Projective.part_unitClass_eq_of_lt_aleph0 []
#assert_axioms LMonoid.kMonoidOfLT_ofCompatible []
#assert_axioms LMonoid.ofCompatible_kMonoidOfLT []
#assert_axioms KMonoid.lemma_2_15 []
#assert_axioms KMonoid.lemma_2_15_add []
#assert_axioms KMonoid.lemma_2_15_kIso []
#assert_axioms KMonoid.equivFinitePartSumCard_splitSum []
#assert_axioms KMonoid.isOrderUnit_of_kGenerates []
#assert_axioms KMonoid.addOfCard_eq_add_closure []
#assert_axioms LMonoid.toPaper_toLMonoid []
#assert_axioms PaperLMonoid.toLMonoid_toPaper_sigma []
#assert_axioms PaperLMonoid.toLMonoid_lsumOf []
#assert_axioms KMonoid.toPaper_toKMonoid []
#assert_axioms PaperKMonoid.sigma_pair_comm []
#assert_axioms subsingleton_of_realises_cyclicRel_zero []
#assert_axioms cyclicRel_realisable_iff [bergmanDicksData]
#assert_axioms rankRel_classification []
#assert_axioms FreeMod.kGenerates_unit []
#assert_axioms prop_2_16_converse []
#assert_axioms prop_2_16_iff [bergmanDicksData]
#assert_axioms prop_2_17_two []
#assert_axioms exists_unique_lift []
#assert_axioms FreeK_eq_univ []

/-! ## §3 — no axiom at all -/

#assert_axioms exists_common_coarsening []
#assert_axioms mk_ccomp_lt []
#assert_axioms IsBraided.trans_of_ne_aleph0 []
#assert_axioms isBraided_nat_iff []
#assert_axioms not_isBraidedOver_ennreal []
#assert_axioms not_isBraidedOver_trivExt_nnreal []
#assert_axioms IsBraided.exists_aligned []
#assert_axioms IsBraided.exists_aligned_eq_of_ne_aleph0 []
#assert_axioms IsBraided.exists_aligned_of_data []
#assert_axioms IsBraided.exists_aligned_cumulative []
#assert_axioms BraidingData.isBraided_block []
#assert_axioms isBraided_of_blocks []
#assert_axioms isBraidedOn_iff_isBraided []
#assert_axioms isBraidedOn_congr_self []
#assert_axioms IsBraided.trans []
#assert_axioms extend_lhom []
#assert_axioms RTilde.isBraidedOver_rtilde []
#assert_axioms isBraided_nnreal_iff []
#assert_axioms RTilde.isUniversalKExtension_rtilde []
#assert_axioms isUniversalKExtension_withTop_nat []
#assert_axioms isUniversalKExtension_ratSet []
#assert_axioms isConical_of_injective_lhom []
#assert_axioms theorem_3_12 []
#assert_axioms theorem_3_12_of_aleph0_lt []
#assert_axioms isBraidedOver_of_isUniversalKExtension []
#assert_axioms sumOf_eq_of_isBraided []
#assert_axioms lemma_3_14_free []
#assert_axioms lemma_3_14_sub []
#assert_axioms prop_3_15_one []
#assert_axioms prop_3_15_two []
#assert_axioms prop_3_15_two_of_ineqs_empty []
#assert_axioms not_isBraidedOver_ineqSystem []
#assert_axioms not_prop_3_15_two_ineqSystem []
#assert_axioms example_3_16 []
#assert_axioms isBraidedOver_ratReachable []
#assert_axioms remark_3_9 []
#assert_axioms mem_ccomp_iff_reflTransGen []
#assert_axioms ccomp_subset_of_coarsening []
#assert_axioms LinSystem.withSlackEquiv []
#assert_axioms LinSystem.exists_withSlack_iso []
#assert_axioms LinSystem.solutions_eqsAsIneqs []
#assert_axioms not_isSaturated_diagSystem []
#assert_axioms example_3_16_iso []
#assert_axioms mem_doubleSystem_solutions_iff []
#assert_axioms example_3_17_families []
#assert_axioms isBraidedOver_slackSystem_alephExt []
#assert_axioms isUniversalKExtension_slackSystem_alephExt []
#assert_axioms example_3_17_alephExt_ineq []
#assert_axioms example_3_17_alephExt_slack []
#assert_axioms example_3_17_slack_sums []
#assert_axioms Dedekind.isBraided_iff []
#assert_axioms Dedekind.isUniversalKExtension_dedExt []
#assert_axioms not_isSaturatedFin_ineqSystem []
#assert_axioms example_3_17_slack_iso []

/-! ## §4 — Bergman–Dicks in one direction of Corollary 4.7(1), nothing else -/

#assert_axioms IsLambdaSmallLe.isLambdaSmall_succ []
#assert_axioms theorem_4_3 []
#assert_axioms corollary_4_4 []
#assert_axioms corollary_4_4_one []
#assert_axioms corollary_4_4_two []
#assert_axioms corollary_4_5 []
#assert_axioms corollary_4_5_two []
#assert_axioms corollary_4_5_three []
#assert_axioms kaplansky []
#assert_axioms isLambdaSmall_succ_iff []
#assert_axioms isLambdaSmall_succ_aleph0_of_countable []
#assert_axioms isLambdaSmallLe_aleph0_of_countable []
#assert_axioms IsUniversalKExtension.exists_kIso_of_base_iso []
#assert_axioms exists_kIso_of_aleph1Iso []
#assert_axioms exists_kIso_of_fgIso []
#assert_axioms exists_kIso_of_fgIso_univ []
#assert_axioms corollary_4_6_hereditary []
#assert_axioms examples_4_8_3_nat []
#assert_axioms examples_4_8_3_nnreal []
#assert_axioms examples_4_8_3_rat []
#assert_axioms examples_4_8_3_diophantine []
#assert_axioms addOf_unitClass_eq []
#assert_axioms addOfCard_unitClass_eq []
#assert_axioms corollary_4_7_one_backward []
#assert_axioms corollary_4_7_one_backward_iso []
#assert_axioms corollary_4_7_one_forward [bergmanDicksData]
#assert_axioms corollary_4_7_one [bergmanDicksData]
#assert_axioms corollary_4_7_two []
#assert_axioms corollary_4_7_two_iff []
#assert_axioms krsa_ascent []
#assert_axioms krsa_ascent_lambdaGen []
#assert_axioms krsa_ascent_free []
#assert_axioms krsa_ascent_iso []
#assert_axioms isUniversalKExtension_unique' []

/-! ## §5 — Bergman–Dicks only, and only where Corollary 4.7(1) is invoked -/

#assert_axioms TwoGen.lemma_5_1 []
#assert_axioms TwoGen.lemma_5_1_core []
#assert_axioms TwoGen.lemma_5_1_fg []
#assert_axioms TwoGen.lemma_5_1_addOf_eq_closure []
#assert_axioms TwoGen.lemma_5_1_iso []
#assert_axioms TwoGen.lemma_5_2_one []
#assert_axioms TwoGen.lemma_5_2_two []
#assert_axioms TwoGen.lemma_5_2_three []
#assert_axioms TwoGen.lemma_5_2_four []
#assert_axioms TwoGen.lemma_5_2_five []
#assert_axioms TwoGen.theorem_5_3_forward []
#assert_axioms TwoGen.theorem_5_3_backward [bergmanDicksData]
#assert_axioms TwoGen.theorem_5_3 [bergmanDicksData]
#assert_axioms TwoGen.theorem_5_3_sumFG [bergmanDicksData]
#assert_axioms TwoGen.prop_5_4 []
#assert_axioms TwoGen.prop_5_4_free []
#assert_axioms TwoGen.prop_5_4_hereditary []
#assert_axioms TwoGen.corollary_5_5_one [bergmanDicksData]
#assert_axioms TwoGen.corollary_5_5_two [bergmanDicksData]
#assert_axioms TwoGen.corollary_5_5_three [bergmanDicksData]
#assert_axioms TwoGen.corollary_5_5_three_nonfree [bergmanDicksData]
#assert_axioms TwoGen.corollary_5_5_three_trace [bergmanDicksData]
#assert_axioms TwoGen.cmul_top_add_ecmul_of_mem_addOf []
#assert_axioms TwoGen.unique_infinite_form_of_addOf_eq []
#assert_axioms TwoGen.cex_incomparable []
#assert_axioms TwoGen.cex_absorb []
#assert_axioms TwoGen.cex_kGenerates []
#assert_axioms TwoGen.cex_not_cyclic []
#assert_axioms TwoGen.isFaithful_iff_of_kGenerates []
#assert_axioms TwoGen.isBraidedOver_addOf_of_ne []
#assert_axioms TwoGen.ne_nsmul_iff_exists_withTop []
#assert_axioms TwoGen.ne_nsmul_of_realization []
#assert_axioms TwoGen.remark_before_5_5 [bergmanDicksData]
#assert_axioms TwoGen.remark_before_5_5_realizable [bergmanDicksData]
#assert_axioms TwoGen.realization_of_ne [bergmanDicksData]
#assert_axioms TwoGen.cyclic_realizable_iff [bergmanDicksData]
#assert_axioms TwoGen.cyclic_realizable_iff_withTop [bergmanDicksData]
#assert_axioms Paper.lemma_5_2_three' []
#assert_axioms Paper.lemma_5_2_four' []
#assert_axioms Paper.corollary_5_5_two_converse_false_setting []
#assert_axioms Paper.corollary_5_5_three_converse_false_setting []

/-! ## The paper layer restates §5, so it must report the same axioms -/

#assert_axioms Paper.lemma_5_2_three []
#assert_axioms Paper.theorem_5_3_backward [bergmanDicksData]
#assert_axioms Paper.exists_form []
#assert_axioms Paper.lemma_5_1 []
#assert_axioms Paper.theorem_5_3_forward []
#assert_axioms Paper.theorem_5_3_realizable [bergmanDicksData]
#assert_axioms Paper.prop_5_4 []
#assert_axioms Paper.corollary_5_5_one [bergmanDicksData]
#assert_axioms Paper.corollary_5_5_two [bergmanDicksData]
#assert_axioms Paper.corollary_5_5_three [bergmanDicksData]
#assert_axioms Paper.corollary_5_5_three_trace [bergmanDicksData]

end KappaMonoid
