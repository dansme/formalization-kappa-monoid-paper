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

namespace KappaMonoid

/-! ## §2 — Proposition 2.16 reaches Bergman–Dicks through Leavitt's theorem -/

#assert_axioms prop_2_16 [bergmanDicksData]
#assert_axioms prop_2_17_one []
#assert_axioms Projective.isFaithful_unitClass []
#assert_axioms Projective.isOrderUnit_unitClass []
#assert_axioms KMonoid.lemma_2_15 []
#assert_axioms exists_unique_lift []

/-! ## §3 — no axiom at all -/

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
#assert_axioms not_isSaturatedFin_ineqSystem []
#assert_axioms example_3_17_slack_iso []

/-! ## §4 — Bergman–Dicks in one direction of Corollary 4.7(1), nothing else -/

#assert_axioms theorem_4_3 []
#assert_axioms corollary_4_4 []
#assert_axioms corollary_4_5_three []
#assert_axioms kaplansky []
#assert_axioms addOf_unitClass_eq []
#assert_axioms corollary_4_7_one_backward []
#assert_axioms corollary_4_7_one_forward [bergmanDicksData]
#assert_axioms corollary_4_7_two []
#assert_axioms krsa_ascent []
#assert_axioms krsa_ascent_free []
#assert_axioms krsa_ascent_iso []
#assert_axioms isUniversalKExtension_unique' []

/-! ## §5 — Bergman–Dicks only, and only where Corollary 4.7(1) is invoked -/

#assert_axioms TwoGen.lemma_5_1 []
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
#assert_axioms TwoGen.prop_5_4_hereditary []
#assert_axioms TwoGen.corollary_5_5_one [bergmanDicksData]
#assert_axioms TwoGen.corollary_5_5_two [bergmanDicksData]
#assert_axioms TwoGen.corollary_5_5_three [bergmanDicksData]
#assert_axioms TwoGen.corollary_5_5_three_nonfree [bergmanDicksData]
#assert_axioms TwoGen.corollary_5_5_three_trace [bergmanDicksData]
#assert_axioms TwoGen.cex_incomparable []
#assert_axioms TwoGen.cex_absorb []

/-! ## The paper layer restates §5, so it must report the same axioms -/

#assert_axioms Paper.lemma_5_2_three []
#assert_axioms Paper.theorem_5_3_backward [bergmanDicksData]
#assert_axioms Paper.corollary_5_5_three [bergmanDicksData]

end KappaMonoid
