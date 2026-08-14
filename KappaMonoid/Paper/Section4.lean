/-
**Section 4 of the paper**: an index of its numbered results.

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

/-- **Definition 4.1** — `KappaMonoid.IsLambdaSmall`, in `Modules/Small.lean`. -/
alias definition_4_1_IsLambdaSmall := KappaMonoid.IsLambdaSmall

/-- **Example 4.2(2)** — `KappaMonoid.isLambdaSmall_aleph0_of_fg`, in `Modules/Small.lean`. -/
alias example_4_2_2_isLambdaSmall_aleph0_of_fg := KappaMonoid.isLambdaSmall_aleph0_of_fg

/-- **Example 4.2(2)** — `KappaMonoid.isLambdaSmall_of_span`, in `Modules/Small.lean`. -/
alias example_4_2_2_isLambdaSmall_of_span := KappaMonoid.isLambdaSmall_of_span

/-- **Theorem 4.3** — `KappaMonoid.DoubleDecomp.isBraided`, in `Modules/Theorem43.lean`. -/
alias theorem_4_3_isBraided := KappaMonoid.DoubleDecomp.isBraided

/-- **Theorem 4.3** — `KappaMonoid.exists_braided_of_iso`, in `Modules/Theorem43.lean`. -/
alias theorem_4_3_exists_braided_of_iso := KappaMonoid.exists_braided_of_iso

/-- **Theorem 4.3** — `KappaMonoid.theorem_4_3`, in `Modules/Theorem43.lean`. -/
alias theorem_4_3_theorem_4_3 := KappaMonoid.theorem_4_3

/-- **Theorem 4.3** — `KappaMonoid.theorem_4_3_core`, in `Modules/Theorem43.lean`. -/
alias theorem_4_3_theorem_4_3_core := KappaMonoid.theorem_4_3_core

/-- **Corollary 4.4(2)** — `KappaMonoid.corollary_4_4`, in `Modules/Theorem43.lean`. -/
alias corollary_4_4_2_corollary_4_4 := KappaMonoid.corollary_4_4

/-- **Corollary 4.5(1)(2)** — `KappaMonoid.corollary_4_5`, in `Modules/Projective.lean`. -/
alias corollary_4_5_1_2_corollary_4_5 := KappaMonoid.corollary_4_5

/-- **Corollary 4.5(3)** — `KappaMonoid.corollary_4_5_three`, in `Modules/Projective.lean`. -/
alias corollary_4_5_3_corollary_4_5_three := KappaMonoid.corollary_4_5_three

/-- **Corollary 4.6** — `KappaMonoid.corollary_4_6`, in `Modules/Projective.lean`. -/
alias corollary_4_6_corollary_4_6 := KappaMonoid.corollary_4_6

/-- **Corollary 4.7(1)** — `KappaMonoid.corollary_4_7`, in `Modules/Projective.lean`. -/
alias corollary_4_7_1_corollary_4_7 := KappaMonoid.corollary_4_7

/-- **Corollary 4.7(1)** — `KappaMonoid.corollary_4_7_one_backward`, in `Modules/Corollary47.lean`. -/
alias corollary_4_7_1_corollary_4_7_one_backward := KappaMonoid.corollary_4_7_one_backward

/-- **Corollary 4.7(1)** — `KappaMonoid.corollary_4_7_one_backward_braided`, in `Modules/Corollary47.lean`. -/
alias corollary_4_7_1_corollary_4_7_one_backward_braided := KappaMonoid.corollary_4_7_one_backward_braided

/-- **Corollary 4.7(1)** — `KappaMonoid.corollary_4_7_one_forward`, in `Modules/Corollary47.lean`. -/
alias corollary_4_7_1_corollary_4_7_one_forward := KappaMonoid.corollary_4_7_one_forward

/-- **Corollary 4.7(2)** — `KappaMonoid.corollary_4_7_two`, in `Modules/Corollary47.lean`. -/
alias corollary_4_7_2_corollary_4_7_two := KappaMonoid.corollary_4_7_two

/-- **Example 4.8(1)** — `KappaMonoid.krsa_ascent`, in `Modules/Corollary47.lean`: `V^κ(C)` is
`λ⁻`-braided over `F_{λ⁻}(B)`. -/
alias example_4_8_1_krsa_ascent := KappaMonoid.krsa_ascent

/-- **Example 4.8(1)**, the isomorphism `V^κ(C) ≅ F_κ(B)` the paper states —
`KappaMonoid.krsa_ascent_iso`, in `Modules/Corollary47.lean`.  Expressible only since the test
universe of `IsUniversalKExtension` became a parameter; the two sides live one universe apart. -/
alias example_4_8_1_iso := KappaMonoid.krsa_ascent_iso

/-- **Example 4.8(1)**, the `B`-indexed universal property — `KappaMonoid.krsa_ascent_free`. -/
alias example_4_8_1_free := KappaMonoid.krsa_ascent_free


/-! ## Not formalised, deliberately

* **Corollary 4.6** is Corollary 4.5(3) together with six results quoted from the literature —
  weakly semihereditary (Bergman), one-sided semihereditary (Bergman), exchange (Warfield),
  semiperfect (Mueller), weakly noetherian commutative (Hinohara), Bézout with one-sided Krull
  dimension (McGovern–Puninski–Rothmaler) — none of them monoid-theoretic and none in Mathlib.
  `corollary_4_6` is a documented stub, and `EveryProjectiveIsSumOfFG` is the hypothesis the six
  would supply.
* **Examples 4.8(2)** is not formalised.

Examples 4.8(1) *is* formalised as printed, `V^κ(C) ≅ F_κ(B)` included (`krsa_ascent_iso`).  It was
a documented deviation until the test universe of `IsUniversalKExtension` became a parameter: the
two sides live one universe apart, and the old definition could not compare them. -/

end Paper

end KappaMonoid
