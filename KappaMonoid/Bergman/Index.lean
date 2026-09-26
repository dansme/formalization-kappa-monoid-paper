/-
**Index of Bergman's results used in the proof of the realisation theorem.**

The proof of `KappaMonoid.bergmanDicksData` follows two papers:

* **[B1]** G. M. Bergman, *Modules over coproducts of rings*, Trans. AMS 200 (1974), 1–32, in the
  setting of its §9: the base ring `R₀` is a finite product `k^ι` of copies of a field.  In the
  code `R₀` is the index `none : Option Λ`, and `R_λ` is `R l` for `λ = some l`.
* **[B2]** G. M. Bergman, *Coproducts and some universal ring constructions*, Trans. AMS 200 (1974),
  33–88.

Each entry names the declaration that formalises a numbered result, in the style of the
`Paper/` indices.  The build checks that the declarations exist; `#check` one to see what it
states.  Results of [B1] and [B2] that the proof does not need are listed at the end.
-/
import KappaMonoid.Bergman.Realization

universe u

namespace Bergman.Index

/-! ## [B1] *Modules over coproducts of rings* -/

/-- **[B1] Proposition 4.1** — `Bergman.Core.Std.exists_unique_lift`, in `Core/Std.lean`: the
explicit module `Std` on the monomials `s t₁ ⋯ tₙ` has the universal property of the standard
module `⊕ N_μ ⊗ R`. -/
alias B1_prop_4_1 := Bergman.Core.Std.exists_unique_lift

/-- **[B1] Proposition 2.1(1)** — `Bergman.Core.Std.incl_injective`, in `Core/Std.lean`: each
`N_μ` embeds in the standard module. -/
alias B1_prop_2_1_one := Bergman.Core.Std.incl_injective

/-- **[B1] Proposition 2.1(1)**, for an abstract standard presentation —
`Bergman.Core.StdPres.j_injective`, in `Core/Main.lean`. -/
alias B1_prop_2_1_one_pres := Bergman.Core.StdPres.j_injective

/-- **[B1] Proposition 2.1(2)** — `Bergman.Core.Std.Φ`, in `Core/Std.lean`: as an `R_μ`-module the
standard module is `N_μ` plus a free module on the monomials not on side `μ`. -/
alias B1_prop_2_1_two := Bergman.Core.Std.Φ

/-- **[B1] Lemma 5.1** — `Bergman.Core.lead_letter`, in `Core/Pure.lean`: multiplying an element
that is not `λ`-pure by a letter of `R_λ` gives a `λ`-pure element with the expected leading
term. -/
alias B1_lemma_5_1 := Bergman.Core.lead_letter

/-- **[B1] Definition 5.2** — `Bergman.Core.WP`, in `Core/Pure.lean`: well-positioned families. -/
alias B1_def_5_2 := Bergman.Core.WP

/-- **[B1] Lemma 6.1** — `Bergman.Core.exists_step_presIndex_lt`, in `Core/Prop62.lean`: if the
images are not well-positioned, a basic transfer or a transvection lowers the index.  One lemma per
failing condition: `presIndex_lt_of_not_pureS` (`(a_λ)`), `presIndex_lt_of_not_pure_none` (`(a_0)`)
and `presIndex_lt_of_lead` (`(b)`). -/
alias B1_lemma_6_1 := Bergman.Core.exists_step_presIndex_lt

/-- **[B1] Proposition 6.2** — `Bergman.Core.exists_reach_wp`, in `Core/Prop62.lean`: finitely many
basic transfers and transvections make the images of a finitely generated standard module
well-positioned. -/
alias B1_prop_6_2 := Bergman.Core.exists_reach_wp

/-- **[B1] Lemma 8.1** — `Bergman.Core.Idx.linearIndependent_V`, in `Core/Prop82.lean`: the
products `t_n ⋯ t_1 q` have distinct leading terms (`Idx.K_injective`), hence are linearly
independent. -/
alias B1_lemma_8_1 := Bergman.Core.Idx.linearIndependent_V

/-- **[B1] Proposition 8.2** — `Bergman.Core.SubFam.lift_of_wp`, in `Core/Prop8.lean`: a
well-positioned family is a standard presentation of the submodule it generates. -/
alias B1_prop_8_2 := Bergman.Core.SubFam.lift_of_wp

/-- **[B1] Lemma 8.3** — `Bergman.Core.mem_range_of_mem_span`, in `Core/Prop82.lean`, in the form
used for Proposition 8.4. -/
alias B1_lemma_8_3 := Bergman.Core.mem_range_of_mem_span

/-- **[B1] Proposition 8.4** — `Bergman.Core.SubFam.eq_incl_of_wp`, in `Core/Prop8.lean`: a
well-positioned family generating the standard module is its family of components. -/
alias B1_prop_8_4 := Bergman.Core.SubFam.eq_incl_of_wp

/-- **[B1] Theorem 2.3**, for isomorphisms — `Bergman.Core.exists_reach_of_equiv`, in
`Core/Main.lean`: basic transfers and transvections turn a presentation of `M` into one with the
components of any `M' ≅ M`. -/
alias B1_thm_2_3 := Bergman.Core.exists_reach_of_equiv

/-- **[B1] Corollary 2.6** — `Bergman.Core.exists_pres_of_projective`, in `Core/Main.lean`: a
finitely generated projective module is standard, with finitely generated projective
components. -/
alias B1_cor_2_6 := Bergman.Core.exists_pres_of_projective

/-- **[B1] Corollary 2.6** on `V` — `Bergman.IsCoprod.coprodV_surjective`, in `Coprod.lean`. -/
alias B1_cor_2_6_V := Bergman.IsCoprod.coprodV_surjective

/-- **[B1] Corollary 2.8** — `Bergman.IsCoprod.coprodV_eq_iff`, in `Coprod.lean`: `V` of the
coproduct is the pushout of the `V(R_λ)` over `V(k^ι)`. -/
alias B1_cor_2_8 := Bergman.IsCoprod.coprodV_eq_iff

/-! ## [B2] *Coproducts and some universal ring constructions* -/

/-- **[B2] Theorem 5.1**, reduced to a coproduct — `Bergman.IsIdemExt.isCoprod`, in
`Morita.lean`: after passing to a matrix ring, adjoining a universal idempotent is a coproduct with
`k × k`. -/
alias B2_thm_5_1_coprod := Bergman.IsIdemExt.isCoprod

/-- **[B2] Theorem 5.1** on `V` — `Bergman.PresentedBy.idemExt`, in `Steps.lean`: a universal
idempotent `E` adds `[E]`, `[1 - E]` and the relation `[E] + [1 - E] = n [R]`. -/
alias B2_thm_5_1 := Bergman.PresentedBy.idemExt

/-- **[B2] Theorem 5.2**, reduced to a coproduct — `Bergman.IsIsoExt.isCoprod`, in `Morita.lean`:
after passing to a matrix ring, adjoining a universal isomorphism is a coproduct with
`M₂(k) × k`. -/
alias B2_thm_5_2_coprod := Bergman.IsIsoExt.isCoprod

/-- **[B2] Theorem 5.2** on `V` — `Bergman.PresentedBy.isoExt`, in `Steps.lean`: a universal
isomorphism between two nonzero projectives adds the relation `[P] = [Q]`. -/
alias B2_thm_5_2 := Bergman.PresentedBy.isoExt

/-- **[B2] Theorem 6.2**, with Bergman–Dicks for arbitrary monoids — `Bergman.realization`, in
`Realization.lean`, packaged as `KappaMonoid.bergmanDicksData`. -/
alias B2_thm_6_2 := Bergman.realization

/-- **Heredity**, replacing [B1] Corollary 2.5 and the universal derivations of Bergman–Dicks —
`Bergman.RingPres.quasiFree`, in `MainRing.lean`, and `Bergman.QuasiFree.isHereditary`, in
`QuasiFree.lean`: the realising ring is quasi-free, and quasi-free algebras over a field are
hereditary. -/
alias heredity_quasiFree := Bergman.RingPres.quasiFree

/-- **Heredity** — `Bergman.QuasiFree.isHereditary`, in `QuasiFree.lean`. -/
alias heredity_isHereditary := Bergman.QuasiFree.isHereditary

/-! ## Not formalised

The proof does not need these, so they are not formalised.

* **[B1] Theorem 2.2 and Proposition 7.1** (every submodule of a standard module is standard).
  Corollary 2.6 is obtained instead from Propositions 6.2 and 8.2 and Theorem 2.3
  (`exists_pres_of_projective`).
* **[B1] Corollaries 2.4 and 2.5** (homological dimension of a coproduct).  Heredity comes from
  quasi-freeness instead.
* **[B1] Theorem 2.3 for surjections that are not isomorphisms**, Corollaries 2.9–2.17, and
  §§10–15.  Only the isomorphism case enters Corollary 2.8.
* **[B2] §§7–13**, apart from Theorem 6.2.
-/

end Bergman.Index
