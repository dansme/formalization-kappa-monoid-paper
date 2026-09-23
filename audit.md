# Audit: the Lean formalisation against `kappa_monoids.tex`

Audit of commit `ad14b3d`, dated 2026-09-23.

**Bottom line:** no critical problems. There are six real gaps: one that weakens two headline statements, four places where the paper claims something that isn't formalised and the repo doesn't say so, and one statement proved only in a special case. The remaining findings are encoding conventions that do no harm, small missing sub-claims, and documentation errors.

- **Checked:** all 50 numbered items of §§2–5, plus the unnumbered prose claims that later results depend on.
- **Not relied on:** `README.md`, docstrings and comments.
- **Faithful:** every formalised statement says what the paper says, and none is vacuous or about the wrong object.
- **Core definitions** match the paper: κ-monoids, λ⁻-monoids, homomorphisms, generated submonoids, braidings, universal κ-extensions, V^κ(C) and λ⁻-small modules.
- **The one axiom** is no stronger than the published Bergman / Bergman–Dicks theorems.

## How it was checked

- **Proof integrity, checked directly:**
  - The build is green and up to date (`lake build --no-build`: all 8783 jobs up to date).
  - `Lean.collectAxioms` over all 2933 `KappaMonoid` declarations found no `sorryAx`.
  - Exactly 28 declarations use `bergmanDicksData`: Prop 2.16 (through `leavittData`), Cor 4.7(1), Thm 5.3, Cor 5.5 and their `Paper.*` aliases. Everything else uses only `propext`, `Classical.choice` and `Quot.sound`.
  - Every file under `KappaMonoid/` is in the root import closure.
  - There is no `native_decide`, `implemented_by`, `unsafe`, `opaque` or custom elaborator affecting proofs.
  - `#assert_axioms` fails both ways: tested with a `sorry`, an extra axiom and a missing axiom.
- **Scale:** 195 agents in total.
  - One auditor per item, working from the tex and the Lean definition bodies.
  - Second opinions on Definitions 2.1, 2.18, 3.1 and 3.11 and Theorems 3.12, 4.3 and 5.3.
  - Separate audits of the axiom (fidelity to the literature, and consistency), overall proof integrity, and the Core encodings.
  - Every critical or major finding went to 3 independent verifiers told to refute it (one reading the paper, one the Lean, one judging impact); every minor finding went to 1.
  - A completeness critic, followed by 12 follow-up audits of the gaps it found.
- **Verification outcome:** no finding was refuted.

## Confirmed gaps (major, 3/3 verifiers)

1. **"Hereditary" is only one-sided.** This is the one that touches headline statements.
   - Cor 4.7(1)(ii) (tex 1803) says "hereditary k-algebra", deliberately set against "right hereditary ring" in (iii).
   - Thm 5.3's closing sentence (tex 2112) and the unnumbered remark before Cor 5.5 also say "hereditary".
   - Lean concludes only `IsLeftHereditary R`.
   - The cause is the axiom's field `hereditary : IsLeftHereditary R` ([Axioms/Modules.lean:29](KappaMonoid/Axioms/Modules.lean#L29)). Bergman's Thm 6.2 gives a ring hereditary on both sides, and Bergman–Dicks (1978, p. 315) drops "finitely generated".
   - The fix is to strengthen the field to `IsHereditary`, which already exists in [ForMathlib/Hereditary.lean](KappaMonoid/ForMathlib/Hereditary.lean#L34). That changes the assumed result, so it needs the author's decision.
2. **Example 2.13**, two claims not formalised and not listed as omitted:
   - "[P] is a faithful order-unit for every progenerator P" (tex 718, and its V(R) version at tex 687).
   - "H_α = V^α(R) for all infinite α ≤ κ" (tex 720).
3. **Remark 2.19, second half** (tex 862–865): compatible λ-monoid structures for λ < κ define a κ⁻-monoid.
   - Only the restriction direction exists (`LMonoid.ofLE`).
   - Nothing downstream uses it.
4. **Example 4.2(2)** is proved only for regular λ ([Modules/Small.lean:216](KappaMonoid/Modules/Small.lean#L216)).
   - The paper claims it for any infinite λ, and the claim is true: μ < λ generators map into at most max(μ, ℵ₀) < λ summands.
   - Low impact, since every use in the repo has regular λ.
5. **Examples 4.8(4)** (tex 1897–1912), the Dedekind case:
   - Its monoid-theoretic content is unformalised: the braiding criterion over {0} ∪ (ℕ≥1 × G), and the explicit universal extension.
   - The repo's reason for skipping it ("the κ-step is Theorem 4.3 or Prop 3.15", in `Paper/Section4.lean` and `README.md`) is wrong here. Prop 3.15 is about submonoids of ℕ₀ⁿ, and this monoid isn't one when G ≠ 0.

## Not formalised, and the repo says so (reasons checked)

- **Cor 4.6** rests on literature. Its hereditary special case could be assembled today from Albrecht (`Albrecht.exists_directSum_fg`) plus Cor 4.5(3), but isn't.
- **Remark 3.18** is a pointer to the literature. Its third sentence ("Prop 3.15 therefore determines…") isn't stated either.
- **Examples 4.8(2)** is a question; **(5)–(7)** rest on literature. Those reasons are accurate.
- **Examples 4.8(3):** every monoid computation is formalised; only the transport back to V^{ℵ₀}(R) is missing.

## Unrecorded omissions in prose and packaging (minor)

- **§5 preamble** (tex 1989–1991): the one-generator realisation criterion ℵ₀x ≠ nx. [Paper/Section5.lean](KappaMonoid/Paper/Section5.lean) has no "not formalised" section at all.
- **§2.2.1:**
  - The only-if half of the list of realisable cyclic monoids (C_{0,n} forces R = 0 and n = 1).
  - "The generator of a cyclic κ-monoid is an order-unit" (tex 769).
  - `KGenerates κ {[R]}` for V^κ(𝓕^κ), the converse of the "precisely" claim at tex 805.
- **Missing sub-claims inside numbered items:**
  - Lemma 2.15: the isomorphism is shown only for binary `+`, not for κ-sums.
  - Ex 3.3(3): "braided over ℚ≥0" is never stated (it follows in one line).
  - Remark 3.9: the coarsening's pieces are never said to be the connected components.
  - Ex 3.16: Ĥ ≅ F_ℵ₀ is not formalised, and the solution set of 2x = x + y is only shown to differ from Ĥ, not computed.
  - Ex 3.17: non-braidedness is proved with different families from the paper's, and neither the composite Ĥ = H′ + ℵ₀H′ nor the explicit listings are stated.
  - Ex 4.2: "ℵ₁⁻-small ⇔ ℵ₀-small" has only one direction.
  - Cor 5.5: the counterexample ℕ₀² ∪ {∞} is never shown to satisfy §5's standing hypotheses (2-generated, non-cyclic).
- **Prose after Prop 3.15 and after Cor 4.5/4.7:**
  - The slack-variable claim (tex 1444) is done only for the one example.
  - Non-saturation of equation-defined κ-submonoids (tex 1448) is never witnessed.
  - No stand-alone lemma for F_κ(B) = F_κ^B when |B| ≤ κ (tex 663).
  - No transport lemma for "V^{ℵ₀}(R) determines V^κ(R)" (tex 1743–1748). An auditor built a scratch proof of about 15 lines.
- **Unnumbered remark before Cor 5.5:** its general-H form is only a composition of two lemmas, not a named declaration.

## Encoding conventions (confirmed harmless)

- **Braidings use an ι × ℕ normal form** instead of an arbitrary limit well-order. They are proved equivalent (`isBraidedOn_iff_isBraided`, [Braiding/WellOrder.lean:795](KappaMonoid/Braiding/WellOrder.lean#L795)), but Lemmas 3.2, 3.4 and 3.6–3.8 are stated only in the normal form.
- **Left modules stand in for right modules;** transport is via Rᵒᵖ.
- **One universe** holds R, the modules, the index sets and κ (and in §5 also k and H).
- **Universal extensions:**
  - `IsUniversalKExtension` takes the universe of its test objects as a parameter. The theorems that produce it hold in every such universe.
  - "Universal ⇒ braided" is proved only for Ĥ : Type (max u v).
- **λ⁻-submonoids** are encoded as an injective λ⁻-homomorphism X → H.
- **Equivalent or stronger restatements:**
  - Prop 2.9(2) is stated at the λ⁻ level.
  - Lemma 3.14(2) assumes "braided" rather than "universal".
  - Thm 4.3's "in particular" is stated at the monoid level (`corollary_4_4`, which also gives universality).
  - Prop 5.4's hereditary half is proved under `EveryProjectiveIsSumOfFG`, which is stronger.
- **Prop 2.16** depends on the axiom: Leavitt's theorem is derived from the finitely generated case of Bergman's theorem, whereas the paper cites Leavitt.
- **No literal transcription of Def 2.18** proved equivalent, unlike Def 2.1 (`Paper/Definition21.lean`). Auditors checked the equivalence by hand.

## Documentation errors (examples)

- [Paper/Section2.lean:199](KappaMonoid/Paper/Section2.lean#L199) says "Nothing" in §2 is unformalised. That's false: see Example 2.13, Remark 2.19 and the §2.2.1 prose above.
- `corollary_4_7_one_backward` is labelled "(iii) ⇒ (i)" but proves only generation. The full iff, `corollary_4_7_one`, is fine.
- Stale docstrings:
  - Prop 3.15 still calls `prop_3_15_two` a "Deviation" and misquotes the saturation remark.
  - A Thm 5.3 docstring calls the forward hypothesis weaker than the paper's.
  - Two comments give the wrong path for the axiom file.
  - The "Lemma 2.5" labels point at constructors.
  - `cmul_cmul` cites a nonexistent "Lemma 2.7(4)".
- The Lean notation `V(R)` means the paper's V^{ℵ₀}(R), not its V(R).
- **CI:** the axiom grep in `lean_action_ci.yml` misses dotted, `private` and indented axiom names. The `collectAxioms` sweep above is the authoritative check.
- **Axiom audit list:** `Paper/AxiomAudit.lean` omits Lemma 3.8, Prop 3.10, and the universality and braiding results of Examples 3.13 and 3.3(2).

## Possible fixes to the paper (each checked against the tex)

- **Examples 4.8(1):** "KRSA ⇔ V(C) free abelian" should be about V(C_fg). C is closed under κ-sums, so M^(ℕ) ⊕ M ≅ M^(ℕ) makes V(C) non-cancellative.
- **Examples 3.3(2), tex 954–955:** the "finite vs infinite support" argument doesn't show the trivial extension is non-braided, because those two families have different sums there. The Lean uses geom vs 2·geom instead.
- **Def 2.11:** the ℤ/2 example of non-antisymmetry is not a κ-monoid, since κ-monoids are reduced. A κ-monoid example exists: [R] and [R²] in V^κ(R) when R ≅ R³.

## Per-item verdicts

"Faithful, caveats" means faithful in substance, with only the minor conventions or omissions listed above.

| Item | Verdict | Item | Verdict |
|---|---|---|---|
| Def 2.1 | faithful (2 audits) | Lemma 3.8 | faithful, caveats |
| Remark 2.2 | faithful, caveats | Remark 3.9 | faithful, caveats |
| Examples 2.3 | faithful, caveats | Prop 3.10 | faithful |
| Def 2.4 | faithful, caveats | Def 3.11 | faithful, caveats (2 audits) |
| Lemma 2.5 | faithful, caveats | Thm 3.12 | faithful (2 audits) |
| Def 2.6 | faithful | Examples 3.13 | faithful |
| Lemma 2.7 | faithful | Lemma 3.14 | faithful, caveats |
| Lemma 2.8 | faithful | Prop 3.15 | faithful |
| Prop 2.9 | faithful, caveats | Example 3.16 | faithful, caveats |
| Def 2.10 | faithful, caveats | Example 3.17 | faithful, caveats |
| Def 2.11 | faithful | Remark 3.18 | not formalised (literature) |
| Def 2.12 | faithful | Def 4.1 | faithful, caveats |
| Example 2.13 | **partial** (gap 2) | Example 4.2 | faithful, caveats (gap 4) |
| Lemma 2.14 | faithful | Thm 4.3 | faithful, caveats (2 audits) |
| Lemma 2.15 | faithful, caveats | Cor 4.4 | faithful |
| Prop 2.16 | faithful, caveats | Cor 4.5 | faithful |
| Prop 2.17 | faithful, caveats | Cor 4.6 | not formalised (literature) |
| Def 2.18 | faithful, caveats (2 audits) | Cor 4.7 | faithful, caveats (gap 1) |
| Remark 2.19 | **partial** (gap 3) | Examples 4.8 | **partial** (gap 5) |
| Def 3.1 | faithful, caveats (2 audits) | Lemma 5.1 | faithful |
| Lemma 3.2 | faithful | Lemma 5.2 | faithful, caveats |
| Examples 3.3 | faithful | Thm 5.3 | faithful, caveats (gap 1; 2 audits) |
| Lemma 3.4 | faithful, caveats | Prop 5.4 | faithful, caveats |
| Lemma 3.5 | faithful | Cor 5.5 | faithful, caveats |
| Lemma 3.6 | faithful, caveats | | |
| Lemma 3.7 | faithful, caveats | | |

## Status of the major gaps (follow-up commit)

All five major gaps above are closed; the build is green, `sorry`-free, and layering passes.

1. **Hereditary on both sides.** The axiom's field is now `hereditary : IsHereditary R`, which is what Bergman's Theorem 6.2 provides (extended to arbitrary monoids by Bergman–Dicks). Corollary 4.7(1)(ii) and Theorem 5.3 (`TwoGen.theorem_5_3`, `theorem_5_3_backward`, `Paper.theorem_5_3_backward`) now conclude `IsHereditary R`. Corollary 4.7(1)(iii), the paper's "right hereditary", stays `IsLeftHereditary`, its mirror image for left modules. The axiom's name is unchanged, but its statement is stronger. It still stays within the published theorem.
2. **Example 2.13.** Two new files:
   - `Core/OrderUnitTransfer.lean`: a faithful order-unit moves along `u ≼ n v`, `v ≼ m u`.
   - `Modules/Rings/Progenerator.lean`:
     - `isFaithful_of_isProgenerator` shows that `[P]` is a faithful order-unit for every progenerator.
     - `part_unitClass_eq_of_aleph0_le` and `part_unitClass_eq_of_lt_aleph0` show H_α = V^α(R) for infinite α, and H_n = V(R) for finite n.
     - `exists_add_eq_nsmul_of_isProgenerator` covers the V(R) remark at tex 687.
   - All of these are axiom-free.
3. **Remark 2.19, converse.** `Core/Compatible.lean`:
   - `LMonoid.ofCompatible`, with both round trips (`kMonoidOfLT_ofCompatible`, `ofCompatible_kMonoidOfLT`).
   - It needs κ > ℵ₀, which the paper does not say (at κ = ℵ₀ there is no infinite λ < κ). This is documented in the docstring and README.
4. **Example 4.2(2).** `isLambdaSmall_of_span` and `IsLambdaGenerated.isLambdaSmall` now take `ℵ₀ ≤ λ` instead of regularity.
5. **Examples 4.8(4).** `Examples/Dedekind.lean`, for every abelian group G and every infinite κ:
   - E_κ is a κ-monoid (`instKMonoid`).
   - The braiding criterion (`isBraided_iff`).
   - E_κ is braided over D (`isBraidedOver_dedExt`) and is its universal κ-extension (`isUniversalKExtension_dedExt`).
   - All axiom-free.
   - Only Steinitz's theorem V(R) ≅ D is quoted. The repo's inaccurate reason for skipping this item is corrected in `Paper/Section4.lean` and `README.md`.

The index files, `Paper/AxiomAudit.lean` and `README.md` were updated to match, including the "Not formalised" note in `Paper/Section2.lean`, which was false.

The minor findings and documentation errors listed above are not addressed by this commit.

## Status of the documentation errors (follow-up commit)

Every doc-mismatch finding of the audit, 53 in all, is addressed:

- **The `Paper/` indices.**
  - The headers no longer claim that an `alias` checks a type.
  - Lemma 2.5, Remark 2.2 and Examples 3.13 point at the declarations that state them.
  - Aliases now separate a partial result from the full one: the `corollary_4_7_one_backward` generation clause, the Lemma 3.8 core at λ = ℵ₀, the Theorem 4.3 core, and the `simpleListPi` witness.
  - Missing entries were added:
    - the class-level Example 4.2(3) lemmas;
    - Theorem 4.3's "in particular";
    - Lemma 2.7(1) `cmul_zero_cardinal`;
    - §2.2.1 prose;
    - `exists_form`;
    - the remark before Cor. 5.5.
  - Every `Paper/` file now has an accurate "Not formalised" section, and `Paper/Section5.lean` gained one.
- **Library docstrings.**
  - The "Deviation from the paper" for Prop. 3.15(2) is now correctly called a generalisation.
  - Thm 5.3's hypothesis is described as the paper's own.
  - Prop. 5.4 and Cor. 5.5 are no longer described as corrections of the paper.
  - Lemma 3.7 is stated only for the normal-form order.
  - `cmul_cmul` no longer cites a "Lemma 2.7(4)".
  - The Lemma 2.8 idempotence step is labelled consistently.
  - `ModuleClass` no longer mentions summand closure.
  - Example 2.13's header is corrected.
  - The two axiom paths are fixed.
- **Rename.** `isConical_of_isUniversalKExtension` is now `isConical_of_injective_lhom`; it never assumed universality.
- **README.** Examples 4.8(6) now cites Prop. 3.15(1) for the κ-step. The §5 preamble and the §2 prose appear under "What is not formalised", and the entry counts are updated.
- **CI.** The axiom-set check now asks Lean (`scripts/list_axioms.lean`) instead of grepping source text, and the sorry-check step sets `pipefail`.
- **`Paper/AxiomAudit.lean`** now covers Lemma 3.8, Prop. 3.10, the Examples 3.3(2)/3.13 universality results and the §5 `Paper.*` restatements: 111 assertions.

Suggestions to add lemmas are not doc errors and were not taken up: an ext lemma for the Def. 2.1 round trip, and a commutativity statement for Remark 2.2(1).
