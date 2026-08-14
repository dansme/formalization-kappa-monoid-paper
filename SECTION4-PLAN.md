# Section 4 — implementation plan

**Section 4 is done.**  This document is now the record of how it was built and of the two places
where the formalisation departs from the paper; `KappaMonoid/Section4/AddOf.lean` is part of the root
build and is `sorry`-free.

## Ground rules

`CLAUDE.md` carries the conventions, the workflow and the elaboration traps. Specific to §4:

- Trap 1 of `CLAUDE.md` bites here as `(projClass R κ hκ).carrier`, and trap 2 as
  `lambdaSmallPart`, which is a subtype of a subtype.
- Only Corollary 4.7(1)'s forward direction may report `bergmanDicksData` (axiom A5); re-run
  `#print axioms` after each change and keep the provenance table in `README.md` in step.

## Where Section 4 lives

`KappaMonoid/ModuleClass.lean` carries the section through Corollary 4.5:

| Paper | Lean |
| --- | --- |
| Definition 4.1 (`λ`-small) | `IsLambdaSmall` |
| Example 4.2(2) | `isLambdaSmall_of_span`, `isLambdaSmall_aleph0_of_fg` |
| Example 4.2(3) | `lambdaSmallPart`, `lambdaSmallPart_isLSubset` |
| Theorem 4.3 | `theorem_4_3_core`, `theorem_4_3` |
| (M1), (M2) | discharged inside `theorem_4_3_core` |
| Corollary 4.4 | `corollary_4_4` |
| Corollary 4.5(1)(2)(3) | `corollary_4_5`, `corollary_4_5_three` |
| Kaplansky | `kaplansky` |

Two documented stubs remain there — `corollary_4_6 : True := trivial` and
`corollary_4_7 : True := trivial`.  Both are deliberate: 4.6 is six citations (step 5 below) and
4.7 needs `add x`, so it lives downstream, in `KappaMonoid/Section4/AddOf.lean`:

| Paper | Lean |
| --- | --- |
| `add(x)`, `add_λ(x)` | `KMonoid.addOf`, `KMonoid.addOfCard`, with `addOf_isLSubset`, `addOf_isSaturated`, `addOfCard_isLSubset` |
| `V(R) = add([R])` | `addOf_unitClass_eq` |
| Corollary 4.7(1), (iii) ⇒ (i) | `corollary_4_7_one_backward_braided`, `corollary_4_7_one_backward` |
| Corollary 4.7(1), (i) ⇒ (ii) | `corollary_4_7_one_forward` (axiom A5) |
| Corollary 4.7(2) | `corollary_4_7_two`, on `isKIso_of_braidedOver_same` |
| Examples 4.8(1) | `krsa_ascent`, `krsa_ascent_free` (corrected statement, step 6) |

## Steps 1–3 — done

`addOf_isLSubset`, `addOf_isSaturated`, `addOfCard_isLSubset`,
`isKIso_of_braidedOver_same` and `corollary_4_7_two` are proved, with no axiom.

Notes worth keeping:

- `addOf_isLSubset` adds the witnesses and reads the total coefficient off `cmul_sumOf_cardinal`;
  the coefficient is a natural number because a finite sum of finite cardinals is finite
  (`Cardinal.sum_lt_of_isRegular` then `Cardinal.lt_aleph0`). `addOfCard_isLSubset` is the same
  with the constant coefficient `λ`, using `#ι · λ = λ` for a nonempty index type of size `< λ`;
  the empty case is the zero of the submonoid, not the general argument.
- `isKIso_of_braidedOver_same` is two lines: both sides are universal `κ`-extensions of `S`
  (Theorem 3.11(2)) and those are unique up to a unique isomorphism.

## Step 4 — Corollary 4.7(1) — done

Both directions rest on **`addOf_unitClass_eq`: `add [R] = V(R)`**, i.e. the summands of the finite
multiples of `[R]` are exactly the `ℵ₀⁻`-small classes.  Neither inclusion needs a hypothesis on `R`
(the plan's earlier guess that `isOrderUnit_unitClass` was the tool was wrong: an order-unit gives
`y ≼ κ·[R]`, and what is needed is a *finite* multiple).

- `⊆`: if `y + z = n·[R]` then `rep y × rep z ≅ R^{(Idx n)}`, a finitely generated free module, so
  `rep y` is finitely generated (project) and hence `ℵ₀⁻`-small by Example 4.2(2).
- `⊇`: an `ℵ₀⁻`-small class has a finitely generated representative — that is
  `finite_of_isLambdaSmall_aleph0`, the one genuinely module-theoretic input of the step — and a
  finitely generated projective module is a summand of a finitely generated free module
  (`exists_isCompl_of_projective`, the `Idx κ`-free generalisation of
  `exists_summand_of_projective`).  `exists_add_eq_cmul_unitClass` reads off `y + [Z] = #s·[R]` from
  that splitting with `add_eq_of_relCompl`, and `#s < ℵ₀` is a natural number.

`corollary_4_7_one_backward_braided` is then Corollary 4.5(3) moved along that set equality by
`IsBraidedOver.of_set_eq`: `IsLSubset` is a `Prop`, so once the two subsets are equal the two
induced `LMonoid ℵ₀` instances are definitionally equal and `subst` closes the goal.
`corollary_4_7_one_backward` records the generation form, via `IsBraidedOver.kGenerates_coe`.

`corollary_4_7_one_forward` is (i) ⇒ (ii) and uses **axiom A5**, `bergmanDicksData`:

1. `add x` is reduced with order-unit `x` — reducedness from `KMonoid.isConical` through the
   inclusion (`LMonoid.isConical_of_injective`), the order-unit property straight from the
   definition of `addOf`, with `KMonoid.cmul_natCast` to turn `n • x` into `cmul n x` and a
   four-line induction for `↑(n • u) = n • ↑u` in the submonoid.
2. A5 gives a `BergmanDicksData k ↥(add x)`: a hereditary `k`-algebra `R`, the family
   `P : add x → Type u` of finitely generated projectives, and `sumOfFG`.
3. `sumOfFG` has exactly the shape of the `hfg` hypothesis of `corollary_4_5_three`, so it plugs in
   unchanged and makes `V^κ(R)` `ℵ₀⁻`-braided over `V(R) = lambdaSmallPart ℵ₀`.
4. `BergmanDicksData.exists_isLMonoidHom_bijective` turns `iso_zero`/`iso_add`/`inj`/`surj` into an
   isomorphism of `ℵ₀⁻`-monoids `↥(add x) ≅ ↥(lambdaSmallPart ℵ₀)`.  The bridge in both directions is
   `exists_class_of_fg_projective` (a finitely generated projective is the representative of an
   `ℵ₀⁻`-small class) and, for surjectivity, `finite_of_isLambdaSmall_aleph0`.  Multiplicativity is
   only `isLMonoidHom_aleph0_of_add`, since an `ℵ₀⁻`-sum is a finite sum.
5. `IsBraidedOver.of_base_iso` transports the braiding to `add x`, and
   `isKIso_of_braidedOver_same` identifies `V^κ(R)` with `H`.

(ii) ⇒ (iii) is trivial and needs no separate statement.

§5 later **widened the conclusion**: `corollary_4_7_one_forward` now also returns
`EveryProjectiveIsSumOfFG R`, which costs nothing because `bd.sumOfFG` is already in hand at step 3
and is exactly what Theorem 5.3 and Corollary 5.5 need alongside hereditariness — Corollary 4.6,
the implication that would supply it from hereditariness alone, is quoted here rather than
formalised (step 5). See `README.md`, "The statements corrected in Section 5".

Two elaboration lessons from this step, both now trap entries in `CLAUDE.md` (12, 13): a term whose
type is a `def` that unfolds to a `∀` gets its implicit arguments inserted eagerly when the expected
type is not syntactically a `∀`, which breaks `exact h` against an `∈`-goal (`show` the unfolded form
first); and the maps of `isLMonoidHom_aleph0_of_add`/`of_base_iso` have to be passed by name.

## Step 5 — Corollary 4.6 — nothing to prove

Corollary 4.6 is `corollary_4_5_three` plus six citations: weakly semihereditary (Bergman),
one-sided semihereditary (Bergman), exchange (Warfield), semiperfect (Mueller), weakly noetherian
commutative (Hinohara), Bézout with one-sided Krull dimension (McGovern–Puninski–Rothmaler).
Each says *every projective module is a direct sum of finitely generated modules*, which is
`EveryProjectiveIsSumOfFG` in `Section4/AddOf.lean`; given it, Corollary 4.5(3) concludes.

None of the six is in Mathlib, and none is a monoid-theoretic statement.  **The documented stub in
`ModuleClass.lean` is the correct treatment** — leave it.  `EveryProjectiveIsSumOfFG` exists so the
six implications can be stated the day that module theory lands.

## Step 6 — Example 4.8(1) — done, with a corrected statement

`krsa_ascent` and `krsa_ascent_free` are proved (no axiom), now that Lemma 3.13(1) exists —
`Section4/AddOf.lean` imports `Section3/Diophantine.lean` for it.

**The original statement was not expressible.** It asked for `V^κ(C) ≅ F_κ(B)`. But `F_κ(B)` is cut
out of `B → F_κ` and so lives in `Type (u+1)`, while `V^κ(C)` lives in `Type u`; the `universal`
field of `IsUniversalKExtension` quantifies over test objects `K : Type w` in the *same* universe as
the extension, so `isUniversalKExtension_unique` compares two extensions in one universe only. Two
ways out, should the isomorphism itself ever be wanted:

1. make `universal` quantify over `K` in a fresh universe — `extend_lhom` already works for a `K` in
   any universe, so this is a change to the definition and to Theorem 3.11's statement, not to its
   proof; or
2. compare `ULift`s.

What is proved instead is the universe-correct content: `krsa_ascent` gives that `V^κ(C)` *is* the
universal `κ`-extension of `F_{λ⁻}(B)` (transport `hbr`'s universal property along the isomorphism
of bases), and `krsa_ascent_free` turns that into the `B`-indexed universal property of the free
`κ`-monoid — every map `B → K` extends uniquely along the generators — which is what "`V^κ(C)` is
the free `κ`-monoid on `B`" means. The `λ⁻`-level input is `Free.exists_unique_lift`, whose target
universe is free.

## New infrastructure this section added

Reusable, and in the core files rather than here:

| Lemma | Where | What it does |
|---|---|---|
| `IsLMonoidHom.inv` | `Basic.lean` | the inverse of a bijective homomorphism is a homomorphism |
| `KMonoid.cmul_natCast` | `Basic.lean` | `cmul n x = n • x` for a natural `n`; moved here from `Section2/Rings/Realisation.lean` |
| `IsUniversalKExtension.of_base_iso` | `Universal.lean` | universality transports along an isomorphism of the base — formal, no reducedness needed, unlike `IsBraidedOver.of_base_iso` |
| `isLMonoidHom_of_isLHom`, `isLHom_of_isLMonoidHom` | `Universal.lean` | the two packagings of a homomorphism into a `κ`-monoid; moved here from `Section3/Diophantine.lean` |
| `IsBraidedOver.kGenerates_coe` | `Universal.lean` | braided over a subset ⟹ generated by it |
| `IsBraidedOver.of_set_eq` | `Universal.lean` | braidedness over a `λ⁻`-closed subset depends only on the subset |

Both base transports allow the two bases to live in **independent universes**, which is what
Example 4.8(1) needs (`Type u` against `Type (u+1)`).

Module-theoretic, and specific enough to stay in `Section4/AddOf.lean`:
`finite_of_isLambdaSmall_aleph0` (an `ℵ₀⁻`-small summand of `R^{(κ)}` is finitely generated),
`exists_isCompl_of_projective` (a finitely generated projective is a summand of a finitely generated
free module) and `exists_class_of_fg_projective`.

## Status

Done: `KappaMonoid/Section4/AddOf.lean` is `sorry`-free and imported by `KappaMonoid.lean`, so the root
`lake build` checks it.  `#print axioms` reports `propext`, `Classical.choice`, `Quot.sound` for
everything in the file except `corollary_4_7_one_forward`, which additionally reports
`bergmanDicksData` (A5) — as intended, and the only use of A5 in the build.
