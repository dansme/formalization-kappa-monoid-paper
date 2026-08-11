# Section 3

A record of how §3 of Nazemian–Smertnig was formalised, and of what was left out.

Baseline: branch `simplify`. `lake build` is green and `sorry`-free with every §3 file imported —
§3 is complete; see "What is missing" for the two deliberate omissions and one loose end.

Paper source: `kappa_monoids.tex` / `kappa_monoids.pdf`.

## What §3 already has

| Paper | Where |
|---|---|
| Def. 3.1 (braiding, braided over) | `BraidingData`, `IsBraided`, `IsBraidedOver` |
| Lemma 3.2 (telescoping: braided ⟹ equal sums) | `sumOf_eq_of_isBraided` |
| Lemma 3.4(1) (small support) | `isBraided_of_small_support` |
| Lemma 3.4(4) (`λ ≠ ℵ₀` collapse) | `isBraided_iff_of_ne_aleph0`, `of_partition` |
| Lemma 3.6 (permutation, reflexive, symmetric) | `IsBraided.of_perm`, `.refl`, `.symm` |
| Lemma 3.7 (repartition) | `exists_repartition` |
| Lemma 3.8 (transitivity) | `IsBraided.trans` |
| Prop. 3.9 (extension along a braiding) | `extend_lhom` |
| Def. 3.10, Theorem 3.11 | `IsUniversalKExtension`, `theorem_3_11`, `theorem_3_11_of_aleph0_lt` |

And, in `Section32.lean`:

| Paper | Where |
|---|---|
| Examples 3.3(1) (braiding in `ℕ₀`, both cases) | `isBraided_nat_of_finite_support`, `isBraided_nat_of_infinite_support` |
| Examples 3.12, first entry (`ℕ̂₀ ≅ ℕ₀ ∪ {∞}`) | `isBraidedOver_withTop_nat`, `isUniversalKExtension_withTop_nat` |
| Lemma 3.13(1) (free objects) | `freeIncl`, `lemma_3_13_free` |
| Lemma 3.13(2) (saturated submonoids, both cases) | `IsSaturated`, `isBraidedOver_of_isLSubmonoid`, `lemma_3_13_sub_of_subset`, `lemma_3_13_sub` |
| Prop. 3.14, the definitional work | `LinSystem`, `linEval`, `solutions`, `isKSubmonoid_solutions`, `mem_solutions_map`, `mem_solutions_of_incl`, `finSolutions`, `alephPart`, `alephExt`, `addSubmonoid_finSolutions`, `alephExt_subset_solutions`, `isKSubmonoid_alephExt` |

**Lemma 3.4(2)(3) and Lemma 3.5 are deliberately absent.** The `ι × ℕ` normal form for braiding
partitions *is* their content: a braiding breaks into a disjoint union of countable ones and
conversely, and the relation does not depend on the chosen limit well-order. Restating them
would mean reintroducing abstract limit well-orders purely to prove they do not matter. See the
README's "The limit well-order" note. Leave them alone unless you specifically want the
well-order independence as a theorem, in which case it is a project of its own and should be
scoped separately.

| Prop. 3.14(1) | `isBraidedOver_pi_fcard`, `solutions_subset_kclosure`, `prop_3_14_one` |
| Prop. 3.14(2) | `isBraidedOver_pi_lcard`, `alephPart_eq_ksum`, `prop_3_14_two` (with an added hypothesis, see below) |
| Examples 3.3(2)(3), Examples 3.12 for `ℝ≥0`/`ℚ≥0` (in `Reals.lean`) | `esum`, `isBraided_nnreal_iff`, `not_isBraided_single2_geom`, `not_isBraided_geom_two_geom`, `RTilde`, `RTilde.instKMonoid`, `isBraidedOver_rtilde`, `isUniversalKExtension_rtilde`, `not_isBraidedOver_rtilde_self`, `isUniversalKExtension_ratSet`, `exists_ratSet_family`, `kclosure_ofReal_ratSet` |
| The converse of Lemma 3.4(1) (in `Braiding.lean`) | `IsBraided.mk_support_lt` |
| Saturation for systems of equations and congruences | `linEvalNat`, `val_linEval_eq_linEvalNat`, `isSaturatedFin_of_ineqs_empty`, `prop_3_14_two_of_ineqs_empty` |
| The counterexample to Prop. 3.14(2) as printed | `ineqSystem`, `not_isSaturatedFin_ineqSystem` |
| Example 3.15 | `diagSystem`, `doubleSystem`, `mem_diagSystem_solutions`, `mem_doubleSystem_solutions`, `finSolutions_diagSystem`, `alephExt_congr`, `example_3_15` |

And, in `Universal.lean`:

| Paper | Where |
|---|---|
| Theorem 3.11 read as an equivalence (universal ⟹ braided over) | `IsBraidedOver.of_iso`, `IsBraidedOver.of_base_iso`, `isBraidedOver_of_isUniversalKExtension` |

`Section32.lean` is `sorry`-free and imported by `KappaMonoid.lean`.

## What is missing

Nothing: §3 is complete and `sorry`-free, `KappaMonoid/Reals.lean` included. Two things are left
open on purpose, and one is a loose end worth recording:

1. **Lemma 3.4(2)(3), Lemma 3.5, Remark 3.16** — deliberately absent, see above and below.
2. The *braiding* half of the counterexample to Prop. 3.14(2) — only the failure of saturation is
   formalised (`not_isSaturatedFin_ineqSystem`); the braiding computation is in its docstring.
3. Nothing further for `ℚ≥0`: `kclosure_ofReal_ratSet` identifies the extension as
   `ℚ≥0 ∪ ℝ̃>0 ∪ {∞}` on the nose, both inclusions, on top of
   `exists_ratSet_family` (every positive real is the sum of a series of positive rationals).

---

## Ground rules

`CLAUDE.md` carries the conventions, the workflow and the accumulated elaboration traps — all of
the traps below were met in §3 and are recorded there. Specific to §3:

- §3 needs **no axiom**; `#print axioms` on any §3 result must report only `propext`,
  `Classical.choice`, `Quot.sound`.
- Prove at the `λ⁻` level and specialise to `κ` wherever the statement allows it — most of §3 is
  stated for `lam` and used at `lam = ℵ₀` or `lam = ℵ₁`.
- The two deviations from the paper (the `IsConical` hypothesis in Theorem 3.11, the
  `IsSaturatedFin` hypothesis in Proposition 3.14(2)) are documented in the docstrings and in
  `README.md`; keep it that way if a third appears.

---

## How §3.2 fits together

For the record, since it took some finding. Both halves of Prop. 3.14 are Lemma 3.13(2) applied to
an ambient braided extension coming from Lemma 3.13(1):

| | 3.14(1) | 3.14(2) |
|---|---|---|
| base `X` | `F_{ℵ₀}^n` | `ℕ₀^n` |
| ambient `Ĥ` | `F_κ^n` | `F_{ℵ₀}^n` |
| `λ` | `ℵ₁` | `ℵ₀` |
| `S` | the `ℵ₀`-solutions | `H` = the solutions with finite components |
| `T = ⟨S⟩_κ` | the `κ`-solutions | `H + ℵ₀H` |
| which branch of 3.13(2) | `λ ≠ ℵ₀` | `S` saturated |

The two ambient braidings are `isBraidedOver_pi_fcard` and `isBraidedOver_pi_lcard`. Both are
obtained by reading `lemma_3_13_free` at `B = ULift (Fin n)` through
`isBraidedOver_of_isUniversalKExtension` and transporting along the isomorphisms
`F_{λ⁻}(ULift (Fin n)) ≅ F_{λ⁻}^n` (the support condition is vacuous for a finite basis, and the
reindexing is `ULift`). Three ingredients made this possible and are worth remembering:

* `theorem_3_11` had to be generalised from `X : Type u` to `X : Type v` — the construction never
  needed the restriction, but `F_κ^n` lives in `Type (u+1)`;
* `lemma_3_13_sub_of_subset` states 3.13(2) for any `T` with `f(S) ⊆ T ⊆ ⟨f(S)⟩_κ`, which avoids
  rewriting a set equality inside a type;
* `isLMonoidHom_aleph0_of_add`: at `λ = ℵ₀` a homomorphism is just an additive map, which is what
  lets the two different `ℵ₀⁻`-monoid structures on `H` (pointwise cardinal sums, and
  `LMonoid.ofAddCommMonoid`) be compared at all.

## The hypothesis added to Prop. 3.14(2)

The paper's remark that `H` is automatically saturated is false for systems with inequalities, and
Prop. 3.14(2) fails with it — see the README section "The hypothesis added to
Proposition 3.14(2)" and `not_isSaturatedFin_ineqSystem`. `prop_3_14_two` takes saturation as the
hypothesis `IsSaturatedFin`; for systems without inequalities `isSaturatedFin_of_ineqs_empty`
discharges it, so `prop_3_14_two_of_ineqs_empty` needs nothing but `sys.ineqs = ∅`.

## Remark 3.16

Remark 3.16 (saturated submonoids of `ℕ₀^n` are finitely generated reduced Krull monoids, citing
the literature) is a pointer, not a theorem. Either skip it or record it in the README.

## How Examples 3.3(2)(3) came out

For the record, since the plan's guesses were only half right.

The carrier is **not** an inductive with a positivity side condition but
`{p : ℝ≥0∞ × Bool // p.2 = true → p.1 ≠ 0 ∧ p.1 ≠ ⊤}`: a value together with a tilde flag that
only a value which is neither `0` nor `∞` may carry. That gives exactly one `0` and one `∞` with no
quotient, and — the part that matters in practice — the summation can be written as a *single* term
(`sigmaFlag` computes the flag separately), so `val` and `tilded` of a sum are `rfl`. The
three-branch `dite` the plan suggested makes every branch lemma fight the dependent motive, because
`RTilde` is a `def` and the projections cannot be seen through.

`sum_congr` and `sum_unique` are routine; `sum_sigma` is `isPlain_sigma_iff`, exactly the statement
the plan predicted (the marking is associative because, for a family with finite total, the family
of row sums is plain iff the whole double family is).

The braiding construction for `ℝ≥0` is *simpler* than the `ℕ₀` one, not a variation of it: keep the
two cumulative partial sums and alternately overshoot, `u k = X(bI (k+1)) − Y(bJ k)` and
`v k = Y(bJ k) − X(bI k)`. The deficits then telescope by `tsub_add_tsub_cancel` with no case
analysis, and the only analytic inputs are `coe_psum_lt_esum` (with infinite support no partial sum
reaches the total) and `exists_psum_ge`.

`ℚ≥0` needed no new *braiding* at all: `ℚ≥0` is a *saturated* `ℵ₀⁻`-submonoid of `ℝ≥0`, so
Lemma 3.13(2) applies at `λ = ℵ₀`. That is a forward reference from §3.1 to §3.2 — hence
`Reals.lean` importing `Section32.lean` — but it replaces a second run of the whole braiding
argument. It did need one analytic fact: every positive real is the sum of a series of positive
rationals (`exists_ratSet_family`). The cheap route is a case split — a rational value gets the
geometric family already in hand, an irrational one the increments of its dyadic truncations
`⌊a·2ⁿ⌋/2ⁿ`, where irrationality is what keeps infinitely many increments nonzero. No recursion
with invariants and no sequence-existence lemma from Mathlib are needed.

## Where to go next

§3 is done. The open items are listed under "What is missing"; none blocks §§4–5, whose plans are
`SECTION4-PLAN.md` and `SECTION5-PLAN.md`.
