# Completing Section 3

A work plan for the part of §3 of Nazemian–Smertnig that is not yet formalised.

Baseline: branch `simplify`. `lake build` is green and `sorry`-free, `KappaMonoid/Section32.lean`
included — §3 is complete apart from the items under "What is missing" below.

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
| Saturation for systems of equations and congruences | `linEvalNat`, `val_linEval_eq_linEvalNat`, `isSaturatedFin_of_ineqs_empty`, `prop_3_14_two_of_ineqs_empty` |
| The counterexample to Prop. 3.14(2) as printed | `ineqSystem`, `not_isSaturatedFin_ineqSystem` |
| Example 3.15 | `diagSystem`, `doubleSystem`, `mem_diagSystem_solutions`, `mem_doubleSystem_solutions`, `finSolutions_diagSystem`, `alephExt_congr`, `example_3_15` |

And, in `Universal.lean`:

| Paper | Where |
|---|---|
| Theorem 3.11 read as an equivalence (universal ⟹ braided over) | `IsBraidedOver.of_iso`, `IsBraidedOver.of_base_iso`, `isBraidedOver_of_isUniversalKExtension` |

`Section32.lean` is `sorry`-free and imported by `KappaMonoid.lean`.

## What is missing

1. **Examples 3.3(2) and the `ℝ≥0`, `ℚ≥0` entries of Examples 3.12** — not started; see
   "Examples 3.3(2)" below, the only remaining piece of §3.
2. Optionally, the *braiding* half of the counterexample to Prop. 3.14(2) — only the failure of
   saturation is formalised (`not_isSaturatedFin_ineqSystem`); the braiding computation is in its
   docstring.

---

## Ground rules

Same as the rest of the development:

1. **One step = one commit**, with `lake build` green before each.
2. **Prove at the λ⁻ level and specialise to κ** where the statement allows it.
3. **House style**: index types in `Type u`, carriers in `Type v`; docstrings open with the bold
   paper reference; defs producing instances carry `@[instance_reducible]`.
4. **No new axioms** without asking. §3 needs none.
5. **Watch instance resolution on coercions.** Two traps cost real time in §2 and recurred in §3.2:
   a plain `def` is not reducible, so `(freeClass …).carrier` does not unify with `Carrier` during
   instance search — state lemmas at the type instance search expects; and a double coercion like
   `↥↑m` can defeat synthesis outright — state such lemmas over a plain type variable and
   specialise.
6. When a `letI`-in-statement instance argument cannot be inferred from the goal, pass it
   explicitly (`Fcard.instKMonoid_add (le_refl (ℵ₀ : Cardinal.{u}))`); and `rw` will not unfold
   `KMonoid.ksum` to `KMonoid.sumOf`, so convert with `KMonoid.sumOf_Idx` (or `show`) before
   rewriting with the `sumOf` lemmas.
7. **Pin universes in statements that do not mention them.** A hypothesis like
   `(hsat : sys.IsSaturatedFin)` is elaborated before the `letI`s that fix `Cardinal.{u}`, so its
   universe is auto-bound to a *fresh* variable and the proof then fails with
   `constant has level params [u, u_1]`. Write `LinSystem.IsSaturatedFin.{u} sys`.
8. **Pass `g`/`g'` explicitly to the transport lemmas.** `IsLMonoidHom` is a plain `def`, so
   unification against an expected unfolded ∀-type will not solve for the function; supply
   `(g := …)`, `(g' := …)`.

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

## Examples 3.3(2): the `ℝ≥0` example

Not scaffolded. Independent of everything above; nothing else depends on it.

The carrier encoding that works: an inductive `RTilde` with `ofReal`, `tilde` (over *positive*
reals only) and `top`. The tilde copy omitting `0` avoids a quotient and gives exactly one `0`
and one `∞` by construction. The summation: sum the underlying values as a `tsum` in `ℝ≥0∞` —
unconditional there, and order-independent, which is what the paper's "sum of the convergent
series" means for nonnegative terms — then mark the result with a tilde unless the family is
finitely supported with every entry plain.

The three `SumData` axioms: `sum_congr` is immediate (`tsum`, finiteness of support and plainness
are all invariant under reindexing); `sum_unique` is a case check on the single entry; `sum_sigma`
is where the work is. `tsum` over a sigma is `ENNReal.tsum_sigma`, so the *values* match; the
content is that the *marking* matches, i.e. that the double family is finitely supported with all
entries plain iff the family of row-sums is. Left to right is easy; right to left needs that a row
whose sum is plain and nonzero must itself be finitely supported and plain, which is the
definition of the summation read backwards. Prove that as a standalone lemma first.

The braiding classification is the analogue of Examples 3.3(1) with "same series sum, and supports
both finite or both infinite" in place of "both supports infinite"; the infinite case reuses the
alternating construction of `natBraidState`, with the domination step supplied by the tail of a
convergent series of positive terms rather than by entries being `≥ 1`. Then
`isBraidedOver_rtilde` packages it, and the paper's argument that `{0} ∪ ℝ̃>0` is *not*
`ℵ₀⁻`-braided over itself is a short direct computation.

`ℚ≥0` is the same construction restricted, with the observation that irrationals admit only
infinitely-supported representations, so only one copy of them appears. Do it only if you want
Examples 3.12 complete, and expect a light edit of `RTilde` rather than new mathematics.

## Suggested order

Only the `ℝ≥0` example is left; it is independent of everything else and the only remaining item
that needs a new `κ`-monoid built from scratch.
