# Completing Section 3

A work plan for the part of §3 of Nazemian–Smertnig that is not yet formalised.

Baseline: branch `simplify`. `lake build` is green and `sorry`-free; the scaffold
`KappaMonoid/Section32.lean` is deliberately **not** imported by `KappaMonoid.lean`, so it does
not affect that. Build it on its own with `lake build KappaMonoid.Section32`.

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

**Lemma 3.4(2)(3) and Lemma 3.5 are deliberately absent.** The `ι × ℕ` normal form for braiding
partitions *is* their content: a braiding breaks into a disjoint union of countable ones and
conversely, and the relation does not depend on the chosen limit well-order. Restating them
would mean reintroducing abstract limit well-orders purely to prove they do not matter. See the
README's "The limit well-order" note. Leave them alone unless you specifically want the
well-order independence as a theorem, in which case it is a project of its own and should be
scoped separately.

## What is missing

1. **Examples 3.3** — braiding in `ℕ₀`, `ℝ≥0`, `ℚ≥0`.
2. **§3.2 in full** — Examples 3.12, Lemma 3.13, Prop. 3.14, Example 3.15, Remark 3.16.

`KappaMonoid/Section32.lean` fixes the statements for the tractable part of both. Everything in
it is `sorry`; the statements elaborate, so they are known to be well-formed.

---

## Ground rules

Same as the rest of the development:

1. **One step = one commit**, with `lake build` green before each. While `Section32.lean` still
   has `sorry`s, keep it out of `KappaMonoid.lean`; add the import in the commit that removes the
   last one, so the root build is always `sorry`-free.
2. **Prove at the λ⁻ level and specialise to κ** where the statement allows it.
3. **House style**: index types in `Type u`, carriers in `Type v`; docstrings open with the bold
   paper reference; defs producing instances carry `@[instance_reducible]`.
4. **No new axioms** without asking. §3 should need none — the four in `KappaMonoid/Axioms.lean`
   are for §2.3 and Example 2.13 only, and nothing in §3 depends on them.
5. **Watch instance resolution on coercions.** Two traps cost real time in §2 and will recur:
   a plain `def` is not reducible, so `(freeClass …).carrier` does not unify with `Carrier` during
   instance search — state lemmas at the type instance search expects; and a double coercion like
   `↥↑m` can defeat synthesis outright — state such lemmas over a plain type variable and
   specialise.

---

## Step 1 — Examples 3.3(1): braiding in `ℕ₀`

Scaffold: `isBraided_nat_of_finite_support`, `isBraided_nat_of_infinite_support`,
`isBraidedOver_withTop_nat`.

The finite-support case is `isBraided_of_small_support` after matching `∑ᶠ` with `lsumOf`
(`LMonoid.lsumOf_eq_finsum` is the bridge).

The infinite-support case is the real content and is the paper's inductive construction. In the
`ι × ℕ` normal form you must produce a `BraidingData ℵ₀ x y`: partitions `I`, `J : ι × ℕ → Set ι`
into finite pieces, and families `u`, `v`. Build them by recursion on the second coordinate,
alternating: having consumed initial segments of both supports, take the next block of `x` large
enough that its sum is `≥` the current deficit, then the next block of `y` likewise. Every entry
of an infinitely-supported family in `ℕ₀` is eventually `≥ 1` infinitely often, which is what
makes the domination step always possible. Expect this to be the longest step; it is a
self-contained combinatorial argument with no dependencies.

`isBraidedOver_withTop_nat` then packages it: `IsBraidedOver` also needs that `ℕ₀` generates
`ℕ₀ ∪ {∞}` as an `ℵ₀`-monoid and that equal sums imply braided, both of which fall out of the two
classification lemmas plus the description of `TrivExt`'s summation.

**Payoff.** With Theorem 3.11(2) this gives the first entry of Examples 3.12: `ℕ̂₀ ≅ ℕ₀ ∪ {∞}`.

## Step 2 — Lemma 3.13(1): free objects

Scaffold: `freeIncl`, `lemma_3_13_free`.

`freeIncl`'s `sorry` is the support bound: a set of size `< λ` has size `≤ κ` (`hlk` plus
`Order.lt_succ_iff`). The theorem is then a matter of matching two universal properties: the
`λ⁻`-universal property of `F_{λ⁻}(B)` (`exists_unique_lift`) against the `κ`-universal property
of `F_κ(B)` (the same lemma at `λ = κ⁺`). Given `φ : F_{λ⁻}(B) → K` a `λ⁻`-homomorphism into a
`κ`-monoid, the extension is `lift (φ ∘ ι)`, and uniqueness is `hom_ext`. This step is short and
is the right one to do first if you want a quick win.

## Step 3 — Lemma 3.13(2): saturated submonoids

Scaffold: `IsSaturated`, `lemma_3_13_sub`.

Reduce to showing `⟨S⟩_κ` is `λ⁻`-braided over `S`, then apply
`IsBraidedOver.isUniversalKExtension`. The braiding families `u`, `v` come from a braiding in
`Ĥ`; the work is to see they lie in `S`.

* `λ ≠ ℵ₀`: `isBraided_iff_of_ne_aleph0` lets you take `v ≡ 0`, so each `u_μ` is a partial sum of
  elements of `S` and hence in `S`.
* `λ = ℵ₀`, `S` saturated: induct along the block. At `(a, 0)` (the limit elements of the normal
  form) `v = 0` and `u` is a partial sum, so both are in `S`. For the step, `u_{μ} + v_{μ}` and
  `u_{μ} + v_{μ+1}` are partial sums of the two families, hence in `S`, and saturatedness moves
  `u_{μ}` and then `v_{μ+1}` into `S`.

The `ι × ℕ` form makes this induction an ordinary `Nat.rec` on the second coordinate, which is
the main reason to expect it to be easier here than on paper.

## Step 4 — Proposition 3.14

Scaffold: `LinSystem`, `linEval`, `LinSystem.solutions`, `isKSubmonoid_solutions`,
`fcardIncl`, `mem_solutions_of_incl`, `prop_3_14_one`, `prop_3_14_two`.

Order of work:

1. `isKSubmonoid_solutions` — each of the three conditions is preserved by `κ`-sums. Equations
   and inequalities need that `linEval` commutes with `κ`-sums, which is Lemma 2.7(2)/(3) plus
   `KMonoid.pi_sumOf`; congruences need that a `κ`-sum of multiples of `d` is a multiple of `d`,
   using `cmul_sumOf_cardinal`.
2. `mem_solutions_of_incl` — the inclusion `F_{ℵ₀} ↪ F_κ` preserves each condition. Note this is
   *not* automatic for inequalities: `AddLe` is an existential, and the witness has to be
   transported. Cardinal arithmetic below `ℵ₀` is absolute, so the witness can be taken to be the
   image of the old one.
3. `prop_3_14_one` — show the `κ`-solutions are `ℵ₁⁻`-braided over the `ℵ₀`-solutions, then apply
   `IsBraidedOver.isUniversalKExtension`. Two families of `ℵ₀`-solutions with the same `κ`-sum
   are braided because `λ = ℵ₁ ≠ ℵ₀`, so `isBraided_iff_of_ne_aleph0` reduces it to matching
   partial sums, which can be read off coordinatewise in `F_κ^n`.
4. `prop_3_14_two` — the `λ = ℵ₀` case, and the one that genuinely differs: the extension is
   `H + ℵ₀H`, not the solution set of the same system over `F_{ℵ₀}`. Now stated in full:
   `finSolutions` is `H ⊆ ℕ₀^n` (the solutions with all components finite), `alephPart` is the
   paper's "replace every nonzero component by `ℵ₀`", and `alephExt` is `H + ℵ₀H`. Prove in the
   order `addSubmonoid_finSolutions` → `alephExt_subset_solutions` → `isKSubmonoid_alephExt` →
   `prop_3_14_two`. The interesting one is `isKSubmonoid_alephExt`: in each component a countable
   sum either has finitely many nonzero contributions, and is again of that shape, or infinitely
   many, and the component is `ℵ₀` and is absorbed into the `ℵ₀H` part.

Prop. 3.14 is the largest item and the one where the statement, not the proof, carries most of
the risk. Do not start proving until `isKSubmonoid_solutions` and `mem_solutions_of_incl` have
convinced you the definitions are right.

## Step 5 — Examples 3.3(2): the `ℝ≥0` example

Scaffold: `RTilde`, `RTilde.val`, `RTilde.rsum`, `RTilde.sumData`, `RTilde.instKMonoid`,
`isBraided_nnreal_iff`, `isBraidedOver_rtilde`, `not_isBraidedOver_rtilde_self`.

The carrier encoding is settled: an inductive with `ofReal`, `tilde` (over *positive* reals only)
and `top`. The tilde copy omitting `0` is what avoids a quotient, and gives exactly one `0` and
one `∞` by construction. The summation `rsum` is also settled: sum the underlying values as a
`tsum` in `ℝ≥0∞` — unconditional there, and order-independent, which is what the paper's "sum of
the convergent series" means for nonnegative terms — then mark the result with a tilde unless the
family is finitely supported with every entry plain.

What is left is the three `SumData` axioms and the braiding classification.

* `sum_congr` is immediate: `tsum`, finiteness of support and plainness are all invariant under
  reindexing.
* `sum_unique` is a case check on the single entry.
* `sum_sigma` is the fiddly one, and is where all the work is. `tsum` over a sigma is
  `ENNReal.tsum_sigma`, so the *values* match; the content is that the *marking* matches, i.e.
  that the double family is finitely supported with all entries plain iff the family of row-sums
  is. Left to right is easy. Right to left needs: a row whose sum is plain and nonzero must
  itself be finitely supported and plain, which is exactly the definition of `rsum` read
  backwards. Do this as a standalone lemma about `rsum` before touching `sum_sigma`.

`isBraided_nnreal_iff` is the analogue of step 1 with "same series sum, and supports both finite
or both infinite" in place of "both supports infinite"; the infinite case reuses the same
alternating construction, with the domination step supplied by the tail of a convergent series of
positive terms rather than by entries being `≥ 1`. `isBraidedOver_rtilde` then packages it, and
`not_isBraidedOver_rtilde_self` repeats the paper's argument inside `{0} ∪ ℝ̃>0`.

`ℚ≥0` is the same construction restricted, with the observation that irrationals admit only
infinitely-supported representations, so only one copy of them appears. It is not scaffolded; do
it only if you want Examples 3.12 complete, and expect it to be a light edit of `RTilde` rather
than new mathematics.

## Step 6 — Example 3.15 and Remark 3.16

Example 3.15 (`H = {(n,n)} ⊆ ℕ₀²`, whose universal `ℵ₀`-extension is *not* the solution set of the
same equations over `F_{ℵ₀}`) is the sharpness witness for 3.14(1) and (2) being different
statements. `example_3_15` in the scaffold is a placeholder `True`: state it properly once step 4
is done, when `finSolutions` and `alephExt` are available to phrase it with.

Remark 3.16 (saturated submonoids of `ℕ₀^n` are finitely generated reduced Krull monoids, citing
the literature) is a pointer, not a theorem. Either skip it or record it in the README.

## Suggested order

Step 2 (short, self-contained) → step 4.1–4.2 (fixes the §3.2 definitions) → step 1 (long but
independent) → step 3 → step 4.3–4.4 → step 5 → step 6.

Steps 1 and 2 are independent of everything else and can be done in either order. Step 3 depends
on nothing but the existing §3 API. Step 5 is the only one that needs a new `κ`-monoid built from
scratch, and nothing else depends on it.
