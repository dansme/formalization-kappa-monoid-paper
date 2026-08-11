# Completing Section 3

A work plan for the part of §3 of Nazemian–Smertnig that is not yet formalised.

Baseline: branch `simplify`. `lake build` is green and `sorry`-free; `KappaMonoid/Section32.lean`
is deliberately **not** imported by `KappaMonoid.lean`, so it does not affect that. Build it on
its own with `lake build KappaMonoid.Section32`.

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
| Lemma 3.13(2) (saturated submonoids, both cases) | `IsSaturated`, `lemma_3_13_sub` |
| Prop. 3.14, all the definitional work | `LinSystem`, `linEval`, `solutions`, `isKSubmonoid_solutions`, `mem_solutions_map`, `mem_solutions_of_incl`, `finSolutions`, `alephPart`, `alephExt`, `addSubmonoid_finSolutions`, `alephExt_subset_solutions`, `isKSubmonoid_alephExt` |

**Lemma 3.4(2)(3) and Lemma 3.5 are deliberately absent.** The `ι × ℕ` normal form for braiding
partitions *is* their content: a braiding breaks into a disjoint union of countable ones and
conversely, and the relation does not depend on the chosen limit well-order. Restating them
would mean reintroducing abstract limit well-orders purely to prove they do not matter. See the
README's "The limit well-order" note. Leave them alone unless you specifically want the
well-order independence as a theorem, in which case it is a project of its own and should be
scoped separately.

In `Universal.lean`:

| Paper | Where |
|---|---|
| Theorem 3.11 read as an equivalence (universal ⟹ braided over) | `IsBraidedOver.of_iso`, `isBraidedOver_of_isUniversalKExtension` |

## What is missing

Exactly two `sorry`s remain in `Section32.lean`: `prop_3_14_one` and `prop_3_14_two`. Beyond
that, §3 is missing Examples 3.3(2) — the `ℝ≥0` and `ℚ≥0` entries of Examples 3.12 — which is
independent of everything else and not scaffolded any more than sketched below.

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
6. When a `letI`-in-statement instance argument cannot be inferred from the goal, pass it
   explicitly (`Fcard.instKMonoid_add (le_refl (ℵ₀ : Cardinal.{u}))`); and `rw` will not unfold
   `KMonoid.ksum` to `KMonoid.sumOf`, so convert with `KMonoid.sumOf_Idx` (or `show`) before
   rewriting with the `sumOf` lemmas.

---

## Step A (mostly done) — "universal ⟹ braided", i.e. Theorem 3.11 as an equivalence

Both halves of Prop. 3.14 follow the paper by applying **Lemma 3.13(2)** (`lemma_3_13_sub`, now
proved) to a *known ambient braided extension*:

* 3.14(1): `X = F_{ℵ₀}^n`, `Ĥ = F_κ^n`, `λ = ℵ₁`, `S =` the `ℵ₀`-solutions;
* 3.14(2): `X = ℕ₀^n`, `Ĥ = F_{ℵ₀}^n`, `λ = ℵ₀`, `S = H`, which is saturated.

`lemma_3_13_sub` takes `IsBraidedOver lam κ X Ĥ hlk f` as its hypothesis, whereas what
`lemma_3_13_free` supplies for these `X ⊆ Ĥ` is `IsUniversalKExtension`. The paper gets back with
Theorem 3.11 plus uniqueness ("universal ⟹ braided", the remark after Def. 3.10 that the two
notions are equivalent), and **that is now available**:

* `UnivExt` and `theorem_3_11` were stated for `X : Type u`, which excluded
  `F_κ^n : Type (u+1)`; the construction never needed the restriction (it only ever indexes by
  `Idx κ : Type u`), so it is now stated for `X : Type v` with the extension in
  `Type (max u v)`;
* `IsBraidedOver.of_iso` transports braidedness along an isomorphism of the *extension* — a
  bijective `κ`-homomorphism commuting with the structure maps, which is exactly what
  `isUniversalKExtension_unique` hands you;
* `isBraidedOver_of_isUniversalKExtension` combines the two.

What is still missing on this route is the transport along an isomorphism of the *base*
(`g : X₁ ≃ X₂` a `λ⁻`-isomorphism; `BraidingData` transports by applying `g` to `u` and `v`),
needed because `lemma_3_13_free` is about `F_{λ⁻}(B) ⊆ F_κ(B)`, whose carriers are *subtypes* of
the products `B → LCard lam`, `B → Fcard κ`, whereas §3.2 works with the products themselves. For
`B = Fin n` the two are isomorphic — the support condition is vacuous for finite `B` — and both
isomorphisms are the subtype coercion, so this is a bijection whose compatibility with the sums is
`rfl`-level.

**Do not try to prove the two braidings by hand instead.** Both are genuinely `n`-component
constructions:

* for 3.14(1), two families in `F_{ℵ₀}^n` with equal `κ`-sums must be split into *countable*
  pieces with equal partial sums *in all `n` components at once*, and the components can blow up
  at different cardinalities, which forces a transfinite construction;
* for 3.14(2) the pieces are finite and the index set countable, so it is the `ℕ₀` argument of
  `isBraided_nat_of_infinite_support` with the deficit `v` a *vector*; the domination step then
  has to consume all remaining nonzero entries in the components whose total is finite while
  growing the blocks in the others.

Either is a project the size of the `ℕ₀` braiding was, and the first is larger. The Step A route
is cheaper and gives both.

## Step B — Prop. 3.14(1)

First assemble `IsBraidedOver ℵ₁ κ (F_{ℵ₀}^n) (F_κ^n)`: apply
`isBraidedOver_of_isUniversalKExtension` to `lemma_3_13_free` at `lam = ℵ₁`, `B = Fin n`
(reducedness is automatic for `λ > ℵ₀`, by `LMonoid.isConical`), then transport both sides from the
`FreeL`/`FreeK` subtypes to the products as described in Step A. Then:

1. `lemma_3_13_sub` (the `λ ≠ ℵ₀` branch) gives that `⟨H⟩_κ ⊆ F_κ^n` is the universal
   `κ`-extension of `H`, for `H` the `ℵ₀`-solution set. Its `IsLSubmonoid ℵ₁ H` hypothesis is
   `isKSubmonoid_solutions`: a `KMonoid ℵ₀` structure *is* an `LMonoid ℵ₁` structure, with the
   same sums.
2. What remains is the paper's generation statement: `⟨H⟩_κ =` the `κ`-solution set. One
   inclusion is `mem_solutions_map`; the other is the decomposition
   `α = β + Σ_{ℵ₀ ≤ λ ≤ κ} λ γ^{(λ)}`. Only *finitely many* levels are needed: take
   `Λ = {α_i : α_i ≥ ℵ₀}` (at most `n` cardinals), `β_i = min(α_i, ℵ₀)` and
   `γ^{(λ)}_i = ℵ₀` if `α_i ≥ λ`, else `0`. Each `γ^{(λ)}` and `β` is a solution by
   `mem_solutions_map`: both maps are additive on `F_κ` (for `λ` infinite, `a + b ≥ λ` iff
   `max(a,b) ≥ λ`), which is exactly the paper's observation that the construction does not look
   at the coefficients. The index set of the `κ`-sum can be taken to be
   `Option (Fin n × Idx κ)`, padding along `Idx λ ↪ Idx κ` for each level.
3. Finally transport `IsUniversalKExtension` from `↥⟨H⟩_κ` to `↥(solutions κ)` along the equality
   of the two sets.

## Step C — Prop. 3.14(2)

The ambient braiding here is `IsBraidedOver ℵ₀ ℵ₀ (ℕ₀^n) (F_{ℵ₀}^n)`, again from
`lemma_3_13_free` — at `lam = ℵ₀`, `κ = ℵ₀`, `B = Fin n`, where `F_{ℵ₀⁻}(Fin n) = ℕ₀^n` — plus
`isBraidedOver_of_isUniversalKExtension`. Note that at `λ = ℵ₀` reducedness is *not* automatic and
has to be supplied: `ℕ₀^n` is reduced.

Then the same shape as Step B, and shorter, because everything else is done: `H = finSolutions` is
saturated in
`ℕ₀^n` (cancellativity — this still has to be proved, it is the paper's remark before
Prop. 3.14), `alephExt = ⟨H⟩_{ℵ₀}` needs `isKSubmonoid_alephExt` (proved) for one inclusion and
the paper's finite-`J` argument for the other — which is precisely the argument already carried
out inside `ksum_mem_alephExt`, so extract it rather than redo it.

## Step D — Example 3.15 and Remark 3.16

Example 3.15 (`H = {(n,n)} ⊆ ℕ₀²`, whose universal `ℵ₀`-extension is *not* the solution set of
the same equations over `F_{ℵ₀}`) is the sharpness witness for 3.14(1) and (2) being different
statements. `example_3_15` in the scaffold is a placeholder `True`; state it properly with
`finSolutions` and `alephExt` once Step C is done.

Remark 3.16 (saturated submonoids of `ℕ₀^n` are finitely generated reduced Krull monoids, citing
the literature) is a pointer, not a theorem. Either skip it or record it in the README.

## Step E — Examples 3.3(2): the `ℝ≥0` example

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

Step A is done except for the base-side transport; do that, then Step B → Step C → Step D. Step E
any time — it is independent of all of them.
