# Section 5 — implementation plan

*Realization to hereditary rings for two-generated `ℵ₀`-monoids.*

Companion to `KappaMonoid/Section5/`; a record of the work, now finished.

## Read this first

**Section 5 is complete.** Every lemma, theorem, proposition and corollary is stated and proved,
`sorry`-free, and `KappaMonoid/Section5/` is imported by `KappaMonoid.lean`. Theorem 5.3 and
Corollary 5.5 use no axiom beyond A5, which enters through Corollary 4.7(1); Proposition 5.4 and
its hereditary half use none at all.

This document is kept as the record of how each step went and of the six statements that had to be
corrected on the way; `README.md` carries the corrections in their user-facing form under "The
statements corrected in Section 5".

**§5 is the most expensive section per result**, as predicted: its proofs are explicit
combinatorial constructions, and two of them — Lemma 5.2(3)'s partitions and the reduction of an
arbitrary family to a form family inside Theorem 5.3 — are the longest in the development.

## Ground rules

`CLAUDE.md` carries the conventions, the workflow and the elaboration traps. Specific to §5:

- §5 fixes `κ = ℵ₀` throughout. `KMonoid ℵ₀ H` is `LMonoid ℵ₁ H` plus `ℵ₀ ≤ ℵ₀`; index types are
  countable, so `ℕ` is the canonical index and `Idx ℵ₀ ≃ ℕ` — but index by `Nats := ULift.{u} ℕ`,
  see step 1.
- Trap 5 of `CLAUDE.md` (pin universes) is the reason for that `ULift`, and also for the section
  variable being `[KMonoid (ℵ₀ : Cardinal.{u}) H]`: with `ℵ₀`'s universe auto-bound, two
  occurrences of `eval` in one statement end up in *different* universes and cannot be combined.

## Step 1 — forms — **done**

The whole section is written in terms of *forms* `α X₁ + β X₂` with `0 ≤ α, β ≤ ℵ₀`. Encode a
coefficient as `ℕ∞ = WithTop ℕ`, whose elements are exactly `0, 1, 2, …, ℵ₀`, and push it into
`Cardinal` with Mathlib's `Cardinal.ofENat`. This is the one real encoding decision in §5 and it
makes `α` decidably finite-or-not, which every proof in the section branches on.

```lean
/-- A **form** `α X₁ + β X₂`: a pair of coefficients in `{0, 1, 2, …, ℵ₀}`. -/
abbrev Form : Type := ℕ∞ × ℕ∞

/-- `ℵ₀`-many copies of `x`, or `n` copies for finite `n`. -/
noncomputable def ecmul (a : ℕ∞) (x : H) : H :=
  KMonoid.cmul (κ := ℵ₀) (Cardinal.ofENat a) (Cardinal.ofENat_le_aleph0 a) x

/-- The element of `H` represented by a form. -/
noncomputable def eval (x₁ x₂ : H) (F : Form) : H := ecmul F.1 x₁ + ecmul F.2 x₂

/-- A form is *infinite* if either coefficient is. -/
def Form.IsInfinite (F : Form) : Prop := F.1 = ⊤ ∨ F.2 = ⊤
```

All of this is in the scaffold already, along with `HasFiniteForm`, `HasInfiniteForm`,
`NoMixedForms` and `BraidedForms`. `sumOf_familyOfForm` is **proved**, but the encoding had to be
corrected first:

- **The index type is `FormIdx := Nats ⊕ Nats`**, one copy of `ℕ` for the `X₁` slots and one for the
  `X₂` slots (`Nats := ULift.{u} ℕ`, because `BraidingData` indexes by a type in the cardinal's
  universe). The scaffold instead listed the `α` copies of `x₁` and then the `β` copies of `x₂`
  inside a single copy of `ℕ`, which is **wrong for `α = ℵ₀`**: no slot is left for `x₂`, and
  `sumOf_familyOfForm` is then false — in `H = F_{ℵ₀}` with `x₁ = 0`, `x₂ = 1`, `F = (ℵ₀, 1)` the
  family is identically `0` while the form evaluates to `1`. With two summands the sum splits by
  `sumOf_sumType` and each slot still carries a single generator, as in the paper.
- The sum of the `X₁`-slots is `#{n : ℕ | n < α}` copies of `x₁`, and `mk_slots` computes that
  cardinal to be `α` (`ℵ₀` when `α = ℵ₀`). `sumOf_indicator` in `Basic.lean` turns a family that is
  `x` on a set and `0` off it into `#S · x`.

`BraidedForms` being an equivalence relation comes free from `braidingSetoid`.

## Step 2 — Lemma 5.1 (`l:twogen-braided`)

If `H ≅ V^{ℵ₀}(R)` for a ring whose projectives are direct sums of f.g. modules, then `x₁` and
`x₂` are classes of f.g. modules, `H` is braided over `add (x₁ + x₂)`, and
`V(R) ≅ add (x₁ + x₂) = ⟨x₁, x₂⟩`.

Direct from `corollary_4_5_three` plus `corollary_4_7_one_backward`. The one step needing care is
the paper's parenthetical: *both* `P₁` and `P₂` must appear as summands of f.g. modules, else
`V(R)` would be cyclic and hence so would `V^{ℵ₀}(R)` — that uses `KGenerates` and the
non-cyclicity hypothesis, and is where `H` being non-cyclic first bites.

## Step 3 — Lemma 5.2 (`easyfactlemma1`), five parts — **done**

- **(1) — done**, and it needed a **correction**: the scaffold omitted the non-degeneracy
  hypotheses, and with `x₁ = 0` the infinite form `(ℵ₀, 0)` has the identically zero family, which
  *is* braided with the finite form `(0, 0)`. `lemma_5_2_one` now takes `x₁ ≠ 0`, `x₂ ≠ 0`, which
  `ne_zero_of_not_cyclic` supplies from §5's standing hypotheses (a zero generator could be
  dropped, making `H` cyclic). The proof is not the paper's cofinite-blocks argument but
  `IsBraided.mk_support_lt` (the converse of Lemma 3.4(1), already proved): a partner of a
  finite-support family has finite support, and an infinite form's family has infinite support.
- **(2) — done**, from `isBraided_of_small_sets` (`Universal.lean`): both families are supported on
  the finitely many slots of their forms and have the same sum there. `coe_lsumOf_slots` is the
  bookkeeping — the coercion of a submonoid sum is the sum in `H` (`IsLSubset.coe_lsumOf` is `rfl`),
  and dropping the slots off which the family vanishes is `sumOf_eq_sumOf_subset`.
- **(3) — done**, and it was the longest proof in the section, as expected. The partitions are not
  transcribed as sets but as **level functions**: `IsBraided.of_levels` (new, in `Braiding.lean`)
  builds a `BraidingData ℵ₀` from two maps `ι → ℕ` with finite fibres, parking all the action on a
  single `ω`-chain of `ι × ℕ`. Fibres are disjoint and cover for free, so only finiteness and the
  two block equations remain — exactly what the paper's hand-written partitions supply.
  `of_partition` is the special case `v ≡ 0`.

  For `α = A` finite, `A x₁ + t = n x₂` with `n ≥ 1` gives the levels
  `(j ↦ if j < A then 0 else j - A + 1) ⊕ (j ↦ j / n + 1)` against `(j ↦ j) ⊕ (j ↦ j / n)`, with
  `u ≡ A x₁`, `v 0 = 0`, `v (k+1) = t`. For `α = ℵ₀` one re-derives `m x₂ = (m'+1) x₁ + n' x₂` and
  the block sums already agree, so `v ≡ 0`. The lemma itself is then symmetry and transitivity
  through `β = 0`, as in the paper.

  **This corrects the scaffold**: `lemma_5_2_three` now takes the generation hypothesis `hgen`. It
  is a standing assumption of §5 and the `α = ℵ₀` case genuinely needs it — that is where
  `t = m' x₁ + n' x₂` comes from, and with `NoMixedForms` that `m'`, `n'` are finite.

  The supporting machinery is in `Section5.lean`: fibre splitting and counting on `FormIdx`
  (`fiber_elim`, `finsum_fiber_const`, `ncard_nats_div`, …), `coe_finsum_mem` for computing a
  submonoid `finsum` in `H`, and `addOf_add_mem` / `addOf_nsmul_mem`.
- **(4) — done**, and it also needed the generation hypothesis `hgen` added to the scaffold's
  statement. The paper cuts its single well-order at one ordinal `α`; `BraidingData` has countably
  many `ω`-chains instead, so the cut becomes a **rectangle**: choose a finite set `A` of chains and
  a level `K` with every one of the finitely many `x_i`-slots of either family inside some
  `I (a,k)` resp. `J (a,k)`, `a ∈ A`, `k ≤ K`. `BraidingData.telescope` (new, in `Braiding.lean` —
  the `λ = ℵ₀` counterpart of `block_lsumOf_eq`) then gives
  `n x_i + q x_j = m x_i + p x_j + Σ_{a ∈ A} v (a, K+1)`, each rectangle being a finite set of slots
  containing all the `x_i`-slots of its family (`exists_block_value`). Finally `I (a, K+1)` holds no
  `x_i`-slot, so `v (a,K+1) + u (a,K+1)` is a finite multiple of `x_j`; hence `v (a,K+1) ∈ add x_j`,
  its form has zero `X_i`-coefficient (`x_i ∉ add x_j`) and finite `X_j`-coefficient
  (`NoMixedForms`).
- **(5) — done**. The forward direction is `cmul_top_absorb`. The backward direction is where the
  work is, and the paper's "we conclude that there exist positive integers `m`, `n`" hides a block
  induction, which the formal proof runs explicitly: braid the constant families `(x₁+x₂)` and
  `(x₂)` (same `ℵ₀`-sum by hypothesis), take the least level `k` of a block whose `I`-piece is
  nonempty, use reducedness to see that `u`, `v` vanish below it, so `v (a,k)` is a *finite multiple
  of* `x₂`, and read `x₁ ≼ m(x₁+x₂) = v(a,k) + u(a,k) ≼ (r + #J(a,k)) x₂` off the two braiding
  equations. `ksum_const` and `sumOf_const_finite` came out of it.

Step 3 is complete, and feeds Theorem 5.3.

## Step 4 — Theorem 5.3 (`hereditarycasecor`) — **done**

The main result, in both directions, with the two indices symmetric (`Cond1 x₁ x₂ ∧ Cond1 x₂ x₁ ∧
…`) rather than as `Fin 2` bookkeeping.

**The statement carries `EveryProjectiveIsSumOfFG R` alongside hereditariness.** The paper reaches
that from Corollary 4.6, a quoted result which this development bundles into axiom A5 rather than
derives, so it is not recoverable from `∀ I, Module.Projective R I` here. Both sides of the
equivalence carry it; for a hereditary ring it is automatic. `corollary_4_7_one_forward` now returns
it (`bd.sumOfFG`). Documented in `README.md` under "The hypothesis added to Theorem 5.3".

**Forward** (`theorem_5_3_forward`): Lemma 5.1 gives the braiding, (iii) is 5.2(1), (ii) is 5.2(4),
and (i) is `cond1_of_braidedOver`, whose counting step `mem_addOf_of_braidedForms_top` is the
paper's "all but finitely many blocks sum to `|I_μ| x_j`". Only finitely many `I`-blocks meet the
`x₁`-slots of the finite form, but infinitely many `J`-blocks meet those of `ℵ₀X₁ + ℵ₀X₂`, so some
`p` has `x₁` inside `J p` while neither `I p` nor `I (p+1)` meets an `x₁`-slot, and
`x₁ ≼ v(p+1) + u p ≼ (r + r') x₂`.

**Backward** (`theorem_5_3_backward`): two separate pieces.

- `braidedForms_of_conditions` is the paper's four-case split, on *forms*: both finite (5.2(2));
  both `_ X₁ + ℵ₀ X₂` (5.2(3) if `x₁ ∈ add x₂`, else both `X₁`-coefficients are finite and (ii)
  gives the finite relation, which `braidedForms_of_finite_relation` turns into a braiding); the
  mixed case `α X₁ + ℵ₀ X₂` against `ℵ₀ X₁ + n X₂` (braid both with `ℵ₀X₁ + ℵ₀X₂`); and both
  `ℵ₀ X₁ + _ X₂`, which is the second case with the generators swapped (`braidedForms_swap`).
- `exists_braided_form` is the step the paper compresses into "hence `add(x₁+x₂) = ⟨x₁,x₂⟩`": an
  *arbitrary* family over `add (x₁ + x₂)` is braided with a form family. Each member has a finite
  form (`exists_finite_form_of_mem`, from (iii)), and `blockIdx` cuts the slots of the total form
  into consecutive blocks of `c k` copies of `x₁` and `d k` of `x₂` while the family is cut into
  singletons, so `IsBraided.of_levels` applies with `v ≡ 0`.

The two meet through `IsBraided.comp_equiv`, which moves a braiding between the index types
`FormIdx` and `Idx ℵ₀`, and Lemma 3.2, which turns equality of the families' sums into equality of
the two forms' values.

## Step 5 — trace ideals and Proposition 5.4 — **done**

**Mathlib has no trace ideal** — there is no `traceIdeal`, and `Module.trace` is the trace of an
endomorphism, unrelated. The scaffold defines it and states the three facts to prove. These are
**formalised, not assumed**: unlike Bergman–Dicks (A5) or Leavitt (A2) they are elementary, so
assuming them would be assuming the inconvenient rather than the out-of-reach.

**The three lemmas are done**, with one addition to the scaffold: `Ideal R` in Mathlib is a *left*
ideal, and `I • (⊤ : Submodule R R) ≤ I` — the inclusion both `traceIdeal_le_of_smul_eq` and
`traceIdeal_mul_self` rest on — is false for a one-sided ideal. So `traceIdeal_isTwoSided` is proved
first (right multiplication by `r` is left-`R`-linear, so `f (·) * r` is again a functional) and
`traceIdeal_le_of_smul_eq` takes `[I.IsTwoSided]`. What remains of step 5 is Proposition 5.4
itself.

```lean
noncomputable def traceIdeal : Ideal R := ⨆ f : P →ₗ[R] R, LinearMap.range f
```

The three lemmas, with their proofs — all short given `Module.projective_def`:

1. `smul_traceIdeal_eq : Tr(P) • ⊤ = ⊤` for projective `P`. `Module.projective_def` gives
   `s : P →ₗ[R] P →₀ R` splitting `Finsupp.linearCombination R id`, so
   `x = Σ_{p ∈ supp (s x)} (s x) p • p`. Each coefficient map `x ↦ (s x) p` is the functional
   `Finsupp.lapply p ∘ₗ s`, hence lands in `Tr(P)`; so `x ∈ Tr(P) • ⊤`.
2. `traceIdeal_le_of_smul_eq : I • ⊤ = ⊤ → Tr(P) ≤ I`. For any `f : P →ₗ[R] R`,
   `im f = f (I • ⊤) = I * im f ⊆ I`.
3. `traceIdeal_mul_self : Tr(P) * Tr(P) = Tr(P)`. From 1, `im f = f (Tr(P) • ⊤) = Tr(P) * im f`,
   so `Tr(P) ≤ Tr(P) * Tr(P)`; the reverse is `Ideal.mul_le_left`.

`Ideal` multiplication is available for noncommutative rings, so (3) states as written.

Proposition 5.4 itself needed four more trace-ideal facts — `traceIdeal_of_iso`, `traceIdeal_self`,
`traceIdeal_le_of_prod` and `traceIdeal_dsum_le` — and the extraction of a finite subfamily of
functionals from `Tr(P) = R` (`exists_sum_eq_one_of_traceIdeal_eq_top`, proved by exhibiting the
finite sums as an ideal).  (i) ⇒ (ii) replaces the paper's `P₂ Tr(P₁) = P₂` by the observation that
the classes whose trace ideal fits inside `I` form a `κ`-submonoid, so `[R]` — an `ℵ₀`-sum of copies
of the generators — lands in it.  (ii) ⇒ (iii) is the epimorphism `P₁ⁿ ↠ R`, split because `R` is
projective; the resulting idempotent cuts `P₁ⁿ` into `R` and a complement, both classes since
`V^{ℵ₀}(R)` is closed under summands.  The hereditary half needs two further lemmas:
`mem_of_divisorClosed_of_generates` (the paper's parenthetical from Lemma 5.1, now shared with it)
and `eq_zero_of_finite_cmul_top` (`ℵ₀` copies of a nonzero class are never finitely generated).

## Step 6 — Corollary 5.5 (`hereditarycase`), three parts — **done**

Case analysis on how `add x₁` and `add x₂` compare — incomparable, equal, or `add x₁ ⊊ add x₂` —
each giving an equivalence between realizability and an explicit relation condition. All three are
bookkeeping on top of Theorem 5.3, plus Proposition 5.4 for part (3)'s trace formulation.

Two of the parts assert **"the converse is not true"** with the same witness: `H := ℕ₀² ∪ {∞}`,
the trivial `ℵ₀`-extension of `ℕ₀²` with `x₁ = (1,0)`, `x₂ = (0,1)`. That is Example 2.3(1),
already formalised as `TrivExt.instKMonoid` in `KappaMonoid/Examples.lean`, so the scaffold builds
`H` outright and leaves only `cex_incomparable`, `cex_absorb` and `cex_unique_infinite` open.

**Done** — and they paid for themselves: they are what exposed the encoding error in step 1.
`corollary_5_5_two_unique` and `corollary_5_5_three_absorb` are proved too, both from
`cmul_top_absorb`: if `x₁ ∈ add x₂` then `ℵ₀ x₂` absorbs any number of copies of `x₁`
(`β x₁ ≼ ℵ₀ x₁ ≼ ℵ₀ (n x₂) = ℵ₀ x₂`, then Lemma 2.8(2)). Neither needs the generation hypothesis,
which is why both carry it as `_hgen`.
`isConical_natSq`, `cex_incomparable`, `cex_absorb` and `cex_unique_infinite` are proved, on
`TrivExt.cmul_top_eq_top` (`ℵ₀` copies of a nonzero element of a trivial extension are `∞`) and
`TrivExt.coe_nsmul`, both added to `Section2/Examples.lean`.

The three `corollary_5_5_*` statements are proved.  (1) is pure monoid theory on top of Theorem 5.3.
(2) and (3) go through Proposition 5.4: for (2), each generator lying in `add` of the other makes
both trace ideals `R`, and the hereditary half then gives freeness; for (3), Theorem 5.3(i) for the
ordered pair `(x₂, x₁)` is what forces `β` finite.  Helpers introduced here: `map_cmul_of_isKHom`,
`addOf_subset_of_mem`, `rep_cmul_top_dsum`, `traceIdeal_eq_top_of_addLe` and
`cmul_top_eq_unitClass_of_free`.

## Dependency order

```
step 1 (forms) ──> step 2 (Lem 5.1) ──> step 3 (Lem 5.2) ──> step 4 (Thm 5.3) ──> step 6 (Cor 5.5)
   done                done                  done               done                done ▲
                                     step 5 (trace ideals, Prop 5.4) — done ──────────────┘
```

Step 5 is independent of steps 1–4 and can be done in parallel; it only meets the rest at 5.5(3).

## Status

No `sorry`s; `KappaMonoid/Section5/` is part of the root target.

Everything is closed with no axiom beyond the A5 already inside Corollary 4.7(1), which
Theorem 5.3 and Corollary 5.5 inherit; `sumOf_familyOfForm`, `exists_form`, all of Lemma 5.2, the
trace ideals and **Proposition 5.4** (both halves) are axiom-free.

New reusable infrastructure in the core files: `KMonoid.cmul_eq_sumOf`, `KMonoid.sumOf_indicator`,
`KMonoid.sumOf_eq_sumOf_subset`, `KMonoid.sumOf_sumType`, `KMonoid.cmul_zero`, `KMonoid.cmul_cmul`,
`KMonoid.IsKHom.map_add`, `KMonoid.IsKHom.inv` (`Basic.lean`), `IsBraided.of_levels`,
`IsBraided.comp_equiv` and `BraidingData.telescope` (`Braiding.lean`),
`IsBraidedOver.of_kIso_subset` (`Universal.lean`), `TrivExt.coe_nsmul`, `TrivExt.cmul_top_eq_top`
(`Section2/Examples.lean`), `KMonoid.self_mem_addOf` (`Section4/AddOf.lean`).  `corollary_4_7_one_forward`
(`Section4/AddOf.lean`) now also returns `EveryProjectiveIsSumOfFG R`.

### The six corrected statements

All are documented in the docstring of the affected result and in `README.md`.

1. **Lemma 5.2(1)** needs `x₁ ≠ 0`, `x₂ ≠ 0`; with `x₁ = 0` the infinite form `(ℵ₀, 0)` is braided
   with the finite form `(0, 0)`.  `ne_zero_of_not_cyclic` supplies them.
2. **Lemma 5.2(3)** and 3. **Lemma 5.2(4)** take the generation hypothesis `hgen`, a standing
   assumption of §5 that both proofs need.
4. **Theorem 5.3**, **Proposition 5.4**'s hereditary half and all of **Corollary 5.5** carry
   `EveryProjectiveIsSumOfFG R` alongside hereditariness, because Corollary 4.6 is quoted here
   rather than formalised.
5. **Corollary 5.5(1)**'s condition is quantified over both orderings of the generators, as the
   paper's `1 ≤ i ≠ j ≤ 2` requires; the scaffold kept one instance of each clause and both are
   needed.
6. **Proposition 5.4**'s hereditary half and **Corollary 5.5(2)** quantify their freeness clause
   over the classes of `V^{ℵ₀}(R)` — the countably generated projectives — and not over all
   projective modules, for which it is false (`R^{(ℵ₁)}`, by axiom A1).

### What is not formalised

Corollary 5.5(3) is stated, and proved, as the equivalence between the relation condition and plain
realizability.  The paper's part (3) is a *three*-way equivalence: it also records that `R` may be
taken with a finitely generated projective `P` whose `P^{(ℵ₀)}` is not free, and that this is the
same as `Tr(P₁) ⊊ Tr(P₂)`.  Both extra clauses would need one more module-theoretic step — that a
finitely generated summand of `P^{(ℵ₀)}` is already a summand of some `P^n` — which is the same
`ℵ₀⁻`-smallness argument as `eq_zero_of_finite_cmul_top` and would be the natural next addition.

## One thing to fix in the paper

Corollary 5.5(3) reads "The converse is not true.2" — a stray `2` after the full stop, at
`kappa_monoids.tex:2133`. Not a formalisation issue, but worth catching before submission.
