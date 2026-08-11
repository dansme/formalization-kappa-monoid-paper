# Section 5 — implementation plan

*Realization to hereditary rings for two-generated `ℵ₀`-monoids.*

Companion to `KappaMonoid/Section5.lean`. Work through the steps in the order given; each is
independently checkable.

## Read this first

**The §4 blocker is gone.** Corollary 4.7(1) is proved (both directions, with axiom A5 for
(i) ⇒ (ii)), so Lemma 5.1 and Theorem 5.3 have their input. Steps 1 and 6's counterexample are
done, as are Lemma 5.2(1)(2), the trace ideals of step 5 and two claims of step 6;
10 `sorry`s remain.

**§5 is the most expensive section per result.** Unlike §§2–4, its proofs are explicit
combinatorial constructions — Lemma 5.2(3) writes down three interleaved partitions of `ℕ` by
hand — and Proposition 5.4 needs trace ideals, which Mathlib does not have. Budget accordingly:
steps 1–4 are comparable in size to all of §3.2, and step 5 is a small module-theory development
of its own.

## Ground rules

`CLAUDE.md` carries the conventions, the workflow and the elaboration traps. Specific to §5:

- `Section5.lean` is **not** imported by `KappaMonoid.lean`; build it with
  `lake build KappaMonoid.Section5`.
- §5 fixes `κ = ℵ₀` throughout. `KMonoid ℵ₀ H` is `LMonoid ℵ₁ H` plus `ℵ₀ ≤ ℵ₀`; index types are
  countable, so `ℕ` is the canonical index and `Idx ℵ₀ ≃ ℕ` — but index by `Nats := ULift.{u} ℕ`,
  see step 1.
- Trap 5 of `CLAUDE.md` (pin universes) is the reason for that `ULift`, and also for the section
  variable being `[KMonoid (ℵ₀ : Cardinal.{u}) H]`: with `ℵ₀`'s universe auto-bound, two
  occurrences of `eval` in one statement end up in *different* universes and cannot be combined.

## Step 1 — forms

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

## Step 3 — Lemma 5.2 (`easyfactlemma1`), five parts

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
- **(3)** the substantial one. `x_i ∈ add x_j` and no element has both a finite and an infinite
  form ⟹ `α X_i + ℵ₀ X_j` and `β X_i + ℵ₀ X_j` are braided, for all `α, β ≤ ℵ₀`. The paper gives
  the partitions explicitly — `I₀ = {0,…,α-1}`, `I_k = {α + n(k-1), …}`, `J_k = {nk, …}` with
  `u_k = α x_i`, `v_k = t`, `v_0 = 0` — so transcribe them. Expect this to be the longest proof
  in the section: it splits on `α` finite versus `α = ℵ₀`, and the second case re-derives
  `m x_j = (m'+1) x_i + n' x_j` before building its partitions.
- **(4)** `x_i ∉ add x_j`, no mixed forms, `m X_i + ℵ₀ X_j` braided with `n X_i + ℵ₀ X_j` ⟹
  `m x_i + k x_j = n x_i + k' x_j` for some finite `k, k'`.
- **(5)** `H` braided over `add (x₁ + x₂)` ⟹ (`x_i ∈ add x_j` ↔ `ℵ₀ (x₁ + x₂) = ℵ₀ x_j`). The
  forward direction is elementary: from `x₁ + z = n x₂` scale by `ℵ₀` (`cmul_top_distrib`,
  `ℵ₀·n = ℵ₀`, `α + α = α`), with the case `n = 0` closed by reducedness. The backward direction is
  where the work is, and the paper's "we conclude that there exist positive integers `m`, `n`" hides
  a block induction: braid the constant families `(x₂)` and `(x₁+x₂)` (same `ℵ₀`-sum by hypothesis),
  take the least level `k` in some block whose `I`-piece is nonempty, use reducedness to see that
  `u`, `v` vanish below it, so `v (a,k)` is a *finite multiple of* `x₂`, and read
  `x₁ ≼ m(x₁+x₂) = v(a,k) + u(a,k) ≼ (r + #J(a,k)) x₂` off the two braiding equations.

Do (5) next: it is used by both later steps.

## Step 4 — Theorem 5.3 (`hereditarycasecor`)

The main result: a non-cyclic two-generated `ℵ₀`-monoid is `V^{ℵ₀}(R)` for a hereditary `R` iff
(i) `n x_i + ℵ₀ x_j = ℵ₀ x_i + ℵ₀ x_j` with `n` finite implies `ℵ₀ x_j = ℵ₀ x_i + ℵ₀ x_j` and
`x_i ∈ add x_j`; (ii) if `x_i ∉ add x_j` and `m x_i + ℵ₀ x_j = n x_i + ℵ₀ x_j` then
`m x_i + k x_j = n x_i + k' x_j` for finite `k, k'`; (iii) no element has both a finite and an
infinite form.

Forward: Lemma 5.1 gives braidedness, then (iii) is 5.2(1), (ii) is 5.2(4), and (i) is the
counting argument — cofinitely many blocks sum to `|I_μ| x_j`, so `x_i ∈ add x_j`, then 5.2(3).

Backward: verify braidedness over `add (x₁ + x₂)` by the four-case split the paper lists
(`fin/fin`, `m,ℵ₀ / m',ℵ₀`, `ℵ₀,n / m,ℵ₀`, `m,ℵ₀ / ℵ₀,ℵ₀`), then apply Corollary 4.7(1).

State it with the two indices symmetric — the paper's `1 ≤ i ≠ j ≤ 2` is best rendered as a
hypothesis quantified over both orderings rather than as `Fin 2` bookkeeping, which would cost
more than it saves.

## Step 5 — trace ideals and Proposition 5.4 (7 sorries)

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

Proposition 5.4 itself is then the four-way equivalence plus its hereditary addendum. Note that
`ModuleClass` has no constructor taking a module to its class — only `rep` going the other way —
so `prop_5_4` is stated for carrier elements `p₁ p₂` with modules `rep p₁`, `rep p₂`. (iii) ⇒ (iv)
is Lemma 2.14 (`eq_cmul_top_of_add`, proved) and the final claim uses Lemma 5.1.

## Step 6 — Corollary 5.5 (`hereditarycase`), three parts

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
`TrivExt.coe_nsmul`, both added to `Examples.lean`. What is left in step 6 is the three
`corollary_5_5_*` statements themselves.

## Dependency order

```
step 1 (forms) ──> step 2 (Lem 5.1) ──> step 3 (Lem 5.2) ──> step 4 (Thm 5.3) ──> step 6 (Cor 5.5)
   done                                                                                 ▲
                                        step 5 (trace ideals, Prop 5.4) ────────────────┘
```

Step 5 is independent of steps 1–4 and can be done in parallel; it only meets the rest at 5.5(3).

## Status

10 `sorry`s in `KappaMonoid/Section5.lean`, all statements type-checked; the root `lake build`
stays green and `sorry`-free because the file is not imported by `KappaMonoid.lean`.

Closed so far, all without any axiom: `sumOf_familyOfForm` (step 1); Lemma 5.2(1)(2) (step 3); the
trace ideals `smul_traceIdeal_eq`, `traceIdeal_le_of_smul_eq`, `traceIdeal_mul_self` and
`traceIdeal_isTwoSided` (step 5); the counterexample block, `corollary_5_5_two_unique` and
`corollary_5_5_three_absorb` (step 6).

Still open (10): Lemma 5.1; Lemma 5.2(3)(4)(5); Theorem 5.3; Proposition 5.4 and its hereditary
addendum; Corollary 5.5(1)(2)(3). New reusable infrastructure, in the core files: `KMonoid.cmul_eq_sumOf`,
`KMonoid.sumOf_indicator`, `KMonoid.sumOf_eq_sumOf_subset`, `KMonoid.sumOf_sumType`,
`KMonoid.cmul_zero`, `KMonoid.cmul_cmul` (`Basic.lean`), `TrivExt.coe_nsmul`,
`TrivExt.cmul_top_eq_top` (`Examples.lean`), `KMonoid.self_mem_addOf` (`Section4.lean`).

## One thing to fix in the paper

Corollary 5.5(3) reads "The converse is not true.2" — a stray `2` after the full stop, at
`kappa_monoids.tex:2133`. Not a formalisation issue, but worth catching before submission.
