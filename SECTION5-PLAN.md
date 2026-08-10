# Section 5 — implementation plan

*Realization to hereditary rings for two-generated `ℵ₀`-monoids.*

Companion to `KappaMonoid/Section5.lean`, which contains the `sorry`-ed statements — 30 of them,
all type-checked. Work through the steps in the order given; each is independently checkable.

## Read this first

**§5 is blocked on `SECTION4-PLAN.md` step 4.** Lemma 5.1 and both directions of Theorem 5.3 go
through Corollary 4.7(1), which is still `sorry` in `KappaMonoid/Section4.lean` and depends on
axiom A5. Nothing in §5 can be closed before that is.

**§5 is the most expensive section per result.** Unlike §§2–4, its proofs are explicit
combinatorial constructions — Lemma 5.2(3) writes down three interleaved partitions of `ℕ` by
hand — and Proposition 5.4 needs trace ideals, which Mathlib does not have. Budget accordingly:
steps 1–4 are comparable in size to all of §3.2, and step 5 is a small module-theory development
of its own.

## Ground rules

Same as `SECTION3-PLAN.md` and `SECTION4-PLAN.md`:

- `lake build` stays green and `sorry`-free at every commit. `KappaMonoid/Section5.lean` is
  **not** imported by `KappaMonoid.lean`; build it with `lake build KappaMonoid.Section5`.
- After a manifest bump run `lake exe cache get` first.
- Instance-resolution traps: a plain `def` is not reducible, so state results at
  `(projClass R κ hκ).carrier` rather than at an abbreviation; double coercions `↥↑m` defeat
  synthesis, so state subtype-of-subtype lemmas over a plain type variable and transport.
- §5 fixes `κ = ℵ₀` throughout. `KMonoid ℵ₀ H` is `LMonoid ℵ₁ H` plus `ℵ₀ ≤ ℵ₀`; index types are
  countable, so `ℕ` is the canonical index and `Idx ℵ₀ ≃ ℕ`.

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

All of this is in the scaffold already, along with `familyOfForm`, `HasFiniteForm`,
`HasInfiniteForm`, `NoMixedForms` and `BraidedForms`. Two encoding notes:

- **The index type is `Nats := ULift.{u} ℕ`, not `ℕ`.** `BraidingData` indexes by a type in the
  cardinal's universe, and `#ℕ : Cardinal.{0}` will not unify with `Cardinal.{u}`. Everything in
  the section indexes by `Nats`.
- `familyOfForm` puts the `α` copies of `x₁` first, the `β` copies of `x₂` next, and `0`
  afterwards. Order is irrelevant to the sum (`lsumOf_comm`, Basic.lean), so this is a choice of
  representative, not a loss.

Only `sumOf_familyOfForm` is left open at this step: the family sums to the element its form
represents. `BraidedForms` being an equivalence relation comes free from `braidingSetoid`.

## Step 2 — Lemma 5.1 (`l:twogen-braided`)

If `H ≅ V^{ℵ₀}(R)` for a ring whose projectives are direct sums of f.g. modules, then `x₁` and
`x₂` are classes of f.g. modules, `H` is braided over `add (x₁ + x₂)`, and
`V(R) ≅ add (x₁ + x₂) = ⟨x₁, x₂⟩`.

Direct from `corollary_4_5_three` plus `corollary_4_7_one_backward`. The one step needing care is
the paper's parenthetical: *both* `P₁` and `P₂` must appear as summands of f.g. modules, else
`V(R)` would be cyclic and hence so would `V^{ℵ₀}(R)` — that uses `KGenerates` and the
non-cyclicity hypothesis, and is where `H` being non-cyclic first bites.

## Step 3 — Lemma 5.2 (`easyfactlemma1`), five parts

- **(1)** an infinite and a finite form cannot be braided. The paper says "clear". It is: in a
  braiding, the finite form's family has cofinitely many zero terms, so cofinitely many blocks
  contribute `0`, while the infinite form's family has infinitely many non-zero terms. Reducedness
  (`LMonoid.isConical`, already proved) closes it.
- **(2)** two finite forms of an element are braided over `add (x₁ + x₂)`. Also easy: both sums
  lie in `add (x₁ + x₂)` by construction, so the one-block partition works.
- **(3)** the substantial one. `x_i ∈ add x_j` and no element has both a finite and an infinite
  form ⟹ `α X_i + ℵ₀ X_j` and `β X_i + ℵ₀ X_j` are braided, for all `α, β ≤ ℵ₀`. The paper gives
  the partitions explicitly — `I₀ = {0,…,α-1}`, `I_k = {α + n(k-1), …}`, `J_k = {nk, …}` with
  `u_k = α x_i`, `v_k = t`, `v_0 = 0` — so transcribe them. Expect this to be the longest proof
  in the section: it splits on `α` finite versus `α = ℵ₀`, and the second case re-derives
  `m x_j = (m'+1) x_i + n' x_j` before building its partitions.
- **(4)** `x_i ∉ add x_j`, no mixed forms, `m X_i + ℵ₀ X_j` braided with `n X_i + ℵ₀ X_j` ⟹
  `m x_i + k x_j = n x_i + k' x_j` for some finite `k, k'`.
- **(5)** `H` braided over `add (x₁ + x₂)` ⟹ (`x_i ∈ add x_j` ↔ `ℵ₀ (x₁ + x₂) = ℵ₀ x_j`). Uses
  Lemma 2.14, `eq_cmul_top_of_add` in `OrderUnit.lean`, which is proved.

Do (1), (2), (5) first — they are cheap and (5) is used by both later steps.

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
being **formalised, not assumed**: unlike Bergman–Dicks (A5) or Leavitt (A2) they are elementary,
so assuming them would be assuming the inconvenient rather than the out-of-reach.

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

**Do these first.** They are the cheapest `sorry`s in the file and they exercise `addOf`, `ecmul`,
`eval` and `Form.IsInfinite` end to end — a real check on the step 1 encoding before the expensive
proofs are built on top of it.

## Dependency order

```
SECTION4-PLAN step 4 (Cor 4.7(1), axiom A5)
        │
        ▼
step 1 (forms) ──> step 2 (Lem 5.1) ──> step 3 (Lem 5.2) ──> step 4 (Thm 5.3) ──> step 6 (Cor 5.5)
                                                                                        ▲
                                        step 5 (trace ideals, Prop 5.4) ────────────────┘
```

Step 5 is independent of steps 1–4 and can be done in parallel; it only meets the rest at 5.5(3).

## Status

30 `sorry`s in `KappaMonoid/Section5.lean`, all statements type-checked; the root `lake build`
stays green and `sorry`-free because the file is not imported by `KappaMonoid.lean`.

## One thing to fix in the paper

Corollary 5.5(3) reads "The converse is not true.2" — a stray `2` after the full stop, at
`kappa_monoids.tex:2133`. Not a formalisation issue, but worth catching before submission.
