# Section 5 — implementation plan

*Realization to hereditary rings for two-generated `ℵ₀`-monoids.*

Section 5 was omitted from the formalisation by request, and there is no scaffold file for it yet.
This plan says what formalising it would take, in the order it should be done. The Lean signatures
below have been type-checked against the current tree.

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

- `lake build` stays green and `sorry`-free at every commit. Put §5 in a new
  `KappaMonoid/Section5.lean`, **not** imported by `KappaMonoid.lean`; build it with
  `lake build KappaMonoid.Section5`. It will `import KappaMonoid.Section4`.
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

These four compile as written (`Cardinal.ofENat_le_aleph0` is in Mathlib, and
`simp [ecmul]` proves `ecmul ⊤ x = cmul ℵ₀ x`). Then add:

- `familyOfForm : Form → (ℕ → H)`, the family with `α` copies of `x₁` followed by `β` copies of
  `x₂` — the paper's `(y_k)_{k ∈ ℵ₀}`. Only well-defined up to reindexing, which is fine:
  `lsumOf_comm` (Basic.lean) says the sum does not see the order.
- `eval_familyOfForm : lsumOf _ (familyOfForm x₁ x₂ F) = eval x₁ x₂ F`.
- `IsFormOf x₁ x₂ F y : Prop := eval x₁ x₂ F = y`, and the key predicate the section turns on:
  **`y` has both a finite and an infinite form**.
- `Braided F G : Prop`, two forms braided over `add (x₁ + x₂)` — `braidingSetoid` from
  `Braiding.lean` applied to `familyOfForm F` and `familyOfForm G`.

`Braided` being an equivalence relation (used constantly, e.g. "by transitivity and symmetry it
suffices to consider `β = 0`") comes free from `braidingSetoid`.

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

## Step 5 — Proposition 5.4 (`traceideal`) — needs a decision

For projective `P`, `Tr(P) := Σ_{f ∈ Hom(P,R)} im f`. **Mathlib has no trace ideal** — there is no
`traceIdeal`, and `Module.trace` is the trace of an endomorphism, unrelated. The definition itself
is one line:

```lean
noncomputable def traceIdeal (R P : Type u) [Ring R] [AddCommGroup P] [Module R P] : Ideal R :=
  ⨆ f : P →ₗ[R] R, LinearMap.range f
```

but the proposition rests on two standard facts about it that would have to be proved:

1. `Tr(P)` is idempotent;
2. `Tr(P)` is the least ideal `I` with `P = P I`.

Both are short in the literature (see the paper's citations to Pavel–Puninski and Whitehead) and
neither is deep, but together with the four-way equivalence they are a self-contained piece of
module theory — call it a day's work, not an hour's.

> **Ask before axiomatising.** The cheap route is to assume (1) and (2) as an axiom, but I would
> not: unlike Bergman–Dicks (A5) or Leavitt (A2), these are *elementary* and provable in Mathlib
> as it stands, so assuming them would be assuming something merely inconvenient rather than
> something out of reach. Prove them. If the budget says otherwise, that is a maintainer call.

Note that the proof of (iii) ⇒ (iv) uses Lemma 2.14 (`eq_cmul_top_of_add`), already proved, and
the final claim uses Lemma 5.1.

## Step 6 — Corollary 5.5 (`hereditarycase`), three parts

Case analysis on how `add x₁` and `add x₂` compare — incomparable, equal, or `add x₁ ⊊ add x₂` —
each giving an equivalence between realizability and an explicit relation condition. All three are
bookkeeping on top of Theorem 5.3, plus Proposition 5.4 for part (3)'s trace formulation.

Two of the parts assert **"the converse is not true"** with the same witness: `H := ℕ₀² ∪ {∞}`,
the trivial `ℵ₀`-extension of `ℕ₀²` with `x₁ = (1,0)`, `x₂ = (0,1)`. That is Example 2.3(1), which
is *already formalised* in `KappaMonoid/Examples.lean` — so both counterexamples are cheap and
worth doing early as a sanity check on the step 1 encoding.

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

## One thing to fix in the paper

Corollary 5.5(3) reads "The converse is not true.2" — a stray `2` after the full stop, at
`kappa_monoids.tex:2133`. Not a formalisation issue, but worth catching before submission.
