# Completing Section 2

**Status (commits on `simplify`): steps 1–8, 10 and the axioms file are done and `sorry`-free,
as is the Definition 2.10 payoff of step 5.  Only step 9 (Propositions 2.16 and 2.17) remains.**

**Correction to step 9 discovered while implementing it:** `ModuleClass` cannot express
`V^κ(𝓕^κ)`, because it carries a summand-closure field (`exists_of_isCompl`) that §4 needs and
free modules do not satisfy.  Proposition 2.16 therefore needs `V^κ(𝓕^κ)` built either by
splitting `ModuleClass` into Definition 2.4's base structure plus summand closure, or — probably
cheaper, and it leaves Theorem 4.3 untouched — as a bespoke `κ`-monoid on rank classes.  It also
needs the elementary classification of cyclic monoids as `ℕ₀` or `C_{m,n}` to match against
`CyclicRel`.

A sequential work plan for finishing the formalisation of §2 of Nazemian–Smertnig,
*A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

Baseline: branch `simplify`, commit `6c72a2e`. Every file is `sorry`-free at that commit.
Paper source: `kappa_monoids.tex` / `kappa_monoids.pdf` (numbering below refers to the PDF).

## What is already done

| Paper | Where |
|---|---|
| Def. 2.1 (both the verbatim form `PaperKMonoid` and the working form `KMonoid`) | `Basic.lean` |
| Examples 2.3(1)(2)(3) | `Examples.lean` |
| Examples 2.3(4), Def. 2.4 (`V^κ(C)`, `V^κ(R)`) | `Modules.lean` |
| Lemma 2.5, incl. `SumData`/`BareKMonoid` reconstruction of `+` from `Σ` | `Basic.lean` |
| Def. 2.6, Lemma 2.7, Lemma 2.8 — **at the κ level only** | `Basic.lean` |
| §2.1 homomorphisms, submonoids, `⟨S⟩_κ`, Def. 2.10 | `Basic.lean` |
| Def. 2.18 (`LMonoid`), forward half of Remark 2.19 | `Basic.lean` |

## What this plan covers

* Prop. 2.9 (free objects), Def. 2.11–2.12, Ex. 2.13, Lemma 2.14 (order-units),
  Lemma 2.15, Prop. 2.16–2.17 (realisation) — none of which is currently stated;
* the λ⁻ analogues of Lemmas 2.7 and 2.8, whose absence is the one gap with a
  mathematical consequence downstream (it forces an extra hypothesis on Theorem 3.11);
* two loose ends from the bullets after Lemma 2.5.

---

## Ground rules

1. **One step = one commit.** Before committing: `lake build` green, and
   `grep -rc sorry KappaMonoid/` zero in every file. Steps are ordered so that the build
   is green at every commit boundary.
2. **Prove at the λ⁻ level, specialise to κ.** `KMonoid κ H` is *defined* as
   `LMonoid (Order.succ κ) H` plus `ℵ₀ ≤ κ`, and `#ι ≤ κ ↔ #ι < Order.succ κ`
   (`KMonoid.lt_succ`, `KMonoid.le_of_lt_succ`). Any fact that can be stated for
   `LMonoid lam` should be, and then wrapped at the κ level. This is the organising
   principle of the codebase and it is what makes most of the work below cheap.
3. **New monoid structures come from `SumData`.** Supply a `SumData lam X`
   (`Basic.lean:133` — three axioms: `sum_congr`, `sum_unique`, `sum_sigma`) and call
   `toLMonoidOfZero` / `toLMonoid'`. Copy the template at `Examples.lean:92`
   (`Fcard.sumData`). Do **not** hand-roll an `AddCommMonoid` and a summation separately.
4. **House style.** Index types live in `Type u`, carriers in `Type v`; docstrings open
   with the bold paper reference (`/-- **Lemma 2.7(2)**: … -/`); defs that produce
   instances carry `@[instance_reducible]`; cardinals are `Cardinal.{u}`.
5. **Never `sorry`.** Three classical results from the literature are sanctioned as
   axioms, all collected in `KappaMonoid/Axioms.lean` (see the section below):
   invariance of infinite rank (step 7), Leavitt's realisation theorem and uniqueness of
   simple multiplicities (step 9). **No further axiom may be added without asking.**
   Anything else that depends on out-of-scope literature should carry the external input
   as an explicit hypothesis; the bare-stub convention
   (`theorem corollary_4_6 : True := trivial` with an explanatory docstring,
   `Modules.lean:2081`) is reserved for results whose *statement* cannot reasonably be
   phrased here.
6. **Update `README.md` in the same commit** whenever a step changes what is claimed.
   The README is currently stale in three places: its file table has no `Examples.lean`
   row; it says order-units and the realisation results were "deliberately left out";
   and it asserts, without proof, that reducedness is automatic for `λ > ℵ₀` (step 2
   turns that into a theorem).

The Lean snippets below are guidance on the intended shape, not code known to compile.
Names of Mathlib lemmas should be checked against the toolchain in `lean-toolchain`.

---

## The sanctioned axioms

Three classical theorems are assumed rather than proved. Each is a theorem of ordinary
mathematics, so assuming them cannot make the development inconsistent — **but a
mis-stated axiom is false, and a false axiom proves everything.** Each statement below
must therefore be reviewed carefully against the literature before it is used, and each
must carry a docstring giving the standard proof sketch or a reference.

All three go in one file, `KappaMonoid/Axioms.lean`, imported only where needed, so that
the blast radius is visible at a glance. Conventions: everything in `Type u` (no
`Cardinal.lift` — do not generalise universes "for good measure", it costs lifts
everywhere); `Nontrivial R` wherever the zero ring would otherwise be a counterexample.

### A1 — Invariance of infinite rank (used in step 7)

```lean
/-- **Assumed** (invariance of infinite rank).  Over a nontrivial ring, a free module with an
infinite basis cannot be generated by fewer elements than its rank.

Standard proof, not formalised here: each element of a generating set `S` has finite support
in the basis, so `S` lies in the span of a subfamily of the basis of size at most `#S ⊔ ℵ₀`;
a basis element outside that subfamily would lie in the span of the others, contradicting
linear independence.  Hence the subfamily is everything. -/
axiom Basis.mk_le_of_span_eq_top {R : Type u} [Ring R] [Nontrivial R] {M : Type u}
    [AddCommGroup M] [Module R M] {ι : Type u} (b : Basis ι R M) [Infinite ι]
    {S : Set M} (hS : Submodule.span R S = ⊤) : #ι ≤ #S
```

Notes on the formulation:

* **The generation form, not the two-bases form, is what the application needs**, because
  the complement appearing in Example 2.13 is merely projective, not free — there is no
  second basis to compare against. Derive the recognisable named statement from it in the
  same file, so the classical result is visibly present:

  ```lean
  /-- Invariance of infinite rank: two bases of the same module, one of them infinite, have
  equal cardinality.  Derived from `Basis.mk_le_of_span_eq_top`. -/
  theorem Basis.mk_eq_mk_of_infinite (b : Basis ι R M) (b' : Basis ι' R M) [Infinite ι] :
      #ι = #ι'
  ```

  Proof: `b'` spans, so `#ι ≤ #ι'`; hence `ι'` is infinite too; apply the axiom again with
  the roles exchanged.
* `Nontrivial R` is required: over the zero ring every type indexes a basis of the zero module.
* The conclusion is `#ι ≤ #S` with no `⊔ ℵ₀`. That is the sharp form and it is true: when
  `S` is finite the hypothesis is itself contradictory, so nothing false is asserted. The
  sharp form is what lets the application avoid a case split on `α` finite vs. infinite.

### A2 — Leavitt's realisation theorem (used in step 9, Prop. 2.16)

```lean
/-- The congruence `~_{m,n}` on `ℕ₀` defining the cyclic monoid `C_{m,n}`: `k` and `l` are
identified iff they are equal, or both are at least `m` and differ by a multiple of `n`. -/
def CyclicRel (m n k l : ℕ) : Prop := k = l ∨ (m ≤ k ∧ m ≤ l ∧ (n : ℤ) ∣ (k : ℤ) - l)

/-- A ring realising the cyclic monoid `C_{m,n}` as its monoid of finitely generated free
modules. -/
structure LeavittData (m n : ℕ) where
  R : Type u
  [ring : Ring R]
  [nontrivial : Nontrivial R]
  iso_iff : ∀ k l : ℕ, Nonempty ((⨁ _ : Fin k, R) ≃ₗ[R] (⨁ _ : Fin l, R)) ↔ CyclicRel m n k l

/-- **Assumed** (Leavitt, 1962).  Every cyclic monoid `C_{m,n}` is the monoid of finitely
generated free modules over some ring. -/
axiom leavittData (m n : ℕ) (hn : 1 ≤ n) : LeavittData.{u} m n
```

Notes:

* Bundling as a structure (rather than an `∃` over a `Ring` instance) keeps instance
  resolution usable downstream: `obtain ⟨R, iso⟩ := leavittData m n hn; letI := …`.
  Instance-implicit structure fields (`[ring : Ring R]`) are supported and make `R`'s
  algebra available in the type of `iso_iff`.
* `CyclicRel` is the *equivalence closure* of the paper's generating relation
  (`|k - l| = n` and `min {k,l} ≥ m`). Check this against the paper before relying on it —
  this is the axiom most easily got wrong.
* The remaining cyclic monoid, `ℕ₀` itself, needs no axiom: any ring with IBN realises it,
  e.g. a field, via Mathlib's rank theory.

### A3 — Uniqueness of simple multiplicities (used in step 9, Prop. 2.17)

```lean
/-- **Assumed**: in a decomposition into simple modules the multiplicity of each isomorphism
class is uniquely determined, infinite multiplicities included.  (Jordan–Hölder gives the
finite case; the infinite case is the classical cardinal-counting extension.) -/
axiom mk_multiplicity_eq {R : Type u} [Ring R] {I J : Type u}
    {A : I → Type u} {B : J → Type u}
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)]
    (hA : ∀ i, IsSimpleModule R (A i)) (hB : ∀ j, IsSimpleModule R (B j))
    (e : (⨁ i, A i) ≃ₗ[R] (⨁ j, B j))
    (S : Type u) [AddCommGroup S] [Module R S] :
    #{i // Nonempty (A i ≃ₗ[R] S)} = #{j // Nonempty (B j ≃ₗ[R] S)}
```

Note that only *uniqueness* is assumed. The companion existence statement — every module
over a semisimple ring is a direct sum of simples — may well be in Mathlib already
(`IsSemisimpleModule`, `IsSemisimpleModule.exists_setIndependent_sSup_simples_eq_top` and
neighbours). **Check before assuming**: if Mathlib has it, do not add a fourth axiom.

### Axiom hygiene (required, after every step that touches the axiom file)

`#print axioms` on the top-level results must show that the assumption has not leaked:
everything in Tracks A and B, plus `theorem_3_11`, `theorem_4_3` and `corollary_4_5`, must
continue to report only `propext`, `Quot.sound`, `Classical.choice`. Only Example 2.13
(A1) and Props. 2.16–2.17 (A2, A3) may name an axiom. Record the resulting provenance
table in the README as part of step 10.

---

## Track A — close the mathematical gap

### Step 1 — Generalise `cmul` to λ⁻-monoids (Lemma 2.7 at the λ⁻ level)

**Why first.** Cardinal scalar multiplication currently exists only in
`namespace KMonoid` (`Basic.lean:801-1017`), and `cmul` is *used nowhere outside
`Basic.lean`* — verified by grep. So this is a contained refactor, and it unlocks step 2.

**Do.** In `namespace LMonoid`:

```lean
/-- **Definition 2.6** at the `λ⁻` level. -/
noncomputable def lcmul (α : Cardinal.{u}) (hα : α < lam) (x : X) : X :=
  lsumOf (lam := lam) (lt_of_eq_of_lt (mk_Idx α) hα) fun _ : Idx α => x
```

Port, in this order: `lcmul_zero_cardinal`, `lcmul_one`, `lcmul_sumOf_cardinal`
(Lemma 2.7(2)), `lcmul_lsumOf` (Lemma 2.7(3)), `lcmul_add`, and `add_lcmul_self`
(the remark after Def. 2.6: `x + α x = α x` for `ℵ₀ ≤ α < lam`).

The existing κ-level proofs transfer line by line under `≤ κ ↦ < lam`. They get *shorter*:
where the κ proofs invoke `Cardinal.mul_eq_self` (`κ * κ = κ`), the λ⁻ versions use the
regularity lemmas already at the top of `Basic.lean` (`mk_prod_lt`, `mk_sigma_lt`).

Then redefine `KMonoid.cmul` as `LMonoid.lcmul` at `lam = Order.succ κ` and keep every
existing `cmul_*` lemma as a one-line wrapper, so no name disappears.

**Done when.** The `Cmul` section of `Basic.lean` is net shorter, all previous `cmul_*`
names still resolve, and the build is green.

### Step 2 — Lemma 2.8 at the λ⁻ level; discharge the added hypothesis in Theorem 3.11

**Do.**

```lean
theorem LMonoid.isConical (h : ℵ₀ < lam) : IsConical X
```

Transcribe `KMonoid.isConical` (`Basic.lean:977`) with `κ ↦ ℵ₀`:
`x = x + ℵ₀·0 = x + ℵ₀(x+y) = (x + ℵ₀x) + ℵ₀y = ℵ₀x + ℵ₀y = ℵ₀(x+y) = ℵ₀·0 = 0`.
The only inputs are `add_lcmul_self` at `α = ℵ₀` (i.e. `1 + ℵ₀ = ℵ₀`) and `ℵ₀ * ℵ₀ = ℵ₀`.
Port Lemma 2.8(2) the same way. Make `KMonoid.isConical` a corollary — `ℵ₀ < Order.succ κ`
holds since `ℵ₀ ≤ κ`.

Then in `Universal.lean`, next to `theorem_3_11`:

```lean
/-- **Theorem 3.11** for `λ > ℵ₀`, where the added `IsConical` hypothesis is automatic. -/
theorem theorem_3_11_of_aleph0_lt (hlam : ℵ₀ < lam) … -- same conclusion, hypothesis discharged
```

**Why this matters.** `theorem_3_11` carries an `IsConical X` hypothesis that is not in the
paper. It is genuinely necessary for `λ = ℵ₀` (see `isConical_of_isUniversalKExtension`),
but the README claims it is vacuous for `λ > ℵ₀` without proving it. After this step that
claim is a theorem, and the deviation from the paper is confined to `λ = ℵ₀`.

**Done when.** `theorem_3_11_of_aleph0_lt` compiles and the corresponding README paragraph
is rewritten.

---

## Track B — complete the definitional scaffolding

### Step 3 — The two leftovers from the bullets after Lemma 2.5 (small)

(a) Restriction of a κ-monoid to an α-monoid for infinite `α ≤ κ`:

```lean
@[instance_reducible]
noncomputable def KMonoid.ofLE (H : Type v) [KMonoid κ H] {α : Cardinal.{u}}
    (hα0 : ℵ₀ ≤ α) (hακ : α ≤ κ) : KMonoid α H :=
  { toLMonoid := LMonoid.ofLE (Cardinal.isRegular_succ hα0) (Order.succ_le_succ hακ)
    aleph0_le := hα0 }
```

No case split on `α = κ` is needed: the ambient structure is `LMonoid (Order.succ κ)` and
`Order.succ_le_succ` supplies `Order.succ α ≤ Order.succ κ` directly. Add the `sumOf`
compatibility lemma, mirroring `toLMonoidOfLE_lsumOf` (`Basic.lean:1251`); it should be `rfl`.

(b) Finite sums are iterated `+`. Generalise `lsumOf_aleph0_eq_finsum` (`Basic.lean:1788`),
currently stated only for `LMonoid ℵ₀ X`, to arbitrary regular `lam`: for finite `ι`,
`lsumOf h x = ∑ᶠ i, x i`. Route: induction on `Fintype.card ι` using `lsumOf_union` or
`SumData.sum_sumType`. This is the paper's `Σⁿ(x₁,…,xₙ) = x₁ + ⋯ + xₙ` bullet.

**(a) is a prerequisite for step 6** (the filtration `H_α` must carry an α-monoid structure).

### Step 4 — Products, and the λ⁻ cardinal monoid

Prerequisites for step 5.

(a) **`LMonoid.pi`.** For `X : B → Type v` with `∀ b, LMonoid lam (X b)`, put pointwise
sums on `∀ b, X b`. Via `SumData`, with `sum h x := fun b => lsumOf h (fun i => x i b)`;
each axiom is `funext` plus the corresponding axiom of the factors. Specialise to
`KMonoid.pi`. ~40 lines, reusable, and it is what makes `F_κ^B` available.

(b) **`LCard`.** Generalise `Fcard` (`Examples.lean:79`) to

```lean
abbrev LCard (lam : Cardinal.{u}) : Type (u + 1) := {α : Cardinal.{u} // α < lam}
```

with an `LMonoid lam` instance — the existing `Fcard.sumData` proof, with `csum_le_of_le`
replaced by a new `csum_lt_of_lt` (regularity of `lam`). Then set
`Fcard κ := LCard (Order.succ κ)` and re-derive the existing `≤ κ`-flavoured `Fcard` API as
wrappers through `Order.lt_succ_iff`. One construction now serves `F_κ` and `F_{λ⁻}`.

**Pitfall.** `LCard lam : Type (u + 1)` while index types are `Type u`. This is fine —
`LMonoid lam X` allows `X : Type v` — but watch for universe-unification failures when
`LCard` appears as the carrier of a `Pi` type; annotate explicitly rather than letting Lean
guess.

### Step 5 — Proposition 2.9: free objects

New file `KappaMonoid/Free.lean`, importing `Examples`.

```lean
def FreeL (lam : Cardinal.{u}) (B : Type u) : Set (B → LCard lam) :=
  {x | #(Function.support x) < lam}
```

with `FreeK κ B := FreeL (Order.succ κ) B` and
`iota : B → FreeL lam B` sending `b` to the indicator of `b` at value `1`.

* **2.9(1), closure.** The support of a sum is contained in the union of the supports;
  bound it with `Cardinal.mk_iUnion_le` (already used at `Modules.lean:2100`) plus
  regularity of `lam`.
* **Induced structure.** At the κ level use `IsKSubmonoid.kmonoid` (`Basic.lean:1178`).
  At the λ⁻ level note that the existing `IsLSubset` is a subset of a *κ*-monoid closed
  under λ⁻-sums — not what is needed here. Add an `IsLSubmonoid` (subset of a λ⁻-monoid
  closed under λ⁻-sums) with its `lmonoid`; it is a transcription of `IsLSubset.lmonoid`
  (`Basic.lean:1200`) with `sumOf ↦ lsumOf`.
* **2.9(2), universal property.** `f̄ x := sumOf (support x) (fun b => cmul (x b) (f b))`.
  That it is a homomorphism uses Lemma 2.7(2) (`cmul_sumOf_cardinal`) and (A4)
  (`sumOf_sigma`), both available.
* **The fiddly lemma**, needed for uniqueness: `x = Σ_{b ∈ supp x} (x b) • iota b`,
  proved coordinatewise from the `csum_*` lemmas at the top of `Examples.lean`.
  Budget most of this step here.
* **Payoff.** State Def. 2.10 in the paper's literal form and prove it equivalent to the
  current `IsAlphaGenerated` (`Basic.lean:1116`):
  `IsAlphaGenerated κ α H ↔ ∃ B (f : FreeK κ B → H), #B ≤ α ∧ IsKHom κ f ∧ Function.Surjective f`.
  This retires the caveat in that definition's docstring.

**Done when.** `Free.lean` compiles, and both the κ and λ⁻ free objects have their universal
property (the λ⁻ one is asserted at the end of §2.4 of the paper).

---

## Track C — the two skipped subsections

### Step 6 — §2.2 order-units: Def. 2.11, Def. 2.12, `size`, the filtration, Lemma 2.14

New file `KappaMonoid/OrderUnit.lean`.

```lean
/-- **Definition 2.11**.  Notation `≼`, deliberately *not* `≤`: this preorder is not
antisymmetric, so none of Mathlib's canonically-ordered monoid classes applies. -/
def KMonoid.le (a b : H) : Prop := ∃ c, a + c = b

/-- **Definition 2.12(1)**. -/
def IsOrderUnit (u : H) : Prop := ∀ x, x ≼ cmul (κ := κ) κ le_rfl u

/-- **Definition 2.12(2)**. -/
def IsFaithful (u : H) : Prop :=
  IsOrderUnit u ∧ ∀ α β, α < β → β ≤ κ → ℵ₀ ≤ β → ¬ (cmul β ‹_› u ≼ cmul α ‹_› u)

noncomputable def size (u x : H) : Cardinal.{u} :=
  sInf {α | α ≤ κ ∧ ∃ n : ℕ, x ≼ cmul (α + n) ‹_› u}

def part (u : H) (α : Cardinal.{u}) : Set H := {x | size u x ≤ α}
```

* `≼` is reflexive and transitive. Record the paper's `ℕ/2ℕ` counterexample to antisymmetry
  as an `example`, so that nobody later tries to replace `≼` with a Mathlib order class.
* `sInf` on `Cardinal` is legitimate (cardinals are well-ordered); the defining set is
  nonempty exactly because `u` is an order-unit — take `α = κ`. Use `Cardinal.sInf_mem`.
* `part u α` is closed under `sumOf` over index types of cardinality `≤ α`, for infinite `α`
  (Lemma 2.7(2)/(3) plus `Cardinal.mul_eq_self`); give it a `KMonoid α` structure by
  composing **step 3(a)**'s `KMonoid.ofLE` with `IsKSubmonoid.kmonoid`. `part u 0` is an
  ordinary submonoid.
* Monotonicity of the filtration, and
  `IsFaithful u ↔ ∀ α β, α < β → β ≤ κ → ℵ₀ ≤ β → part u α ⊂ part u β`.
* **Lemma 2.14** (`t = κ•u + l ⟹ t = κ•u`) is three lines from `add_cmul_top_eq`
  (`Basic.lean:1006`).

### Step 7 — Example 2.13: `[R]` is a faithful order-unit of `V^κ(R)`

Uses **axiom A1** (`Basis.mk_le_of_span_eq_top`); write `KappaMonoid/Axioms.lean` first if it
does not exist yet.

**Example 2.13 is short.** The pieces:

1. `R^(α)` is spanned by `Set.range (freeGen R α)`, of cardinality `≤ α` — `freeMod_span`
   already proves this (`Modules.lean:1742`).
2. An isomorphism `R^(α) ≃ₗ R^(β) ⊕ P` pushes that spanning set forward and then projects to
   a spanning set of `R^(β)` of cardinality `≤ α`. **No property of `P` is used** — this is
   why the generation form is the right axiom.
3. The axiom gives `β ≤ α`, contradicting `α < β`. Uniform in `α` finite or infinite.

So: `[R]` is an order-unit (immediate: every summand of `R^(κ)` is `≼ κ•[R]`), and faithful
by 1–3. Expect ~40 lines once `cmul α [R]` has been identified with the class of a summand
isomorphic to `⨁ _ : Idx α, R` — that identification follows from `rep_sumOf`
(`Modules.lean:606`) and `dsum_restrict_iso` (`Modules.lean:179`).

**Optional sub-item, do last:** `part [R] α = V^α(R)` for infinite `α ≤ κ`, i.e. that the
filtration by `size` is the filtration by number of generators. Inputs: `exists_small_support`
(`Modules.lean:1902`) and `isLambdaSmall_of_span` (`Modules.lean:211`). The remaining clause
of Example 2.13 — that `V^κ(R)` is generated by `V^{ℵ₀}(R)` — is already proved as
`kaplansky` (`Modules.lean:2017`).

**Axiom hygiene.** Run the `#print axioms` audit described in the axioms section before
committing.

### Step 8 — §2.3 Lemma 2.15: cyclic κ-monoids with a faithful order-unit

Pure monoid theory; fully formalisable, and independent of steps 5–7 (so it can be pulled
forward if step 7 stalls).

1. Every element is `α • u` for some `α ≤ κ`: from `mem_kclosure_iff` (`Basic.lean:1075`)
   plus Lemma 2.7(2) — a κ-sum of copies of `u` is `(Σ αᵢ) • u`.
2. `α ↦ α • u` is injective on infinite `α ≤ κ`, and its image meets `C₀ = {n • u : n ∈ ℕ}`
   trivially. Both from faithfulness.
3. Package as an explicit bijection `C ≃ C₀ ⊕ {α : Cardinal // ℵ₀ ≤ α ∧ α ≤ κ}` and check
   it is a κ-homomorphism.

Prove 1 and 2 as standalone lemmas first; 3 is packaging and may be dropped if it fights
the elaborator — the mathematical content is in 1 and 2.

### Step 9 — §2.3 Propositions 2.16 and 2.17: realisation

Uses **axioms A2** (`leavittData`) and **A3** (`mk_multiplicity_eq`). Both propositions are
proved outright — no hypothesis-carrying statements, no stubs.

**Prop. 2.16** (cyclic κ-monoids with a faithful order-unit are realised by rings). Structure
of the argument:

1. Step 8 gives `C ≅ C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}`, where `C₀` is the size-zero submonoid, a cyclic
   *monoid*.
2. Classify `C₀`: every cyclic monoid is `ℕ₀` or `C_{m,n}` (elementary; prove it, it is not an
   axiom). This is where `CyclicRel` from A2 must line up with `C₀`'s congruence — if the
   translation is awkward, adjust `CyclicRel`, not the classification.
3. Apply A2 to get a ring `R` with `V(𝓕 R) ≅ C₀` (or a field for the `ℕ₀` case), then show
   `V^κ(𝓕^κ R) ≅ C` — the infinite part is forced, because the classification in step 8
   depends only on `C₀` and faithfulness.
4. Faithfulness of `[R]` on the module side is step 7's argument (axiom A1) applied to
   `𝓕^κ R`.

**Prop. 2.17(1)** (`R` semisimple with `n` simple classes ⟹ `V^κ(R) ≅ (Fcard κ)^n`). Route:

* over a semisimple ring every module is a direct sum of simples — **check Mathlib first**
  (`IsSemisimpleModule` and neighbours); assume nothing if it is there;
* the multiplicity map sends a module to the function `simple class ↦ #(copies)`, well defined
  by **A3** and additive by construction;
* it lands in `(Fcard κ)^n` because a κ-generated module has at most κ copies of each simple,
  and it is surjective by taking the corresponding direct sum;
* every module over a semisimple ring is projective, so `V^κ(R)` really is all κ-generated
  modules — Mathlib should have this.

**Prop. 2.17(2)** (for every `n` there is a semisimple ring with exactly `n` simple classes):
take `Fin n → K` for a field `K`. Product of semisimple rings is semisimple, and the simple
modules are the `n` coordinate fields. No axiom; some Mathlib legwork.

### Step 10 — Consistency pass

* README: add the `Examples.lean` row to the file table; delete the sentence saying
  order-units and the realisation results were deliberately left out; rewrite the
  Theorem 3.11 discussion in the light of step 2; add an axiom-provenance section listing
  A1–A3 and exactly which results depend on each, as measured by `#print axioms` rather
  than by memory.
* Leave `corollary_4_6` / `corollary_4_7` (`Modules.lean:2081,2088`) as they are — their
  docstrings already say what they are.

---

## Dependency graph

```
1 ── 2                     (Track A: independent of everything else)
3(a) ─────── 6 ── 7        (7 needs axiom A1)
4 ── 5
8                          (independent; needs only §2.0 + step 1)
9                          (needs 7 and 8; needs axioms A2, A3)
10                         (last)
```

`KappaMonoid/Axioms.lean` may be written in one go before step 7, or split — A1 before
step 7, A2 and A3 before step 9. Writing all three up front is preferable: it makes the
total assumed content reviewable in a single sitting, which is the point of collecting
them in one file.

Recommended order: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10. Steps 1–2 come first because they are the
only ones that change what is *proved* rather than what is *stated*, and because step 1
makes `Basic.lean` shorter rather than longer. If step 7 stalls, jump to 8 and return.

## Out of scope

§2.2's remark that `H` is a preorder but not a partial order beyond the recorded
counterexample; §3.2 (`Fκ(B)` worked extensions, Prop. 3.14); §5 in its entirety. Any
further axiom beyond A1–A3 requires asking first.
