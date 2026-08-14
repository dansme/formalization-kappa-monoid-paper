# Refactor — implementation plan

*Two goals: make the development reusable outside this paper, and make its agreement with the paper
checkable by a human in an afternoon.*

Companion to `CLAUDE.md`, which keeps the conventions and the traps.

**Steps 0–7 and 9 are done**, and step 8 in the one place it paid.  Two deliberate departures from
the plan as written: the paper's `\label`s were left alone, so the `@[paper]`
attribute and the generated index (steps 3 and 6 as planned) gave way to a `Paper/` layer written
once by hand; and `Paper/Section{2,3,4}.lean` are `alias` indices rather than full restatements,
which only §5 got.

**Step 8(a) turned out not to exist.**  See its entry below: the "137 redundant hypotheses" in the
measurement table was a count of a string, not of a redundancy.

## Read this first

The development is complete and green; this is a reorganisation, not new mathematics. Two goals,
and every step below is justified by one of them:

- **R (reuse).** Someone formalising a different paper should be able to import the `κ`-monoid core,
  or the braiding theory, or the module layer, without taking the rest — and without taking the six
  axioms or the whole of Mathlib.
- **V (verification).** A referee with the PDF should be able to check that every numbered result is
  formalised, and formalised faithfully, by reading a few hundred lines — not 19 000.

**Invariants for every commit**, as usual: `lake build` green and `sorry`-free, the axiom list
unchanged, `README.md` and `CLAUDE.md` updated in the same commit as the change they describe.
Phases 0–2 must not change a single proof; phase 3 is the only one that does, and it moves one
notion at a time behind deprecated aliases.

## Why — the measurements this plan is answering

Taken on the tree at `0cb5519`:

| Observation | Number |
|---|---|
| Files with **zero** module-theoretic content (`Basic`, `Braiding`, `Universal`, `Section2/{Free,OrderUnit,Cyclic,Examples}`, `Section3/*`, `Section5/{Forms,Braided,Counterexample}`) | 13 files, ≈ 11 600 of 19 000 lines |
| Yet `Section5/Forms.lean` → `Section4/AddOf.lean` → `ModuleClass.lean` → `Axioms.lean` | pure monoid theory imports all six axioms |
| `import Mathlib` in the core (`Basic.lean`, `Axioms.lean`) | everything inherits all of Mathlib |
| ~~`(hκ : ℵ₀ ≤ κ)` in statements — though `KMonoid.aleph0_le` is a field of the class~~ **wrong: see step 8** | ~~137~~ 6 apparent, 0 real |
| ~~`(hlam : lam.IsRegular)` — though `LMonoid.isRegular` is a field~~ **same error** | ~~47~~ |
| `letI` (of which inside statements) | 602 (456) |
| `(κ := …)` explicit arguments | 804 |
| Numbered environments in `kappa_monoids.tex` (14 lemma, 10 defi, 6 prop, 5 cor, 4 examples, 3 teor, 3 example, 3 remark) | 48, of which **15 carry no `\label`** |
| Declarations carrying a bold paper reference | ≈ 90, **none of them in `Braiding.lean`**, which holds Lemmas 3.2–3.8 in an unbolded style |
| Stale entries found in the hand-maintained correspondence tables (2026-08-14) | 2 (`prop_2_17`, `map_cmul_of_isKHom`) |

Two of §5's six corrected statements were *dropped standing hypotheses* (`hgen` in Lemma 5.2(3) and
5.2(4)). Step 5 below is aimed squarely at that failure mode.

## Ground rules

- The layering is a **claim about imports**, so it is enforced in CI (step 1), not by convention.
- Paper-numbered names (`theorem_3_11`, `lemma_5_2_one`) belong in `Paper/` only; library layers get
  descriptive names and carry the paper number in the docstring and the `@[paper]` attribute.
- No renaming for its own sake. A file move plus an `import` fix is cheap to review; a rename buried
  in a move is not. Keep the two in separate commits.
- Each step ends with `lake build` green, and steps 0–2 additionally with a **diff of nothing but
  imports, module headers and whitespace** in the moved files.

---

## Step 0 — split `Section4/AddOf.lean`, the proof of concept — **done** (R)

The smallest change with a measurable result. [`Section4/AddOf.lean`](KappaMonoid/Section4/AddOf.lean)
holds two unrelated things:

- lines 36–115: `addOf`, `addOfCard`, `addOf_isLSubset`, `self_mem_addOf`, `addOf_isSaturated`,
  `addOfCard_isLSubset` — pure `κ`-monoid theory, no module in sight;
- lines 117–end: `ℵ₀⁻`-small classes, `V(R) = add [R]`, Corollary 4.7 (axiom A5), Examples 4.8(1).

Move the first block to `Core/AddOf.lean`, leave the rest as `Modules/Corollary47.lean`.
`Section5/{Forms,Braided,Counterexample}` then stop importing `ModuleClass.lean` and, with it, all
six axioms.

**Acceptance:** `#print axioms` on `sumOf_familyOfForm`, `exists_form`, every part of Lemma 5.2 and
the three `cex_*` counterexample results reports only `propext`, `Classical.choice`, `Quot.sound`
*and no longer depends on the `Axioms.lean` module at all* — check with `lake build` after deleting
the import, not with `#print axioms`, which was already clean.

## Step 1 — layer the tree by subject — **done** (R, V)

```
KappaMonoid/
  ForMathlib/   Finprod, NatBlocks, TraceIdeal                  (unchanged, no repo deps)
  Core/         monoid theory: no modules, no axioms
  Braiding/     braidings, braided extensions, universal extensions
  Modules/      ModuleClass, Theorem 4.3, projectives, rings, trace ideals
  Examples/     ℝ≥0∞, F_κ, TrivExt, RTilde, Diophantine systems, ℕ₀² ∪ {∞}
  TwoGen/       §5: forms and the classification
  Axioms/       Rank.lean, Monoid.lean, Modules.lean
  Paper/        Section2.lean … Section5.lean — statements only
```

Mapping, with cut points taken from the `/-! ##` headers that are already in the files (this is
what was actually done; the cut points held, and only the file names drifted from the sketch):

| Now | After |
|---|---|
| `Basic.lean` (2251) | `Core/Index.lean` (39–123), `Core/SumData.lean` (124–335), `Core/LMonoid.lean` (336–796), `Core/KMonoid.lean` (797–1401), `Core/Subobject.lean` (1402–1646), `Core/Bare.lean` (1647–2007), `Core/LHom.lean` (2144–2250), and **`Paper/Definition21.lean`** (2008–2143, `PaperKMonoid`) |
| `Braiding.lean` (2575) | `Braiding/Prelim.lean` (28–105, keeping the finsum bridge — `Aux` is a reserved file name on Windows), `Braiding/Defs.lean` (106–523), `Braiding/TransAleph0.lean` (524–1510), `Braiding/Sums.lean` (1512–2046), `Braiding/TransUncountable.lean` (2048–2557), `Braiding/Over.lean` (2559–end) |
| `Universal.lean` | `Braiding/UnivAux.lean` (51–489), `Braiding/Prop39.lean` (491–847), `Braiding/UnivExt.lean` (848–end) |
| `ModuleClass.lean` (2115) | `Modules/Small.lean`, `Modules/DirectSum.lean`, `Modules/Class.lean`, `Modules/Theorem43.lean` (490–1674), `Modules/Projective.lean` (1739–end) |
| `Section2/{Free,OrderUnit,Cyclic}.lean` | `Core/{Free,OrderUnit,Cyclic}.lean` |
| `Section2/Examples.lean` | `Core/Cardinal.lean` (`F_κ` — the free monoid is built from it, so not an example) and `Examples/{TrivExt,ENNReal}.lean` |
| `Section2/Rings/*` | `Modules/Rings/*` |
| `Section3/Diophantine.lean` (2149) | `Braiding/Saturated.lean` (Lemma 3.13, general), `Examples/Diophantine.lean` (linear systems, Prop. 3.14, Example 3.15) |
| `Section3/Reals.lean` | `Examples/Reals.lean` |
| `Section4/AddOf.lean` | `Core/AddOf.lean` + `Modules/Corollary47.lean` (step 0) |
| `Section5/Braided.lean` | `TwoGen/Lemma52.lean` (monoid-only) + `TwoGen/Lemma51.lean` (needs `V^{ℵ₀}(R)`) |
| `Section5/{Forms,Realization,Trace,Corollary55,Counterexample}.lean` | `TwoGen/` unchanged |

Lake resolves modules package-wide, so separate `lean_lib`s would *not* stop `Core/` importing
`Modules/`. Enforce it with a script instead — `scripts/check_layering.sh`, run in CI:

```fish
# Core/ may import only Core/ and ForMathlib/; Braiding/ adds Core/; …
# and no file under Core/ or Braiding/ may mention `Module`, `Ring` or `Ideal`.
```

Optionally also declare `KappaMonoidCore`, `KappaMonoidBraiding`, `KappaMonoidModules` as
`lean_lib`s so downstream users have named targets to depend on; the check above is what makes the
claim true.

**Cost:** two sessions, mechanical. The risk is import cycles that only appear on the build; do the
moves one layer at a time, bottom up, and build between.

## Step 2 — narrow the imports — **done** (R)

`Basic.lean` and `Axioms.lean` say `import Mathlib`. Replace with the minimum, using
`Mathlib.Tactic.MinImports`:

```lean
#min_imports in theorem KappaMonoid.lsumOf_sigma …
```

Expect `Core/` to need `Mathlib.SetTheory.Cardinal.Regular`, `Mathlib.SetTheory.Ordinal.Arithmetic`,
`Mathlib.Data.Set.Card` and two or three `Mathlib.Algebra.Order.*`. Do it per new `Core/` file after
step 1, not before — the files are smaller and `#min_imports` is then per-file rather than for 194
declarations at once.

Also give `ForMathlib/` its own `lean_lib`, and open the three upstreaming PRs: `traceIdeal` is a
genuine Mathlib gap (`Module.trace` is unrelated), `Nat.blockIdx` and the `finsum` lemmas are small.

**Payoff, both directions:** a reuser gets the core without analysis and topology, and the local
edit/build loop over `Braiding/` stops re-elaborating Mathlib's import closure.

## Step 3 — the `@[paper]` attribute — **dropped** (V)

`KappaMonoid/Meta/PaperRef.lean`, roughly 40 lines. Key on the **`\label`**, not the number: the
paper is still being revised, and a renumbering would silently invalidate all ≈ 90 docstrings.

```lean
-- sketch, not checked
initialize paperAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `paper
    descr := "the labelled result of kappa_monoids.tex that this declaration formalises"
    getParam := fun _ stx => match stx with
      | `(attr| paper $s:str) => return s.getString
      | _ => throwError "usage: @[paper \"l:twogen-braided\"]"
  }
```

Used as `@[paper "l:twogen-braided"] theorem lemma_5_1 …`. The plan documents already speak in
labels (`easyfactlemma1`, `hereditarycasecor`), so the vocabulary exists.

**Prerequisite: 15 of the 48 numbered environments carry no `\label`** — among them four `defi`s in
§2.2, the two `prop`s at `kappa_monoids.tex:758` and `:778`, and the `cor` at `:1608`. Adding them
is one line each in a paper we control, and it is worth doing before the attribute goes in: an
unlabelled result would have to be keyed by position, which is exactly the fragility the labels are
there to avoid. Do it as its own commit, touching only `kappa_monoids.tex`.

## Step 4 — `Paper/SectionN.lean` — **done for §5, indices for §§2–4** (V)

One file per section containing **only** the paper's numbered results, each restated as faithfully
as the library allows, each proved by one line, each tagged:

```lean
/-- **Lemma 3.2** (telescoping).  Braided families have equal `κ`-sums. -/
@[paper "l:telescope"]
theorem lemma_3_2 … := sumOf_eq_of_isBraided …
```

`PaperKMonoid` (`Basic.lean` 2008–2143) moves here in step 1: it is exactly this pattern already —
Definition 2.1 verbatim, plus the proof that it agrees with the working definition.

This is the deliverable for goal V: four files of ≈ 150 lines each, read against the PDF. It also
gives the deviations one home — today they are in four `README.md` sections, the docstrings, and
three plan documents.

**Do not skip the restatement.** A `Paper/` file that merely re-exports `sumOf_eq_of_isBraided`
under a new name checks nothing. The point is that the statement is written from the PDF and then
*discharged* by the library, so a mismatch is a build error.

## Step 5 — the `Setting` structures — **done for §5** (V)

The paper's standing assumptions are prose: *"Throughout the section, let `H` be a non-cyclic
`ℵ₀`-monoid generated by two elements `x₁` and `x₂`"* (`kappa_monoids.tex:1893`). Formalise each one
as a structure —

```lean
/-- The standing assumptions of §5, `kappa_monoids.tex:1893`. -/
structure Setting5 (H : Type v) [KMonoid (ℵ₀ : Cardinal.{u}) H] where
  x₁ x₂ : H
  gen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H)
  noncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)
```

— and have every `Paper/Section5.lean` statement take it as one argument. Then a §5 result *cannot*
silently drop a standing hypothesis, which is how two of the six §5 corrections arose. §2.2's "let
`H` be a `κ`-monoid with order-unit `u`" (`:675`) gets the same treatment.

## Step 6 — the generated index — **dropped** (V)

`lake exe paper_index`, a Lean executable that imports `KappaMonoid` and does three things:

1. reads `kappa_monoids.tex`, scans the 15 `\newtheorem` environments in order of appearance, and
   computes the number and statement text of each of the 48 numbered results;
2. reads the `@[paper]` registry and `collectAxioms` for each tagged declaration;
3. writes `PAPER-INDEX.md`: number → label → statement → Lean name → `file:line` → axioms →
   deviation, plus a section of *deliberate* omissions (Lemma 3.4(2)(3), Lemma 3.5, Remark 3.16,
   Corollary 4.6, the two extra clauses of Corollary 5.5(3)) each with its reason.

`--check` mode diffs against the committed file and fails; CI runs it. Two failure modes then become
build errors rather than prose that drifts: a numbered result nobody formalised and nobody excused,
and a docstring whose bold number no longer matches what its label resolves to.

This retires the correspondence tables in `README.md` and the three plan documents — which is where
today's two stale names were.

## Step 7 — axiom provenance as code — **done** (V)

CI checks only that the six `axiom` declarations exist; it does not check *who uses them*. Add
`#assert_axioms` (again over `collectAxioms`) and a `Paper/AxiomAudit.lean`:

```lean
#assert_axioms theorem_5_3 [bergmanDicksData]
#assert_axioms prop_2_16   [mk_le_of_span_eq_top, leavittData, cyclicMonoidClassification]
#assert_axioms theorem_3_11 []
```

The `README.md` provenance table becomes generated output. This is also what makes step 8 safe: an
accidental axiom dependency introduced while rewriting proofs breaks the build immediately.

## Step 8 — retire the plumbing — **(a) does not exist, (b) done where it concentrates, (c) not started** (R, V)

The only step that rewrites proofs. One notion per commit, old names kept as `@[deprecated]`
abbreviations until the last use is gone.

1. ~~**Redundant hypotheses.**~~ **This was a mistake in the diagnosis, and there is nothing to do.**
   The measurement counted occurrences of the string `hκ : ℵ₀ ≤ κ`. Classifying them instead: of the
   106 in declarations, 100 are needed outright, and the six a classifier flags are false positives —
   each uses `hκ` to *build* the very instance it would be redundant against (`projClass R κ hκ`,
   `instKMonoidFreeK κ hκ B`, `freeClass Rl.R κ hκ`). `Core/OrderUnit.lean`, the file the plan named
   as the pilot, contains no `hκ` at all: its `variable [KMonoid κ H]` already supplies it, which is
   precisely the pattern the sweep was meant to introduce. The lesson is the obvious one — measure
   the property, not a string that correlates with it.
2. **Bundled subobjects — the concentrated half is done.** 42 of the 49
   `letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (…)` sites were the *same* subset,
   `add (x₁ + x₂)` at `κ = ℵ₀`, written out in every §5 statement and again in its proof.
   `KMonoid.instLMonoidAddOf` makes it an instance and 39 copies go, leaving 18 sites over genuinely
   different subsets. Sound because `IsLSubset` is a `Prop` (trap 13), so the instance is
   definitionally what the `letI`s produced.

   **Still to do:** `LSubmonoid lam X` and `KSubmonoid κ H` as structures with `SetLike` and an
   `LMonoid` instance on the coercion, replacing `IsLSubset` generally — 80 `IsLSubset` and 18
   `IsLSubmonoid` mentions across 17 files. This is the single biggest readability win left: `lemma_5_1`'s statement is currently eight lines, three of them
   instance plumbing, and the reader has to decode them before comparing with the paper. Note
   trap 13 — `IsLSubset` being a `Prop` is what makes `of_set_eq` a one-line `subst`; check the
   bundled version keeps that.
3. **Bundled homomorphisms — not started.** `IsLHom`/`IsKHom`/`IsLMonoidHom` become structures with
   `FunLike`, `comp`, `id`, `ext`. This removes traps 7 and 12 outright — both are consequences of a
   `def` that unfolds to a `∀` — and gives downstream users an API they can compose. Sized: 119
   mentions (`IsKHom` 61, `IsLMonoidHom` 35, `IsLHom` 23) across 11 files, but only 6 anonymous
   constructors; the bulk of the work is renaming `.1`/`.2` to `map_zero`/`map_ksum` and turning
   `IsLMonoidHom`'s direct application `hf hι x` into `hf.map_lsumOf hι x`. `IsKHom.comp` and
   `IsKHom.id'` already exist, added by step 9.

**Cost:** three or four sessions, and the only step where a proof can break. Steps 6–7 exist partly
to make it verifiable: the index and the axiom assertions both have to keep passing.

## Step 9 — universe-generalise `IsUniversalKExtension` — **done** (R)

`universal` quantifies over test objects in the same universe as the extension (trap 8). `README.md`
already records that `extend_lhom` works for a `K` in any universe, so this is a change to the
definition and to Theorem 3.11's *statement*, not to its proof. It removes one of the four
documented deviations — Examples 4.8(1) can then say `V^κ(C) ≅ F_κ(B)` as the paper does — and it
removes a real limitation for anyone reusing the universal-extension machinery.

## Dependency order

```
step 0 (AddOf split) ──> step 1 (layering) ──> step 2 (imports)
                              │                     │
                              └──> step 3 (@[paper]) ──> step 4 (Paper/) ──> step 6 (index)
                                                            │                    │
                                                     step 5 (Settings)     step 7 (axioms)
                                                                                 │
                                                                            step 8 (plumbing)
                                                                                 │
                                                                            step 9 (universes)
```

Steps 0–2 are R, steps 3–7 are V, and step 8 is both. Steps 3–7 add files only and can be done
while the layering is in flight; step 8 should wait for step 7, which is its safety net.

## What this plan does not do

- No new mathematics, and no change to what the six axioms assert.
- No proof golfing. If a proof breaks in step 8 it gets repaired, not rewritten.
- It does not close the open items: the braiding half of the Prop. 3.14(2) counterexample, the two
  extra clauses of Corollary 5.5(3), Lemma 3.4(2)(3)/3.5/Remark 3.16. Those stay recorded in
  `SECTION{3,5}-PLAN.md`, and step 6 makes them visible as explicit omissions rather than absences.

## Status

Steps 0–2 (reuse) and 4–5 (verification) are done; steps 3 and 6 were dropped when the paper's
`\label`s were left alone — the correspondence is taken once, by hand, in `Paper/`, rather than
generated and checked against the `.tex`.  The cost of that choice: if the paper is renumbered, the
`Paper/` docstrings go stale silently, and there is no check that a numbered result has an entry.

What the four commits achieved, measured on the tree afterwards:

| | before | after |
|---|---|---|
| Files reaching the six axioms | all of §5's monoid material | `Modules/`, `TwoGen/Lemma51` and after |
| Mathlib surface of `Core/` + `Braiding/` | all of Mathlib | 16 named modules |
| `import Mathlib` | `Basic.lean`, `Axioms.lean` | `Axioms/*`, `Modules/Small.lean`, both deliberate |
| Files | 27 | 58 |
| Largest file | 2575 lines | 1160 |
| Enforced invariants in CI | sorry-free, axiom list | + the layering |
| Paper correspondence | three prose tables, two entries stale | `Paper/`, 97 checked index entries and §5 restated |

Steps 7 and 9 are done, and step 8 in the one place it concentrated.  What remains is the general
bundling — subobjects (`IsLSubset` → a `SetLike` structure) and homomorphisms (`IsKHom` and friends
→ structures with `FunLike`) — which is a proof-rewriting job of about 200 sites across 17 files,
and wants its own session now that the axiom audit of step 7 is there to catch a proof that quietly
changes what it depends on.

| | before steps 7–9 | after |
|---|---|---|
| Axiom provenance | prose in `README.md` | 43 `#assert_axioms`, checked, non-vacuous |
| Test objects of a universal property | the extension's own universe | a parameter |
| Examples 4.8(1) | a documented deviation | `krsa_ascent_iso`, the paper's statement |
| Documented deviations | four | three |
| `letI := IsLSubset.lmonoid …` | 55 | 18 |
