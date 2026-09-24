# A Lean 4 formalisation of Nazemian–Smertnig, *A monoid-theoretical approach to infinite direct-sum decompositions of modules*

Sections 2–5 of the paper.

## Status

Complete and `sorry`-free: `lake build` checks every definition and every theorem, including
Theorem 3.12 (universal `κ`-extensions), Proposition 3.15 (universal extensions of Diophantine
monoids), Theorem 4.3 (`V^κ(C)` is `λ⁻`-braided over `V^{λ⁻}(C_{λ⁻})`), Theorem 5.3 (which
two-generated `ℵ₀`-monoids are `V^{ℵ₀}(R)` for a hereditary ring) and all of §§2–5.

One classical theorem is assumed rather than proved — Bergman–Dicks realisation, see "The assumed
result". Everything else, §3 and the monoid-theoretic parts of §§4–5 included, depends only on
`propext`, `Classical.choice` and `Quot.sound`.

The statements follow the current version of `kappa_monoids.tex`. "Encoding decisions" records
where a result is rendered differently from the paper's prose and why; "What is not formalised"
lists the deliberate omissions.

The development is layered by subject, and each layer is an entry point of its own: importing
`KappaMonoid.Core` or `KappaMonoid.Braiding` gets the monoid theory without the module theory, the
assumed result, or — since the core does not say `import Mathlib` — most of Mathlib.
`scripts/check_layering.sh` enforces this in CI; Lake would not.

| Layer | Depends on | Contents |
|---|---|---|
| `KappaMonoid/ForMathlib/` | Mathlib | No `κ`-monoid content and no dependence on the rest, so it compiles once: `TraceIdeal.lean`, `NatBlocks.lean` (`Nat.blockIdx`, cutting `ℕ` into consecutive blocks), `Finprod.lean`, `Hereditary.lean`, `FreeRank.lean`, `HomDirectSum.lean` + `SimpleMultiplicity.lean`, `CyclicMonoid.lean` (also `C_{m,n}` as a monoid), `Kaplansky.lean`, `Albrecht.lean`, and `CardinalSum.lean` (cardinal sums over a support) — see "Classical results proved here" |
| `KappaMonoid/Core/` | ForMathlib | §2: `Index`, `SumData`, `LMonoid` (= `λ⁻`-monoid) and `KMonoid` with the whole sum API, cardinal scalar multiplication and reducedness (Lemmas 2.7, 2.8), `Subobject` (homomorphisms, `⟨S⟩_κ`, induced structures), `Bare` (`KMonoid.ofBare`, Lemma 2.5), `LHom`, `Cardinal` (`F_{λ⁻}`, `F_κ`), `Free` (**Proposition 2.9**), `OrderUnit` (Defs. 2.11–2.12, **Lemma 2.14**), `Cyclic` (**Lemma 2.15**), `AddOf` (`add x`, `add_λ x`), `OrderUnitTransfer` (faithful order-units move along `u ≼ n v ≼ m u`), `OrderUnitIso` (and along `κ`-isomorphisms), `CyclicExtra` (**Lemma 2.15** as a `κ`-isomorphism; the generator of a cyclic `κ`-monoid is an order-unit), `Compatible` (**Remark 2.19**, compatible families) |
| `KappaMonoid/Braiding/` | Core | §3: `Defs` (Definition 3.1(1), Lemma 3.6), `TransAleph0` (**Lemma 3.7** and Lemma 3.8 for `λ = ℵ₀`), `Sums` (**Lemma 3.2**, Lemma 3.4), `TransUncountable` (**Lemma 3.7** and Lemma 3.8 for `λ > ℵ₀`, and the two combined), `Over` (Definition 3.1(2)), `WellOrder` (**Lemma 3.4(2)(3)**, **Lemma 3.5**, and Definition 3.1(1) over an arbitrary limit well-order), `UnivAux`, `Prop310` (**Proposition 3.10**, Definition 3.11), `UnivExt` (**Theorem 3.12** and its converse), `Saturated` (**Lemma 3.14**), `Components` (**Remark 3.9**: the coarsening is the connected components), `BaseIso` (universal extensions of isomorphic bases are isomorphic) |
| `KappaMonoid/Modules/` | Braiding, Axioms | Definition 2.4 and §4: `Small` (Definition 4.1), `DirectSum`, `Class` (`ModuleClass`, `V^κ(C)`), `Theorem43` (**Theorem 4.3**, the general form of Cor. 4.4), `SmallPart` (**Corollary 4.4**(1)(2)), `Projective` (**Corollary 4.5**(1)(2)(3), Kaplansky in `κ`-monoid form), `Corollary47` (`V(R) = add [R]`, `add_{ℵ₀} [R] = V^{ℵ₀}(R)`, **Corollary 4.7**(1)(2), **Examples 4.8(1)**), and `Rings/` — the §2.2–2.3 ring examples: `ProjOrderUnit.lean` and `Progenerator.lean` (**Example 2.13**), `FreeModules.lean` (`V^κ(𝓕^κ)`), `FreeUnit.lean` (ranks), `Leavitt.lean` (Leavitt's realisation theorem), `Realisation.lean` (**Proposition 2.16**), `Semisimple.lean` (**Proposition 2.17**), `CyclicRealisable.lean` (§2.2.1, and the converse of Proposition 2.16); `Transport.lean` (Example 4.2(1)–(2) completed, "`V^{ℵ₀}(R)` determines `V^κ(R)`", **Corollary 4.6(2)** for hereditary rings) |
| `KappaMonoid/Examples/` | Braiding | `TrivExt` (**Examples 2.3(1)**), `ENNReal` (2.3(2)), `NatBraiding` (**Examples 3.3(1)**, `ℕ₀ ∪ {∞}`), `Diophantine` (§3.2: **Proposition 3.15**, **Examples 3.16** and **3.17**), `NNReal` (braiding in `ℝ≥0`), `Reals` (**Examples 3.3(2)(3)**), `Dedekind` (**Examples 4.8(4)**, the monoid side), `RealsExtra` (Examples 3.3(3)), `DiophantineExtra` (**Examples 3.16**, **3.17** in full, slack variables) |
| `KappaMonoid/TwoGen/` | Modules | §5: `Forms` (the encoding `α X₁ + β X₂` over `ℕ∞`), `Prelim`, `Lemma52` (**Lemma 5.2**(1)–(5)), `Lemma51` (**Lemma 5.1**), `Realization` (**Theorem 5.3**), `Trace` (**Proposition 5.4**), `Corollary55` (**Corollary 5.5**(1)(2)(3)), `Counterexample` (`ℕ₀² ∪ {∞}`), `Extra` and `ExtraRealization` (the §5 preamble's one-generator criterion, the counterexample's standing hypotheses, the remark before Corollary 5.5) |
| `KappaMonoid/Axioms/` | Mathlib | The one classical result assumed rather than proved — see below |
| `KappaMonoid/Paper/` | everything | The paper's numbered results, and nothing else — see "Reading the formalisation against the paper" |

`Forms`, `Prelim`, `Lemma52` and `Counterexample` are pure monoid theory: §5's braiding material
mentions no module and uses no axiom. The module theory enters at `Lemma51`.

## Reading the formalisation against the paper

`KappaMonoid/Paper/` is what to read with the PDF open; nothing else depends on it.

* `Paper/Section5.lean` restates **every numbered result of §5** in the paper's own terms. Two
  things it adds that the library statements lack. `Setting5` bundles the section's standing
  assumption — *"throughout the section, let `H` be a non-cyclic `ℵ₀`-monoid generated by two
  elements `x₁` and `x₂`"* — which in the library travels as two loose arguments. And
  `IsRealizableAsV` names the nine-line "`H ≅ V^{ℵ₀}(R)` for a ring whose projectives are sums of
  finitely generated modules" that Theorem 5.3 and all three parts of Corollary 5.5 repeat.
* `Paper/Section2.lean`, `Section3.lean` and `Section4.lean` are indices — 212 entries between them,
  one per numbered result, each an `alias` naming the declaration that formalises it and the file
  it lives in. The alias fails to compile if the declaration goes, so the index cannot rot. Each
  closes with what the development deliberately does *not* formalise, and why.
* `Paper/Definition21.lean` and `Paper/Definition218.lean` transcribe **Definitions 2.1** and
  **2.18** literally and prove they agree with the `KMonoid` and `LMonoid` the development works
  with, as equalities of structures.
* `Paper/Section5Extra.lean` collects the unnumbered claims of §5, and `Paper/Examples48.lean` the
  ring-level Examples 4.8(3), which need both `Modules/` and `Examples/`.

`CLAUDE.md` collects what a contributor (human or model) needs before touching the files: the build
commands, the Lean house style, the axiom and deviation discipline, the recurring elaboration traps
of this development, and the workflow that keeps the edit/build loop cheap.

## The assumed result

One classical theorem is taken as an axiom, in `KappaMonoid/Axioms/Modules.lean`. It carries the
standard proof sketch it stands for; assuming a true statement cannot make the development
inconsistent, but a *mis-stated* axiom is false and a false axiom proves everything, so it should
be checked against the literature before it is relied on.

| Axiom | Statement | Used by |
|---|---|---|
| `bergmanDicksData` (A1) | Bergman–Dicks realisation: every reduced commutative monoid with order-unit `u` is `V(R)` for a hereditary `k`-algebra, with `[R] = u` | `corollary_4_7_one_forward`, and `prop_2_16` through Leavitt's theorem |

The list is enforced twice over. `.github/workflows/lean_action_ci.yml` fails if the set of `axiom`
declarations under `KappaMonoid/` differs from the one above, so adding one means editing the
workflow and this table in the same commit. And `KappaMonoid/Paper/AxiomAudit.lean` asserts, for 170
headline results, whether each one uses it — with `#assert_axioms`, a command over `collectAxioms`
that fails both when a result gains an axiom and when it loses one. The claims below are therefore
checked, not merely written.

Two results invoke A1 directly: `corollary_4_7_one_forward`, the implication (i) ⇒ (ii) of
Corollary 4.7(1), and `prop_2_16`, which reaches it through Leavitt's theorem. In §5, Theorem 5.3's
backward direction and all three parts of Corollary 5.5 inherit it from Corollary 4.7(1), and
nothing else does: Lemma 5.1, all of Lemma 5.2, Theorem 5.3's forward direction, both halves of
Proposition 5.4 and the counterexample are axiom-free. So is the rest of §4 — the identification
`V(R) = add [R]` (`addOf_unitClass_eq`), Kaplansky's theorem in its `κ`-monoid form, the other
direction of Corollary 4.7(1), Corollary 4.7(2), Examples 4.8(1) — and so is the whole of §§2.2 and
3, `prop_2_17_one` and Example 2.13's `isFaithful_unitClass` included.

**Leavitt's realisation theorem is a consequence of A1, not a second assumption.** Every cyclic
monoid `C_{m,n}` with `m, n ≥ 1` is the monoid of finitely generated free modules over some ring:
`leavittData` in `KappaMonoid/Modules/Rings/Leavitt.lean`. The deduction uses the part of Bergman's
construction that says which element is the order-unit, `[R] = u`
(`BergmanDicksData.iso_unit`) — without it a realisation `V(R) ≅ M` cannot be turned into a
statement about *free* modules. The rest is bookkeeping: `ForMathlib/CyclicMonoid.lean` builds
`C_{m,n}` as `ℕ₀` modulo the congruence `∼_{m,n}`, which is conical exactly when `m ≥ 1` and has
the class of `1` as an order-unit; A1 realises it; `R^k` is the module realising `k • 1` by
induction from `iso_add` and `iso_unit`; and injectivity of `a ↦ [P a]` turns `R^k ≅ R^l` into
`k ∼_{m,n} l`. `Nontrivial R` falls out of the same injectivity, since `1 ≠ 0` in `C_{m,n}`.

The trade is deliberate: §2.3 rests on Bergman–Dicks, which is a deeper theorem than Leavitt's and
is assumed anyway, rather than on a second assumption. Leavitt's own proof is a seven-page
minimal-counterexample argument on leading terms, it covers only type `(1,k)` — his type `(n,1)`
rings are in the earlier [Leavitt56; Leavitt57] — and even the normal form it computes with is
quoted from those papers rather than proved.

## Classical results proved here

`KappaMonoid/ForMathlib/` proves six things that Mathlib does not have, in files that depend on
nothing else in the development and are the natural shape for upstreaming.

**Hereditary rings** (`Hereditary.lean`). Mathlib has no notion of one. `IsLeftHereditary R` says
every left ideal is projective, `IsRightHereditary R` says every right ideal is — equivalently,
every left ideal of `Rᵐᵒᵖ` — and `IsHereditary R` is both. The development is about *left* modules
and the paper about right ones, so the mirror of the paper's "right hereditary ring" is
`IsLeftHereditary`; that is Corollary 4.7(1)(iii). Bergman's Theorem 6.2 gives a ring hereditary on
*both* sides, and A1 records exactly that (`IsHereditary`), so the "hereditary" of Corollary
4.7(1)(ii) and of the last sentence of Theorem 5.3 is formalised on both sides, as printed. The
side of the modules is moved by passing to the opposite ring, which is again a hereditary
`k`-algebra, and whose left modules are the right modules of the original.

**Invariance of infinite rank** (`FreeRank.lean`). A free module with an infinite basis is not
generated by fewer elements than its rank: `mk_le_of_span_eq_top`. Mathlib's `Module.Basis.le_span`
says the same but assumes `RankCondition R`, which the application here does not have: it covers
finite bases too, where the statement is genuinely about invariant basis number. For an *infinite*
basis nothing beyond nontriviality is needed — each element of a spanning set has finite
`b`-support, the union of those supports covers the basis by linear independence, and a
`#S`-indexed union of finite sets has size at most `#S · ℵ₀ = #S`. The finite-`S` case is vacuous:
the union would be finite and the basis is not. It is stated in the *generation* form rather than
the two-bases form because the complement appearing in Example 2.13 is merely projective, not free,
so there is no second basis to compare against; the familiar two-bases statement is
`mk_eq_mk_of_infinite`, derived from it.

**Uniqueness of the multiplicities of simple modules** (`SimpleMultiplicity.lean`). If
`⨁ A i ≅ ⨁ B j` with all summands simple, each isomorphism class occurs the same number of times
on both sides, infinite multiplicities included: `SimpleMultiplicity.mk_multiplicity_eq`. The
argument is the classical one: apply `Hom_R(S, -)` for a simple `S`. It turns the direct sum into a
direct sum (`HomDirectSum.lean` — Hom out of a *cyclic* module commutes with direct sums, which
Mathlib does not have; it has only the easy direction, Hom out of a sum being a product), each
summand contributes `End_R(S)` or `0` by Schur, and rank over the division ring `End_R(S)` is well
defined. `Module.End R S` acts on `S →ₗ[R] M` on the right, so the rank is taken over
`(Module.End R S)ᵐᵒᵖ`. The converse — that equal multiplicities force an isomorphism — is
`multMap_injective`.

**The classification of cyclic monoids** (`CyclicMonoid.lean`). The map `k ↦ k • u` is either
injective, or its kernel is the congruence `∼_{m,n}` of `C_{m,n}`:
`cyclicMonoidClassification`, and `CyclicRel` lives there too. Mathlib has nothing on the subject —
`IsCyclic` is about groups. The step usually glossed over is made explicit: the set of periods at
`m` is closed under *differences*, not merely under addition, so division with remainder and the
minimality of `n` make it exactly the multiples of `n` — a submonoid of `ℕ` containing `n` would
not be enough. The statement is about the kernel of `k ↦ k • u` for any element of any commutative
monoid, so `prop_2_16` applies it to `u` itself rather than to the submonoid `u` generates.

**Kaplansky's theorem** (`Kaplansky.lean`). Every projective module is a direct sum of countably
generated projective modules: `Module.Projective.exists_directSum_countablyGenerated`.

The argument is the classical one, but it comes out as a single induction rather than two. `P` is
the image of an idempotent `π` on a free module `B →₀ R`. Call a set `S` of coordinates *good* when
the coordinate subspace it spans is `π`-invariant; that is exactly closure under
`b ↦ supp (π (single b 1))`, so one closure operator does the work of the usual alternating closure
under the supports of the `P`- and the `Q`-components. `1 − π` needs no separate step, because
`e_b − π e_b` is supported in `{b} ∪ supp (π e_b)`. The step function has finite values, so the
closure of a *single* coordinate is a countable union of finite sets, hence countable — `Reach`,
`cl` and `iter` in that file.

The chain of good sets then needs no Zorn's lemma either: well-order `B` and take `Jle π b` and
`Jlt π b` to be the closures of `Set.Iic b` and `Set.Iio b`. Closure commutes with unions, so the
chain is increasing and continuous by construction, and the block `Dblock π b` of coordinates new
at stage `b` sits inside the closure of `{b}`, hence is countable. On that block `π` is conjugated
into a fresh idempotent `blockIdem π b` of the free module — idempotent precisely because both
`Jle π b` and `Jlt π b` are good — and `Cpart π b`, its image under `π`, is a complement of
`π (Jlt π b)` inside `π (Jle π b)`. Exhibiting the complement rather than deducing its existence
from projectivity of the successive quotient is what removes the second transfinite induction. It
is projective because `π` is injective on the range of an idempotent of a free module, and
countably generated because the block is; the `Cpart π b` are independent, since the sum of those
below `b` is exactly `π (Jlt π b)`, and their supremum is the whole of `π`'s image.

**Albrecht's theorem** (`Albrecht.lean`). Over a hereditary ring every projective module is a
direct sum of *finitely generated* projective modules: `Albrecht.exists_directSum_fg`.

Two ingredients. First, over a ring all of whose left ideals are projective, a module embedding in
`Rⁿ` is projective (`projective_of_injective_fin`): peel off one coordinate, and the image there is
a left ideal, so the projection splits. Second, Kaplansky's theorem reduces the statement to a
countably generated projective `Q`, which is the image of an idempotent `π` on the free module
`ℕ →₀ R`. Filter that image by `Npart π n`, its part supported on the first `n` coordinates. Each
`Npart π n` is *finitely* generated, because `Fpart R n / Npart π n` is the image of `1 − π` on
`Fpart R n` — finitely generated, hence projective by the first ingredient — so the quotient map
splits and `Npart π n` is a direct summand of `Rⁿ`. And `Npart π (n+1) / Npart π n` embeds in `R`
through the `n`-th coordinate, so it is a finitely generated left ideal: projective again, and that
step of the filtration splits off a finitely generated projective complement. The complements are
independent and sum to the whole image — the same assembly lemma `iSupIndep_of_disjoint_lt` that
Kaplansky's proof uses.

The hypothesis is *left hereditary*, all left ideals projective, which `corollary_4_7_one_forward`
gets from the two-sided `IsHereditary` of A1. Albrecht's own theorem is for semihereditary rings, where
only the finitely generated ideals are assumed projective; that is a genuine strengthening, and the
proof above would need the first ingredient restated for finitely generated submodules to reach it.
Nothing here needs it.

## What is not formalised

* **Remark 3.18** — background from the literature (saturated submonoids of `ℕ₀^n` are the
  finitely generated reduced Krull monoids, Chapman–Krause–Oeljeklaus) and its informal consequence
  for Proposition 3.15; nothing later depends on it.
* **Corollary 4.6** — Corollary 4.5(3) together with six results quoted from the literature, none
  of them monoid-theoretic and none in Mathlib (weakly semihereditary and one-sided semihereditary,
  Bergman; exchange, Warfield; semiperfect, Mueller; weakly noetherian commutative, Hinohara;
  Bézout with one-sided Krull dimension, McGovern–Puninski–Rothmaler). `EveryProjectiveIsSumOfFG`
  in `Modules/Corollary47.lean` names the hypothesis all six supply, and it is what
  `corollary_4_5_three` takes. The *hereditary* case of (2) — Albrecht's theorem, the one §§4–5
  use — is formalised as `corollary_4_6_hereditary`; the other cases stay quoted.
* **Examples 4.8(2), (5)–(7).** Items (1), (3) and (4) are formalised. Item (1) is formalised as
  printed: `krsa_ascent`, `krsa_ascent_free`, `krsa_ascent_iso` are the general `λ⁻` form, from
  which the finite-KRSA and the countable/Kaplansky readings are the cases `λ = ℵ₀` and `λ = ℵ₁`.
  Its closing caution — `⟨V(R)⟩_κ` is braided over `V(R)` but need not be divisor-closed in
  `V^κ(R)` — has its positive half available as `lemma_3_14_sub` applied to `addOf_unitClass_eq`,
  but is not stated at the module level, and the negative half is a remark with no proof in the
  paper. The rest:
  * **(2)** is a question (Herbera–Příhoda–Wiegand, Question 1.1) translated into `κ`-monoid
    language — when is `⟨V(C_fg)⟩_κ` divisor-closed in `V^κ(C)`? — not a claim.
  * **(3)** is formalised at ring level in `Paper/Examples48.lean` (`examples_4_8_3_nat`, `_nnreal`,
    `_rat`, `_diophantine`): for a ring whose projectives are sums of finitely generated ones,
    `V(R) ≅ ℕ₀`, `ℝ≥0`, `ℚ≥0` or a Diophantine monoid (equations and congruences) determines
    `V^{ℵ₀}(R)` as printed.  The inequality case goes through slack variables
    (`LinSystem.exists_withSlack_iso`), as the paper says.
  * **(4)** is formalised on the monoid side in `Examples/Dedekind.lean`: for every abelian group
    `G`, families in `D = {(n, g) ∈ ℕ₀ × G : n ≥ 1 or g = 0}` are braided iff both have finite
    support and equal sums or both have infinite support and equal rank sums
    (`Dedekind.isBraided_iff`), and `E_κ = {(α, g) ∈ F_κ × G : 1 ≤ α < ℵ₀ or g = 0}` is the
    universal `κ`-extension of `D` for every infinite `κ` (`Dedekind.isUniversalKExtension_dedExt`).
    Only Steinitz's theorem `V(R) ≅ D` for a Dedekind domain is quoted.
  * **(5)–(7)** are a survey. Each rests on a classical description of `V(R)` quoted from the
    literature and not in Mathlib — Bass's theorem that
    non-finitely-generated projectives over a connected commutative noetherian ring are free (5),
    Herbera–Příhoda's description of `V^*(R)` for semilocal noetherian `R` (6), Levy–Robson's
    theory of HNP rings (7). For (5) Bass's theorem gives the description directly. For (6) the
    `κ`-monoid step is Proposition 3.15(1), which allows inequalities, and Proposition 3.15(2) is used
    only to recover Herbera–Příhoda's description of `V^{ℵ₀}(R)`; both are formalised. Item (7)
    explicitly declines to carry out its own computation.
* **The remark after Corollary 4.7** (tex 1840) that without the sum-of-finitely-generated
  hypothesis `V(R)` does not in general determine `V^{ℵ₀}(R)` — stated without proof or example.
* **Unnumbered prose of §2**: the remark before Proposition 2.16 that not every cyclic `κ`-monoid
  is a `V^κ(𝓕^κ)` (a consequence of `prop_2_16_iff`, not stated on its own).  See the foot of
  `Paper/Section2.lean`.

## Encoding decisions

**Notation for the three ubiquitous idioms.** Read as the paper writes them:

```lean
ℵ₀∙x    -- KMonoid.cmul ℵ₀ le_rfl x, the paper's ℵ₀x
add(x)  -- KMonoid.addOf at κ = ℵ₀
V(R)    -- projClass R ℵ₀ le_rfl, the paper's V^{ℵ₀}(R)
```

All three are scoped `notation` in namespace `KappaMonoid` rather than definitions: each expands to
exactly the term that would otherwise be written out, so no proof and no lemma statement changes
meaning, and `rw` still matches. Finite multiples are written `n • x`, which
`KMonoid.cmul_natCast` identifies with `cmul (n : Cardinal) _ x`.

The `κ`-monoid structures at the fixed cardinal — `F_{ℵ₀}`, `V^{ℵ₀}(R)`, and products of
`ℵ₀`-monoids — are instances rather than a `letI` threaded through every statement and repeated in
every proof. In `Examples/` the statement-level `letI`s stay even so: there they also pin the
universe of `ℵ₀`, which is otherwise auto-bound afresh in each half of a statement.

**Left modules, right modules.** The paper works with right modules and says "right hereditary";
Mathlib's `Module R` is a left module, so the development works throughout with left modules and
`IsLeftHereditary` for the paper's "right hereditary". The two readings are mirror images of one
another — pass to the opposite ring — so every statement here is the paper's statement for `Rᵒᵖ`.
This is a global convention, not a weakening; where the paper says "hereditary" without a side,
the development says `IsHereditary`.

**`i` and `j` in §5.** The paper's §5 statements are quantified over `1 ≤ i ≠ j ≤ 2`. The library
fixes `i = 1`, `j = 2`, and `Paper.Setting5.swap` exchanges the two generators, which is legitimate
because the standing hypothesis is symmetric in them; `Paper.Setting5.addBase_swap` says the base
`add(x₁ + x₂)` does not move, and `Paper.lemma_5_2_five'`, `lemma_5_2_three'` and `lemma_5_2_four'`
(`Paper/Section5Extra.lean`) are the `i = 2`, `j = 1` instances.

**The §5 preamble's `C ∪ {∞}`.** The preamble says a realisable cyclic `ℵ₀`-monoid has the form
`C ∪ {∞}` for a nonzero cyclic monoid `C`; `TwoGen.ne_nsmul_iff_exists_withTop` asks `C` to be
reduced as well, which the paper leaves implicit: `C ∪ {∞}` is the trivial `ℵ₀`-extension of
Examples 2.3(1), defined only for reduced `C`, and a `κ`-monoid is always reduced (Lemma 2.8).
Among nonzero cyclic monoids this excludes only the groups `C_{0,n}`, `n ≥ 2`.

**Lemma 3.4(3) is stated in the normal form.** The paper concludes *"there exists a limit
well-order on `κ` such that the families are `λ⁻`-braided"*; `isBraided_of_blocks` concludes plain
`IsBraided`, which Lemma 3.5 (`isBraidedOn_iff_isBraided`) shows is the same thing. Its hypothesis
is braidedness of the families cut down to the blocks and padded by zeroes, rather than of families
indexed by `I(l)` and `J(l)`, and the paper's side condition that `|I(l)| = |J(l)|` be infinite is
not needed — so the statement here is the stronger one.

**Lemma 3.7 is proved in two cases.**
 The paper runs one transfinite recursion for every `λ`,
allowing infinite intervals once `λ > ℵ₀`. Here the countable case is that recursion
(`IsBraided.exists_aligned`, `Braiding/TransAleph0.lean`) and the uncountable case goes through
Lemma 3.4(4) and connected components (`IsBraided.exists_aligned_eq_of_ne_aleph0`) — this is the
argument of Remark 3.9, whose own statement is `exists_common_coarsening` — and it proves
more than the lemma asks for: the two partitions of the middle family can be taken *equal*, so the
two cumulative unions coincide rather than merely sandwiching one another.
`IsBraided.exists_aligned_of_data` is the two cases combined, block by block, and
`IsBraided.exists_aligned_cumulative` is the statement as printed,
`⋃_{ν ≤ μ} J_ν ⊆ ⋃_{ν ≤ μ} J'_ν ⊆ ⋃_{ν ≤ μ+1} J_ν`, over the limit well-order `kOrd` on `ι × ℕ`
— which by Lemma 3.5 is no loss of generality.

**`<λ`-generated, not `λ⁻`-small, in Corollaries 4.4 and 4.5.** Definition 4.1's `λ⁻`-small is
what Theorem 4.3 needs; Corollaries 4.4 and 4.5 are about the modules generated by strictly fewer
than `λ` elements, which the paper writes `C_{λ⁻}` and `V^{λ⁻}(R)`. The two notions are separate
declarations here — `IsLambdaSmall` and `IsLambdaGenerated`, with `C.lambdaSmallPart` and
`C.lambdaGenPart` the corresponding subclasses. `<λ`-generated implies `λ⁻`-small for regular `λ`
(`IsLambdaGenerated.isLambdaSmall`, the paper's Example 4.2(2)), which is how Corollary 4.4
reduces to Theorem 4.3; for a *projective* module over any ring the two coincide
(`projClass_lambdaSmallPart_eq_lambdaGenPart`), which is how Kaplansky's theorem feeds
Corollary 4.5.

**`V^{ℵ₀}(R)` in Corollary 4.7(2)** is `(projClass R κ hκ).lambdaGenPart ℵ₁`, the classes of the
countably generated projective modules inside `V^κ(R)`, and `add_{ℵ₀}(x)` carries the `ℵ₁⁻`-monoid
structure of `KMonoid.addOfCard_isLSubset_succ`. The isomorphism the corollary asserts is one of
`ℵ₁⁻`-monoids, which — since `ℵ₁ = ℵ₀⁺` — is what an isomorphism of `ℵ₀`-monoids is. The
identification that makes both directions work is `addOfCard_unitClass_eq`:
`add_{ℵ₀} [R] = V^{ℵ₀}(R)`, the countable analogue of `V(R) = add [R]`.

**Index sets: arbitrary types, not the cardinal.** The paper indexes by the von Neumann
cardinal `κ` itself. Here the summation operation is applied directly to a family indexed by
an *arbitrary* type of the right size:

```lean
lsumOf : ∀ {ι : Type u}, #ι < lam → (ι → X) → X
```

Consequently the reindexing law (A3) is an axiom rather than a theorem, and nothing has to be
transported along a chosen bijection. `Idx κ := κ.ord.toType` survives only as a convenient
`κ`-sized index type for the constructions of §3 and §4, which really do produce `κ`-indexed
data; `KMonoid.ksum` is the specialisation of `sumOf` to it.

**One theory, not two.** A `κ`-monoid is exactly a `λ⁻`-monoid for `λ = κ⁺` (this is
Remark 2.19: `#ι ≤ κ ↔ #ι < κ⁺`, and `κ⁺` is regular). So `KMonoid κ H` is declared as
`extends LMonoid (Order.succ κ) H`, the whole of §2 is proved once for `λ⁻`-monoids, and the
`κ`-level names (`sumOf`, `ksum`, `cmul`, …) are a thin layer on top. Notably:

* the `λ⁻`-analogues of `sumOf_sigma`, `sumOf_extend`, … are not separate developments;
* `LMonoid.ofLE` (a five-line restriction along `λ ≤ λ'`) subsumes the first half of Remark 2.19
  in general; the converse half — compatible `λ`-monoid structures for all infinite `λ < κ` define
  a `κ⁻`-monoid — is `LMonoid.ofCompatible` (`Core/Compatible.lean`), with both round trips. It
  assumes `κ > ℵ₀`, which the paper does not say: at `κ = ℵ₀` there is no infinite `λ < κ`, so the
  family is empty, while an `ℵ₀⁻`-monoid is an arbitrary commutative monoid;
* only genuinely `κ`-specific statements — Lemma 2.8, which needs a largest admissible
  cardinal — are proved at the `κ`-level.

The same identification is why §3's standing hypothesis reads `λ ≤ κ⁺`: `hlk : lam ≤ Order.succ κ`
throughout `Braiding/` and `Modules/`. All that is ever made of it is
`KappaMonoid.le_of_lt_of_le_succ`, that a family indexed by fewer than `λ` elements is indexed by at
most `κ`. The bound is strictly weaker than `λ ≤ κ`, and the difference is load-bearing: at
`κ = ℵ₀` it admits `λ = ℵ₁`, which is the case Kaplansky's theorem supplies, so Corollary 4.5(2)
and Proposition 3.15(1) hold for every infinite `κ` rather than only for `κ ≥ ℵ₁`.

**No junk convention.** Definition 2.18 gives a *partial* operation, defined on families with
support of size `< λ`. That is modelled by restricting the *index type*, not by extending the
operation to all families with a junk value: `lsumOf` simply takes `#ι < λ` as a hypothesis.

**The additive monoid.** By Lemma 2.5 a `λ⁻`-monoid carries a canonical commutative monoid
structure with `a + b = Σ²(a,b)`. Following Mathlib's forgetful-inheritance convention,
`LMonoid` *extends* `AddCommMonoid` and adds the compatibility axiom `add_eq_lsumOf`; this
avoids a second, merely propositionally equal `+` on types that already have one (e.g. `ℕ`
as an `ℵ₀⁻`-monoid). Nothing is lost:

* `SumData` is the bare data (summation only, no `0`, no `+`), and `SumData.toLMonoid`
  constructs the additive structure from it — this *is* Lemma 2.5, and it is short: the
  associativity of `+` is `sum_sigma` for a three-element index type;
* `BareKMonoid` + `KMonoid.ofBare` do the same starting from `Idx κ`-indexed data satisfying
  (A1) and (A2) only, which is what §3 and §4 supply. The one non-formal ingredient is that
  a zero-padded sum does not depend on the chosen embedding into `Idx κ`; this is proved by
  moving both embeddings into the first "row" of a bijection `κ × κ ≃ κ`, where the two
  ranges have equinumerous complements and hence differ by a permutation.

**(A1) at every index.** The paper states (A1) at the distinguished element `0 ∈ κ`. Here it
is `lsumOf_unique`: a sum over a one-point index type is its unique entry. No distinguished
element is needed, and the axiom does not mention `0`.

**Faithfulness to Definition 2.1.** Since none of the three deviations above is word-for-word
the paper's definition, `PaperKMonoid` transcribes Definition 2.1 literally — a `Zero`, a map
`Σ : H^κ → H`, (A1) at one distinguished index, (A2) for every bijection `κ × κ ≃ κ` — and the
two notions are shown to agree:

* `PaperKMonoid.toKMonoid` — the paper's axioms give a `KMonoid`. The work is
  `PaperKMonoid.sigma_perm` (this is (A3), and it is where (A1) at the distinguished index is
  used) and `PaperKMonoid.sigma_single`, which upgrades (A1) to every index by transporting
  along a transposition.
* `KMonoid.toPaper` — conversely, and taking any index as the distinguished one.
* `PaperKMonoid.toKMonoid_ksum`, `KMonoid.toPaper_sigma` and
  `KMonoid.toPaper_toKMonoid_ksum` — the translations leave `0` and `Σ` unchanged, and
  `PaperKMonoid.toKMonoid_sumOf` / `toKMonoid_add` express the reconstructed sums and addition
  back in terms of `Σ`, so nothing is added by the reconstruction.

**The limit well-order, and why the normal form is not a choice.** Definition 3.1 fixes a limit
well-order on `κ` — a well-order in which every element has a successor, i.e. with no maximum —
and speaks of `μ + 1` and of limit elements. Rather than carry an abstract well-order plus a
successor function plus the predicate "is a limit" through every statement, `BraidingData` uses the
canonical normal form: a limit well-order decomposes into `ω`-blocks indexed by its limit elements,
so braiding partitions and braiding families are indexed by `ι × ℕ`, with `bsucc (a, n) = (a, n+1)`
and limit elements `(a, 0)`. That keeps `BraidingData` a plain structure with no order-theoretic
side conditions, and the whole of §3 is proved against it.

**That this loses nothing is proved, not assumed** — it is Lemma 3.5, in
`Braiding/WellOrder.lean`:

* `LimitSucc M` is the combinatorial content of a limit well-order on `M`: an injective successor
  whose image is exactly the non-limit elements, whose iterates from the limit elements exhaust
  `M`. `LimitSucc.ofWellOrder` builds one from any `LinearOrder` + `WellFoundedLT` + `NoMaxOrder`
  (the successor being the least element above, `wsucc`), and `LimitSucc.prodNat` is the normal
  form. `LimitSucc.blockEquiv` is the `ω`-block decomposition `Lim × ℕ ≃ M`.
* `BraidingDataOn lam W x y` is Definition 3.1(1) *verbatim* over such an index structure `W`, and
  `BraidingData` is the case `W = LimitSucc.prodNat ι`.
* `isBraidedOn_iff_isBraided` — **Lemma 3.5** — says that for any `W` on a set of the same
  cardinality as the index set, `IsBraidedOn lam W x y ↔ IsBraided lam x y`; `isBraidedOn_congr_self`
  is the paper's phrasing, that two limit well-orders on `κ` define the same relation, and
  `isBraidedOn_ofWellOrder_iff` is the form taking the order from the instances on `ι`.

Everything rests on one construction, `BraidingDataOn.comap`: braiding data pushes forward along
any map `Φ` of index structures that commutes with the successor, reflects limit elements and has
finite fibres, by taking unions and sums over the fibres. Both directions of Lemma 3.5 are
instances — the forward one reads off block and offset, the backward one either relabels block by
block (when there are `#ι` blocks) or folds all of `ι × ℕ` into one block along the anti-diagonal
`(a, n) ↦ e a + n + 1` (when there are finitely many, so that `ι` is countable). That second case
is the paper's diagonal argument; the `+ 1` is what keeps the new `v` zero at the limit element,
which in the paper is the step "keeping in mind `v_{l_i} = 0`". Unlike the paper's proof, none of
this splits on whether `λ` is countable.

**Lemma 3.4(2)(3)** is in the same file, and says the same thing from the other side: a braiding
*is* a disjoint union of `ω`-block braidings. `BraidingData.isBraided_block` restricts a braiding
to the block of one limit element — keep the partitions, zero the braiding families off the block,
and every equation off it reads `0 = 0 + 0` — and `isBraided_of_blocks` assembles a braiding from
one per piece of a pair of indexed partitions of the index set, by taking `ι × ι` as the block set
(the paper's lexicographic well-order on the pairs `(l, μ)`) and coming back to the normal form
through Lemma 3.5. The paper indexes the restricted families by the blocks themselves and so needs
`|I(l)| = |J(l)|` infinite for Definition 3.1 to apply to them; here they are padded by zeroes to
the ambient index set — which is what part (2) asks for anyway — so part (3) is the exact converse
of part (2) and needs no such hypothesis.

**The test universe of `IsUniversalKExtension` is a parameter.** Examples 4.8(1) concludes
`V^κ(C) ≅ F_κ(B)` across a universe gap: `F_κ(B)` is cut out of `B → F_κ`, so it lives in
`Type (u+1)`, while `V^κ(C)` lives in `Type u`. The `universal` field therefore quantifies over
test objects in a universe of its own — Lean cannot quantify over universes inside a term, so this
is the only way to say "for every `κ`-monoid `K`" — and `isUniversalKExtension_unique'` compares
extensions across universes. Both sides of Examples 4.8(1) are universal at both universes, since
`krsa_ascent` delivers a *braiding* and a braiding is universal at every test universe
(`IsBraidedOver.isUniversalKExtension`). The price is that statements mentioning
`IsUniversalKExtension` must pin the test universe explicitly, as it appears in no argument (trap 8
in `CLAUDE.md`).

**Classes of modules.** There is no type of all `R`-modules, so `ModuleClass R κ` bundles a
type `carrier` of isomorphism classes, chosen representatives `rep a`, the requirement that
distinct classes are non-isomorphic, and closure under `κ`-indexed direct sums. That is exactly
Definition 2.4. `V^κ(C)` is `carrier`, and `ModuleClass.instKMonoid` verifies (A1) and (A2) from
the corresponding isomorphisms of direct sums. `V^{λ⁻}(Cλ⁻)` is the subset
`lambdaSmallPart`, made into an `LMonoid` via `IsLSubset.lmonoid`.

**Closure under summands is separate.** Section 4 additionally needs the class to be closed
under direct summands, but §2.3's class of *free* modules is not — a summand of a free module is
projective, not free — so `V^κ(𝓕^κ)` could not be a `ModuleClass` if that were a field. It is
therefore the class `ModuleClass.IsSummandClosed`, which `V^κ(R)` supplies and `V^κ(𝓕^κ)` does
not. Being a class it threads through the recursion of Theorem 4.3 by instance resolution: one
`variable [C.IsSummandClosed]` before `exists_step` covers everything downstream, and only the
four public §4 theorems carry it explicitly.

**Ranks by subsets, not cardinals.** The classes of `V^κ(𝓕^κ)` are indexed by subsets of
`Idx κ` rather than by the cardinals `≤ κ`, because `ModuleClass.carrier` must live in `Type u`
whereas `Cardinal.{u}` lives in `Type (u+1)`. The same constraint is why the `n` coordinates of
`Fin n → K` in Proposition 2.17(2) are a per-index type synonym `Coord K n i`: they carry `n`
different module structures over one ring, which instance resolution cannot separate if the
types coincide.

**Theorem 4.3, two forms.** `theorem_4_3_core` is the mathematical content — given
`⨁_{i∈κ} A i ≅ ⨁_{j∈κ} B j` with all summands `λ⁻`-small, the families of classes are
`λ⁻`-braided. `theorem_4_3` packages it as `IsBraidedOver` for the generated
`κ`-submonoid, and `corollary_4_4` gives the "in particular" plus the universal-extension
conclusion. Splitting it this way keeps the transfinite recursion (the actual work) free of
subtype and instance plumbing.

## Building

The toolchain and Mathlib are both pinned to `v4.33.0` (`lean-toolchain` and the `rev` in
`lakefile.toml`), so a fresh checkout builds the same way tomorrow as today:

```
lake exe cache get   # Mathlib's build artefacts; fetches the pinned dependency first
lake build           # the root target, KappaMonoid
```

`lake update` is not part of the normal flow. Bumps are taken deliberately, through
`.github/workflows/update.yml` (`mathlib-update-action`, triggered by hand): it opens a pull request
for a new Mathlib tag and files an issue if the update does not build.

CI (`.github/workflows/lean_action_ci.yml`) does four things on every push: it builds the root
target, fails if any declaration in it uses `sorry`, runs `scripts/check_layering.sh`, and fails if
the set of `axiom` declarations under `KappaMonoid/` differs from the one in the table above.
Documentation is generated by `docgen-action`.

`scripts/check_layering.sh` is what keeps the layers honest — Lake resolves modules package-wide,
so `Core/` importing `Modules/` would build fine. It checks the import discipline between layers,
that no module theory appears below `Modules/`, and that only `Axioms/*` and `Modules/Small.lean`
import all of Mathlib.
