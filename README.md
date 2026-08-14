# A Lean 4 formalisation of Nazemian–Smertnig, *A monoid-theoretical approach to infinite direct-sum decompositions of modules*

Sections 2–5 of the paper.

## Status

Complete and `sorry`-free: `lake build` checks every definition and every theorem, including
Theorem 3.11 (universal `κ`-extensions), Proposition 3.14 (universal extensions of Diophantine
monoids), Theorem 4.3 (`V^κ(C)` is `λ⁻`-braided over `V^{λ⁻}(C_{λ⁻})`), Theorem 5.3 (which
two-generated `ℵ₀`-monoids are `V^{ℵ₀}(R)` for a hereditary ring) and all of §§2–5.

The development is layered by subject, and each layer is an entry point of its own: importing
`KappaMonoid.Core` or `KappaMonoid.Braiding` gets the monoid theory without the module theory, the
assumed classical results, or — since the core no longer says `import Mathlib` — most of Mathlib.
`scripts/check_layering.sh` enforces this in CI; Lake would not.

| Layer | Depends on | Contents |
|---|---|---|
| `KappaMonoid/ForMathlib/` | Mathlib | No `κ`-monoid content and no dependence on the rest, so it compiles once: `TraceIdeal.lean` (Mathlib has no trace ideal — `Module.trace` is the trace of an endomorphism), `NatBlocks.lean` (`Nat.blockIdx`, cutting `ℕ` into consecutive blocks), `Finprod.lean` |
| `KappaMonoid/Core/` | ForMathlib | §2: `Index`, `SumData`, `LMonoid` (= `λ⁻`-monoid) and `KMonoid` with the whole sum API, cardinal scalar multiplication and reducedness (Lemmas 2.7, 2.8), `Subobject` (homomorphisms, `⟨S⟩_κ`, induced structures), `Bare` (`KMonoid.ofBare`, Lemma 2.5), `LHom`, `Cardinal` (`F_{λ⁻}`, `F_κ`), `Free` (**Proposition 2.9**), `OrderUnit` (Defs. 2.11–2.12, **Lemma 2.14**), `Cyclic` (**Lemma 2.15**), `AddOf` (`add x`, `add_λ x`) |
| `KappaMonoid/Braiding/` | Core | §3: `Defs` (Definition 3.1(1), Lemma 3.6), `TransAleph0` (Lemmas 3.7, 3.8 for `λ = ℵ₀`), `Sums` (**Lemma 3.2**, Lemma 3.4), `TransUncountable`, `Over` (Definition 3.1(2)), `UnivAux`, `Prop39` (**Proposition 3.9**, Definition 3.10), `UnivExt` (**Theorem 3.11** and its converse), `Saturated` (**Lemma 3.13**) |
| `KappaMonoid/Modules/` | Braiding, Axioms | Definition 2.4 and §4: `Small` (Definition 4.1), `DirectSum`, `Class` (`ModuleClass`, `V^κ(C)`), `Theorem43` (**Theorem 4.3**, Cor. 4.4), `SmallPart`, `Projective` (Cor. 4.5, Kaplansky, the Cor. 4.6 stub), `Corollary47` (`V(R) = add [R]`, **Corollary 4.7**, **Examples 4.8(1)**), and `Rings/` — the §2.2–2.3 ring examples: `ProjOrderUnit.lean` (**Example 2.13**), `FreeModules.lean` (`V^κ(𝓕^κ)`), `FreeUnit.lean` (ranks), `Realisation.lean` (**Proposition 2.16**), `Semisimple.lean` (**Proposition 2.17**) |
| `KappaMonoid/Examples/` | Braiding | `TrivExt` (**Examples 2.3(1)**), `ENNReal` (2.3(2)), `Diophantine` (**Examples 3.3(1)**, §3.2: **Proposition 3.14**, **Example 3.15**), `Reals` (**Examples 3.3(2)(3)**) |
| `KappaMonoid/TwoGen/` | Modules | §5: `Forms` (the encoding `α X₁ + β X₂` over `ℕ∞`), `Prelim`, `Lemma52` (**Lemma 5.2**(1)–(5)), `Lemma51` (**Lemma 5.1**), `Realization` (**Theorem 5.3**), `Trace` (**Proposition 5.4**), `Corollary55` (**Corollary 5.5**(1)(2)(3)), `Counterexample` (`ℕ₀² ∪ {∞}`) |
| `KappaMonoid/Axioms/` | Mathlib | The four classical results assumed rather than proved, split by layer: `Monoid` (A2, A4), `Modules` (A5, A6) — see below |
| `KappaMonoid/Paper/` | everything | The paper's numbered results, and nothing else — see "Reading the formalisation against the paper" |

`Forms`, `Prelim`, `Lemma52` and `Counterexample` are pure monoid theory: §5's braiding material
mentions no module and uses no axiom.  The module theory enters at `Lemma51`.

**Section 2 is complete.** Every definition, example, lemma and proposition of §2 is stated and
proved, `sorry`-free, subject only to the two §2 axioms below (A2 and A4; A5 is used nowhere in the
checked build).  A1 and A3 were assumed until they were proved — see "The assumed results".

**Section 3 is complete.** Every definition, lemma, proposition and example of §3 is stated and
proved, `sorry`-free and axiom-free — including Theorem 3.11 and its converse, all of Examples 3.3,
Examples 3.12, Lemma 3.13, Proposition 3.14 and Example 3.15. Two deliberate omissions are
documented: Lemma 3.4(2)(3) and Lemma 3.5 (the `ι × ℕ` normal form *is* their content, see the
"limit well-order" note) and Remark 3.16 (a pointer to the literature). Proposition 3.14(2) carries one added
hypothesis — the saturation of `H`, which the paper claims is automatic but is not for systems with
inequalities; it *is* automatic without them, so the inequality-free case
(`prop_3_14_two_of_ineqs_empty`) is the paper's statement verbatim. See "The hypothesis added to
Proposition 3.14(2)" below.

**Section 4 is complete.** Definition 4.1 through Examples 4.8(1) are stated and proved. Corollary
4.7(1) is an equivalence: (iii) ⇒ (i) is Corollary 4.5(3) moved along the identification
`V(R) = add [R]` (`addOf_unitClass_eq`) and needs no axiom; (i) ⇒ (ii)
(`corollary_4_7_one_forward`) is the only result in the build that uses Bergman–Dicks realisation,
axiom A5 below. Corollary 4.7(2) needs no axiom either — Corollary 4.5(2) plus uniqueness of
universal `κ`-extensions. Corollary 4.6 is Corollary 4.5(3) together with six results quoted from
the literature, none of them monoid-theoretic and none in Mathlib, so it stays a documented stub in
`Modules/Projective.lean`. Examples 4.8(1) is proved in a corrected form, for a universe reason: see "The
statement corrected in Examples 4.8(1)" below.

**Section 5 is complete.** Every lemma, theorem, proposition and corollary of §5 is stated and
proved, `sorry`-free. Theorem 5.3 and Corollary 5.5 use no axiom beyond A5, which enters through
Corollary 4.7(1); Proposition 5.4 and its hereditary half use none at all. Six statements needed
correcting before they could be proved — the scaffold had dropped hypotheses that the paper's
standing assumptions supply, and in two places the quantifier was too wide; all six are recorded in
"The statements corrected in Section 5" below.

## Reading the formalisation against the paper

`KappaMonoid/Paper/` is what to read with the PDF open; nothing else depends on it.

* `Paper/Section5.lean` restates **every numbered result of §5** in the paper's own terms and
  discharges it from `TwoGen/`.  Two things it adds that the library statements lack.  `Setting5`
  bundles the section's standing assumption — *"throughout the section, let `H` be a non-cyclic
  `ℵ₀`-monoid generated by two elements `x₁` and `x₂`"* — which in the library travels as two loose
  arguments, and which the scaffold dropped from Lemma 5.2(3) and 5.2(4): two of the six corrected
  statements below were exactly that mistake.  And `IsRealizableAsV` names the nine-line
  "`H ≅ V^{ℵ₀}(R)` for a ring whose projectives are sums of finitely generated modules" that
  Theorem 5.3 and all three parts of Corollary 5.5 repeat.
* `Paper/Section2.lean`, `Section3.lean` and `Section4.lean` are indices — 97 entries between them,
  one per numbered result, each an `alias` naming the declaration that formalises it and the file
  it lives in.  The alias fails to compile if the declaration goes, so the index cannot rot the way
  the tables in this file did.  Each closes with what the development deliberately does *not*
  formalise, and why: Lemma 3.4(2)(3), Lemma 3.5, Remark 3.16, Corollary 4.6, Examples 4.8(2).
* `Paper/Definition21.lean` transcribes **Definition 2.1** literally and proves it agrees with the
  `KMonoid` the development works with.

## Conventions

`CLAUDE.md` collects what a contributor (human or model) needs before touching the files: the build
commands, the Lean house style, the axiom and deviation discipline, the recurring elaboration traps
of this development, and the workflow that keeps the edit/build loop cheap. The plan documents —
`SECTION{3,4,5}-PLAN.md` for the sections, `REFACTOR-PLAN.md` for the reorganisation — defer to it
and only record what is specific to their subject.

## The assumed results

Four classical theorems are taken as axioms in `KappaMonoid/Axioms/`, split by layer —
`Monoid.lean` (A2, A4) and `Modules.lean` (A5, A6), so that a file needing only the
monoid-theoretic assumptions does not import the module-theoretic ones.  Each carries the standard
proof sketch it stands for:

| Axiom | Statement | Used by |
|---|---|---|
| `leavittData` (A2) | Leavitt's realisation of the cyclic monoids `C_{m,n}` | `prop_2_16` |
| `cyclicMonoidClassification` (A4) | every cyclic monoid is `ℕ₀` or `C_{m,n}` | `prop_2_16` |
| `bergmanDicksData` (A5) | Bergman–Dicks realisation: every reduced commutative monoid with order-unit is `V(R)` for a hereditary `k`-algebra. Bundled with the hereditary case of Cor. 4.6, since Cor. 4.7(1) uses the two together | `corollary_4_7_one_forward` |
| `kaplansky_classical` (A6) | Kaplansky's theorem: every projective module is a direct sum of countably generated projective modules | `kaplansky`, and through it Cor. 4.5 and Cor. 4.7 |

The list is enforced twice over. `.github/workflows/lean_action_ci.yml` fails if the set of `axiom`
declarations under `KappaMonoid/` differs from the four above, so adding one means editing the
workflow and this table in the same commit. And `KappaMonoid/Paper/AxiomAudit.lean` asserts, for 43
headline results, exactly which of the four each one uses — with `#assert_axioms`, a command over
`collectAxioms` that fails both when a result gains an axiom and when it loses one. The paragraphs
below are therefore checked, not merely written.

**A1 was the sixth, and is now proved.**  Invariance of infinite rank — a free module with an
infinite basis is not generated by fewer elements than its rank — is `mk_le_of_span_eq_top` in
`KappaMonoid/ForMathlib/FreeRank.lean`.  Mathlib's `Module.Basis.le_span` says the same but assumes
`RankCondition R`, which the application here does not have: it covers finite bases too, where the
statement is genuinely about invariant basis number.  For an *infinite* basis nothing beyond
nontriviality is needed, and the proof is the support argument the axiom's docstring described —
each element of a spanning set has finite `b`-support, the union of those supports covers the basis
by linear independence, and a `#S`-indexed union of finite sets has size at most `#S · ℵ₀ = #S`.
The finite-`S` case is vacuous: the union would be finite and the basis is not.

It is stated in the *generation* form rather than the two-bases form because the complement
appearing in Example 2.13 is merely projective, not free, so there is no second basis to compare
against; the familiar two-bases statement is `mk_eq_mk_of_infinite`, derived from it.  The file
depends on nothing in this development and is the natural shape for upstreaming: a
`RankCondition`-free `Basis.le_span` for infinite bases.

**A3 was the fifth, and is now proved too.**  Uniqueness of the multiplicities of simple modules —
if `⨁ A i ≅ ⨁ B j` with all summands simple, each isomorphism class occurs the same number of
times on both sides, infinite multiplicities included — is
`SimpleMultiplicity.mk_multiplicity_eq` in `KappaMonoid/ForMathlib/SimpleMultiplicity.lean`.  The
argument is the classical one: apply `Hom_R(S, -)` for a simple `S`.  It turns the direct sum into
a direct sum (`ForMathlib/HomDirectSum.lean` — Hom out of a *cyclic* module commutes with direct
sums, which Mathlib does not have; it has only the easy direction, Hom out of a sum being a
product), each summand contributes `End_R(S)` or `0` by Schur, and rank over the division ring
`End_R(S)` is well defined.  `Module.End R S` acts on `S →ₗ[R] M` on the right, so the rank is
taken over `(Module.End R S)ᵐᵒᵖ`.

The assumptions are contained.  `#print axioms prop_2_16` reports exactly A2 and A4; and
`prop_2_17_one`, along with Example 2.13's `isFaithful_unitClass`, now reports **no axiom at all** —
which is what retiring A1 and A3 bought.
Note that `multMap_injective` needs *no* axiom: the converse of A3 — that equal multiplicities
force an isomorphism — is proved, not assumed.  **Everything else — including
Theorems 3.11 and 4.3, Proposition 2.9, Lemmas 2.14 and 2.15, and even
`Projective.isOrderUnit_unitClass` — depends only on `propext`, `Classical.choice` and
`Quot.sound`.**

A5 is used by exactly one result: `corollary_4_7_one_forward`, the implication (i) ⇒ (ii) of
Corollary 4.7(1). Everything else in §4 — including the identification `V(R) = add [R]`
(`addOf_unitClass_eq`), the other direction of Corollary 4.7(1), Corollary 4.7(2) and Examples
4.8(1) — reports only `propext`, `Classical.choice` and `Quot.sound`.

## The hypothesis added to Theorem 3.11

Theorem 3.11(1) asserts, for an arbitrary `λ⁻`-monoid `H`, the existence of a `κ`-monoid
`Ĥ ⊇ H` which is a `λ⁻`-overmonoid of `H`. But Lemma 2.8(1) says every `κ`-monoid is
reduced, and a `λ⁻`-submonoid of a reduced monoid is reduced. So no non-reduced `H` can
admit such an `Ĥ`. For `λ = ℵ₀` a `λ⁻`-monoid is just a commutative monoid, and `H = ℤ` is
a counterexample: the construction `Ĥ = H^κ/≈` still goes through as a `κ`-monoid, but the
map `H → Ĥ` is not injective, so `Ĥ` is not an *over*monoid.

`theorem_3_11` therefore adds `IsConical X` (= reduced, = conical), and three facts pin the
hypothesis down exactly:

* `isConical_of_isUniversalKExtension` — reducedness is *necessary*: any `λ⁻`-monoid
  admitting an injective `λ⁻`-homomorphism into a `κ`-monoid is reduced.
* `UnivExt.of_injective` — reducedness is *sufficient* for the point where it is needed,
  namely injectivity of `x ↦ [(x,0,0,…)]`. The argument: in a braiding of `(x,0,0,…)` with
  `(y,0,0,…)`, all but at most one of the defining equations reads `0 = v μ + u μ`, so
  reducedness kills those `u`'s and `v`'s, and the surviving equations give `x = y`.
* `theorem_3_11_of_aleph0_lt` — for `λ > ℵ₀` the hypothesis is automatic, so the statement is
  the paper's verbatim. This rests on `LMonoid.isConical`, the analogue of Lemma 2.8(1) for
  `λ⁻`-monoids, which the paper asserts at the end of §2.4.

So the deviation from the paper is confined to `λ = ℵ₀`, which is (per Lemma 3.4(4)) the
interesting case. Example 2.3(1) already flags reducedness as necessary in exactly this
situation, so this looks like an omission in transcription rather than an error in the
mathematics.

## The hypothesis added to Proposition 3.14(2)

The remark before Proposition 3.14 asserts that a submonoid of `ℕ₀^n` defined by homogeneous
linear equations, inequalities and congruences is saturated, by cancellativity of `ℕ₀^n`. For
equations and congruences that is right — cancel the `t`-part — but for inequalities it is false,
and Proposition 3.14(2), whose proof opens by invoking it, fails with it. Take
`H = {(a,b) ∈ ℕ₀² : a ≤ 2b}`, cut out by the single inequality `x₁ ≤ 2x₂`. Then

* `(2,1) = (0,1) + (2,0)` with `(2,1)`, `(0,1) ∈ H` and `(2,0) ∉ H`, so `H` is not saturated
  (`not_isSaturatedFin_ineqSystem`);
* the families `x_k = (2,1)` and `y_0 = (0,1)`, `y_k = (2,1)` for `k ≥ 1` have the same
  `ℵ₀`-sum `(ℵ₀, ℵ₀) ∈ H + ℵ₀H` but are not `ℵ₀⁻`-braided over `H`: telescoping the braiding
  equations along the `ω`-block carrying `y`'s index `0` forces a deficit `v = (2p-2, p)` with
  `p ≥ 1`, and then the next `u` would have to be `(2m-2p+2, m-p)`, which is never in `H`. So by
  `isBraidedOver_of_isUniversalKExtension`, `H + ℵ₀H` is *not* the universal `ℵ₀`-extension of
  this `H`.

`prop_3_14_two` therefore takes the saturation of `H` as a hypothesis (`IsSaturatedFin`), which is
exactly what Lemma 3.13(2) needs. Only the failure of saturation is formalised; the braiding
computation is recorded in the docstring of `not_isSaturatedFin_ineqSystem`.

For a system of **equations and congruences** the paper's argument is correct and the hypothesis
costs nothing: `isSaturatedFin_of_ineqs_empty` proves it (all values in a finite solution are
finite, so every linear form has a natural-number shadow and the cancellation happens in `ℕ₀`),
and `prop_3_14_two_of_ineqs_empty` is Proposition 3.14(2) for such a system with no hypothesis
beyond `sys.ineqs = ∅`. So the correction to the paper is confined to inequalities.

## Examples 4.8(1), and the universe that used to block it

Examples 4.8(1) concludes `V^κ(C) ≅ F_κ(B)`. That isomorphism was **not expressible** until the
universal property was generalised, and the README recorded it as a deviation. `F_κ(B)` is cut out
of `B → F_κ`, so it lives in `Type (u+1)`, while `V^κ(C)` lives in `Type u`; the `universal` field
of `IsUniversalKExtension` quantified over test objects in the *extension's own* universe, so
`isUniversalKExtension_unique` could compare two extensions in one universe only, and the two sides
of the isomorphism were incomparable.

The test universe is now a **parameter** of `IsUniversalKExtension` — Lean cannot quantify over
universes inside a term, so this is the only way to say "for every `κ`-monoid `K`" — and
`extend_lhom` was generalised to match, which cost nothing: its proof never used the restriction.
Both sides are then universal at both universes, since `krsa_ascent` delivers a *braiding* and a
braiding is universal at every test universe (`IsBraidedOver.isUniversalKExtension`), and
`isUniversalKExtension_unique'` compares extensions across universes.

So the deviation is gone. `krsa_ascent_iso` is the paper's statement, and `krsa_ascent_free` — the
`B`-indexed universal property, every map `B → K` extending uniquely along the generators, now for
`K` in **any** universe — is the stronger companion. The price is that statements mentioning
`IsUniversalKExtension` must pin the test universe: it appears in no argument, so Lean would leave
it a metavariable (trap 5 in `CLAUDE.md`). That is why `isBraidedOver_of_isUniversalKExtension`,
`lemma_3_13_free` and their kin now carry explicit `.{u, v, w, t}` annotations.

## The statements corrected in Section 5

Section 5 was scaffolded before it was proved, and six of its statements had to be corrected on the
way. Each correction is also recorded in the docstring of the affected result.

**Hereditariness is carried together with `EveryProjectiveIsSumOfFG R`** — in Theorem 5.3,
Proposition 5.4's hereditary half and all three parts of Corollary 5.5. Both directions of the
paper's proofs reach `R` only through Corollary 4.6: over a hereditary ring every projective module
is a direct sum of finitely generated ones. That implication is a quoted result (Albrecht; Bergman),
not monoid theory and not in Mathlib, so this development does not derive it — it is bundled into
the Bergman–Dicks data of axiom A5, as `BergmanDicksData.sumOfFG`, for the ring A5 produces. It is
therefore not recoverable from `∀ I : Ideal R, Module.Projective R I` inside the formalisation. For
a hereditary ring the extra conjunct is automatic, so the statements are the paper's; making it
explicit is the same treatment Corollary 4.6 already gets in `Modules/Projective.lean`, where it is a
documented stub rather than a formalised implication. `corollary_4_7_one_forward` was extended to
return it, which it can because axiom A5 supplies it.

**Lemma 5.2(3) and 5.2(4) take the generation hypothesis `hgen`.** It is a standing assumption of
§5 ("let `H` be a non-cyclic `ℵ₀`-monoid generated by two elements") and both proofs genuinely need
it: in 5.2(3) it is where `t = m' x_i + n' x_j` comes from, and in 5.2(4) it is what lets
`v (a, K+1)` be written in a form at all.

**Corollary 5.5(1)'s condition is quantified over both orderings of the generators.** The paper
writes it for `1 ≤ i ≠ j ≤ 2`, so each of its two clauses has two instances; the scaffold kept only
one of each, and both are needed. Without the `X₂`-half of the first clause a finite and an infinite
form could share a value, so condition (iii) of Theorem 5.3 would not follow; and the two halves of
the second clause are exactly condition (ii) of Theorem 5.3 for the two orderings.

**Proposition 5.4's hereditary half and Corollary 5.5(2) quantify over classes, not over all
projective modules.** As scaffolded, the freeness clause read "every projective module that is not
finitely generated is free on a countable basis", which is false as soon as `R ≠ 0`: `R^{(ℵ₁)}` is
projective and not finitely generated, but is not free on a countable basis (axiom A1). The paper
says "any countably (non finitely) generated projective module", and the carrier of `V^{ℵ₀}(R)` is
exactly the countably generated projectives, so the statements range over `q : V^{ℵ₀}(R)`.

One thing the paper has that Section 5 does not: part (3) of Corollary 5.5 also records two further
reformulations of realizability — that `R` may be taken with a finitely generated projective `P`
whose `P^{(ℵ₀)}` is not free, and that this is the same as `Tr(P₁) ⊊ Tr(P₂)`. The scaffold stated
part (3) without them, and it is a correct equivalence as it stands; the omission is noted in
`SECTION5-PLAN.md`.

## Encoding decisions

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
* `LMonoid.ofLE` (a five-line restriction along `λ ≤ λ'`) subsumes Remark 2.19 in general;
* only genuinely `κ`-specific statements — Lemma 2.8, which needs a largest admissible
  cardinal — are proved at the `κ`-level.

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

**The limit well-order (the one substantive choice).** Definition 3.1 fixes a limit
well-order on `κ` — a well-order in which every element has a successor, i.e. with no
maximum — and speaks of `μ + 1` and of limit elements. Rather than carry an abstract
well-order plus a successor function plus the predicate "is a limit", we use the canonical
normal form: a limit well-order decomposes into `ω`-blocks indexed by its limit elements,
and a limit well-order of cardinality `κ` has exactly `κ` blocks (since `κ · ℵ₀ = κ`).
So braiding partitions and braiding families are indexed by `ι × ℕ`, with
`bsucc (a, n) = (a, n+1)` and limit elements `(a, 0)`.

This is not a loss of generality — it *is* the content of Lemma 3.4(2)(3) (every braiding
breaks up into a disjoint union of countable ones, and conversely) together with Lemma 3.5
(independence of the well-order). Those two lemmas consequently do not appear as separate
results: they are absorbed into the definition, which is why `BraidingData` is a plain
structure over `ι × ℕ` with no order-theoretic side conditions. The cost is that if you ever
want to reason with a *given* well-order you must transport across the normal form first.

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
the set of `axiom` declarations under `KappaMonoid/` differs from the six in the table above.
Documentation is generated by `docgen-action`.

`scripts/check_layering.sh` is what keeps the layers honest — Lake resolves modules package-wide,
so `Core/` importing `Modules/` would build fine. It checks the import discipline between layers,
that no module theory appears below `Modules/`, and that only `Axioms/*` and `Modules/Small.lean`
import all of Mathlib.
