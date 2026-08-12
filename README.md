# A Lean 4 formalisation of Nazemian–Smertnig, *A monoid-theoretical approach to infinite direct-sum decompositions of modules*

Sections 2–5 of the paper.

## Status

Complete and `sorry`-free: `lake build` checks every definition and every theorem, including
Theorem 3.11 (universal `κ`-extensions), Proposition 3.14 (universal extensions of Diophantine
monoids), Theorem 4.3 (`V^κ(C)` is `λ⁻`-braided over `V^{λ⁻}(C_{λ⁻})`) and all of §§2–4.

| File | Contents |
|---|---|
| `KappaMonoid/Basic.lean` | §2: `LMonoid` (= `λ⁻`-monoid), `KMonoid`, sums over arbitrary small index types, products, cardinal scalar multiplication and reducedness (Lemmas 2.7, 2.8, both at the `λ⁻` level), homomorphisms, `⟨S⟩_κ`, induced structures on sub-objects, `KMonoid.ofBare` and `PaperKMonoid` (Lemma 2.5, Def. 2.1 verbatim) |
| `KappaMonoid/Examples.lean` | Examples 2.3(1)(2)(3): the trivial `κ`-extension `M ⊎ {∞}` of a reduced monoid, `ℝ≥0∞`, and `F_{λ⁻}` / `F_κ` (the cardinals below a bound) |
| `KappaMonoid/Free.lean` | §2.1: **Proposition 2.9**, the free `λ⁻`-monoid `F_{λ⁻}(B)` and free `κ`-monoid `F_κ(B)`, with the universal property |
| `KappaMonoid/OrderUnit.lean` | §2.2: Defs. 2.11–2.12, `size`, the filtration `H_α`, faithfulness ⟺ properness, **Lemma 2.14** |
| `KappaMonoid/Cyclic.lean` | §2.3: **Lemma 2.15**, the structure of a cyclic `κ`-monoid with a faithful order-unit |
| `KappaMonoid/ProjOrderUnit.lean` | §2.2: **Example 2.13**, `[R]` is a faithful order-unit of `V^κ(R)` |
| `KappaMonoid/FreeModules.lean` | §2.3: `V^κ(𝓕^κ)`, the class of free modules, as a Definition 2.4 `ModuleClass` |
| `KappaMonoid/FreeUnit.lean` | §2.3: ranks in `V^κ(𝓕^κ)`; `[R]` is a cyclic faithful order-unit |
| `KappaMonoid/Realisation.lean` | §2.3: **Proposition 2.16**, cyclic `κ`-monoids are realised by rings of free modules |
| `KappaMonoid/Semisimple.lean` | §2.3: multiplicities of semisimple modules and **Proposition 2.17**, `V^κ(R) ≅ F_κ^n` for semisimple `R`, and such rings exist for every `n` |
| `KappaMonoid/Braiding.lean` | §3: `BraidingData`, `IsBraided`, Lemmas 3.2/3.4/3.6/3.7/3.8, `braidingSetoid`, `IsBraidedOver` (Def. 3.1(2)) |
| `KappaMonoid/Universal.lean` | §3.1: Prop. 3.9, Def. 3.10, the construction `X^κ/≈`, **Theorem 3.11** and its converse (`isBraidedOver_of_isUniversalKExtension`: universal ⟹ braided over), transport of braidedness along isomorphisms |
| `KappaMonoid/Section32.lean` | §3.2: Examples 3.3(1) and Examples 3.12 for `ℕ₀`, **Lemma 3.13**(1) and (2), **Proposition 3.14**(1) and (2) (universal extensions of Diophantine monoids), saturation for inequality-free systems, **Example 3.15**, and the counterexample showing that (2) does need the saturation hypothesis |
| `KappaMonoid/Reals.lean` | §3: **Examples 3.3(2)(3)** and their entries of Examples 3.12 — braiding in `ℝ≥0` (same series sum, supports both finite or both infinite), why neither `ℵ₀`-monoid structure on `ℝ≥0 ∪ {∞}` is braided over `ℝ≥0`, the `ℵ₀`-monoid `ℝ≥0 ∪ ℝ̃>0 ∪ {∞}` and its universal property, that it is not braided over itself, and the `ℚ≥0` variant with its extension identified as `ℚ≥0 ∪ ℝ̃>0 ∪ {∞}` |
| `KappaMonoid/Modules.lean` | §4: Def. 4.1 (`λ⁻`-small), `ModuleClass` (= a class `C` with `V^κ(C)`), Examples 2.3(4) / Def. 2.4, (M1)/(M2), **Theorem 4.3**, Cor. 4.4, Cor. 4.5, Kaplansky (the `κ`-monoid form; the classical statement is axiom A6) |
| `KappaMonoid/Section4.lean` | §4: `add x` and `add_λ x`, `V(R) = add [R]`, **Corollary 4.7**(1) (both directions) and (2), **Examples 4.8(1)** (ascent of KRSA) |
| `KappaMonoid/Axioms.lean` | The six classical results assumed rather than proved — see below |

**Section 2 is complete.** Every definition, example, lemma and proposition of §2 is stated and
proved, `sorry`-free, subject only to the four §2 axioms below (A1–A4; A5 is used nowhere in the
checked build).

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
`Modules.lean`. Examples 4.8(1) is proved in a corrected form, for a universe reason: see "The
statement corrected in Examples 4.8(1)" below.

### Scaffold

One file carries the part of §5 that is not yet proved: every statement type-checks, and the proofs
are filled in as far as they go. It is not imported by `KappaMonoid.lean`, so `lake build` stays
green and `sorry`-free; build it individually with `lake build KappaMonoid.Section5`.

| File | Contents | Plan |
|---|---|---|
| `KappaMonoid/Section5.lean` | §5: forms `α X₁ + β X₂` over `ℕ∞`, Lemmas 5.1–5.2, **Thm. 5.3** (which two-generated `ℵ₀`-monoids are `V^{ℵ₀}(R)` for a hereditary ring), trace ideals and Prop. 5.4, Cor. 5.5 and its `ℕ₀² ∪ {∞}` counterexample | `SECTION5-PLAN.md` |

## Conventions

`CLAUDE.md` collects what a contributor (human or model) needs before touching the files: the build
commands, the Lean house style, the axiom and deviation discipline, the recurring elaboration traps
of this development, and the workflow that keeps the edit/build loop cheap. The three plan
documents defer to it and only record what is specific to their section.

## The assumed results

Six classical theorems are taken as axioms in `KappaMonoid/Axioms.lean`, each with the
standard proof sketch it stands for:

| Axiom | Statement | Used by |
|---|---|---|
| `mk_le_of_span_eq_top` (A1) | invariance of infinite rank, in the form: a free module with an infinite basis is not generated by fewer elements than its rank | Example 2.13, Prop. 2.16 |
| `leavittData` (A2) | Leavitt's realisation of the cyclic monoids `C_{m,n}` | `prop_2_16` |
| `cyclicMonoidClassification` (A4) | every cyclic monoid is `ℕ₀` or `C_{m,n}` | `prop_2_16` |
| `mk_multiplicity_eq` (A3) | uniqueness of the multiplicities of simple modules, infinite multiplicities included | `prop_2_17_one` |
| `bergmanDicksData` (A5) | Bergman–Dicks realisation: every reduced commutative monoid with order-unit is `V(R)` for a hereditary `k`-algebra. Bundled with the hereditary case of Cor. 4.6, since Cor. 4.7(1) uses the two together | `corollary_4_7_one_forward` |
| `kaplansky_classical` (A6) | Kaplansky's theorem: every projective module is a direct sum of countably generated projective modules | `kaplansky`, and through it Cor. 4.5 and Cor. 4.7 |

The list is enforced: `.github/workflows/lean_action_ci.yml` fails if the set of `axiom`
declarations under `KappaMonoid/` differs from the six above, so adding one means editing the
workflow and this table in the same commit.

A1 is stated in the *generation* form rather than the two-bases form because the complement
appearing in Example 2.13 is merely projective, not free, so there is no second basis to compare
against; the familiar two-bases statement is derived from it as `mk_eq_mk_of_infinite`.

The assumptions are contained.  `#print axioms prop_2_16` reports exactly A1, A2 and A4;
`prop_2_17` reports exactly A3; Example 2.13's `isFaithful_unitClass` reports exactly A1.
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

## The statement corrected in Examples 4.8(1)

Examples 4.8(1) concludes `V^κ(C) ≅ F_κ(B)`: if every module in `C` is a direct sum of `λ⁻`-small
ones and `V^{λ⁻}(C_{λ⁻})` is free on `B`, then `V^κ(C)` is the free `κ`-monoid on `B`. That
*isomorphism* is not expressible here. `F_κ(B)` is cut out of `B → F_κ`, so it lives in
`Type (u+1)`, while `V^κ(C)` lives in `Type u`; and the `universal` field of
`IsUniversalKExtension` quantifies over test objects in the *same* universe as the extension, so
`isUniversalKExtension_unique` compares two extensions in one universe only (trap 8 of
`CLAUDE.md`).

What is proved instead is the universe-correct content of the example, in two steps:
`krsa_ascent` — `V^κ(C)` *is* the universal `κ`-extension of `F_{λ⁻}(B)`, by transporting Theorem
4.3's braiding along the isomorphism of bases — and `krsa_ascent_free`, which turns that into the
`B`-indexed universal property of the free `κ`-monoid: every map `B → K` into a `κ`-monoid extends
uniquely along the generators. That is what "`V^κ(C)` is the free `κ`-monoid on `B`" says, and its
`λ⁻`-level input, `Free.exists_unique_lift`, has a free target universe. Two ways to recover the
isomorphism itself, should it ever be wanted: make `universal` quantify over a test object in a
fresh universe (`extend_lhom` already works in that generality, so this changes the definition and
Theorem 3.11's statement but not its proof), or compare `ULift`s.

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

```
lake update                                  # fetches Mathlib
cp .lake/packages/mathlib/lean-toolchain .   # match toolchain
lake build
```

`lakefile.toml` tracks Mathlib `master`; pin a `rev` if you want reproducibility.
