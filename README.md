# A Lean 4 formalisation of Nazemian–Smertnig, *A monoid-theoretical approach to infinite direct-sum decompositions of modules*

Sections 2–4 of the paper. Section 5 is omitted, as requested.

## Status

Complete and `sorry`-free: `lake build` checks every definition and every theorem, including
Theorem 3.11 (universal `κ`-extensions) and Theorem 4.3 (`V^κ(C)` is `λ⁻`-braided over
`V^{λ⁻}(C_{λ⁻})`).

| File | Contents |
|---|---|
| `KappaMonoid/Basic.lean` | §2: `LMonoid` (= `λ⁻`-monoid), `KMonoid`, sums over arbitrary small index types, cardinal scalar multiplication, reducedness (Lemma 2.8), homomorphisms, `⟨S⟩_κ`, induced structures on sub-objects, `KMonoid.ofBare` (Lemma 2.5) |
| `KappaMonoid/Braiding.lean` | §3: `BraidingData`, `IsBraided`, Lemmas 3.2/3.4/3.6/3.7/3.8, `braidingSetoid`, `IsBraidedOver` (Def. 3.1(2)) |
| `KappaMonoid/Universal.lean` | §3.1: Prop. 3.9, Def. 3.10, the construction `X^κ/≈`, **Theorem 3.11**, and the necessity of the added hypothesis |
| `KappaMonoid/Modules.lean` | §4: Def. 4.1 (`λ⁻`-small), `ModuleClass` (= a class `C` with `V^κ(C)`), (M1)/(M2), **Theorem 4.3**, Cor. 4.4, Cor. 4.5–4.7 |

Sections deliberately left out beyond §5: order-units (§2.2), the realisation results for
free modules and semisimple rings (§2.3), and the worked universal extensions of §3.2
(`Fκ(B)`, Prop. 3.14) — none of these feed into Theorems 3.11 or 4.3.

## The missing hypothesis in Theorem 3.11

You are right that a hypothesis is missing, and it is worth stating precisely why.

Theorem 3.11(1) asserts, for an arbitrary `λ⁻`-monoid `H`, the existence of a `κ`-monoid
`Ĥ ⊇ H` which is a `λ⁻`-overmonoid of `H`. But Lemma 2.8(1) says every `κ`-monoid is
reduced, and a `λ⁻`-submonoid of a reduced monoid is reduced. So no non-reduced `H` can
admit such an `Ĥ`. For `λ = ℵ₀` a `λ⁻`-monoid is just a commutative monoid, and `H = ℤ` is
a counterexample: the construction `Ĥ = H^κ/≈` still goes through as a `κ`-monoid, but the
map `H → Ĥ` is not injective, so `Ĥ` is not an *over*monoid.

The formalisation therefore adds `IsConical X` (= reduced, = conical) to
`theorem_3_11`, and records two facts around it:

* `isConical_of_isUniversalKExtension` — reducedness is *necessary*: any `λ⁻`-monoid
  admitting an injective `λ⁻`-homomorphism into a `κ`-monoid is reduced. Short proof, and
  the only place Lemma 2.8 is used essentially.
* `UnivExt.of_injective` — reducedness is *sufficient* for the point where it is needed,
  namely injectivity of `x ↦ [(x,0,0,…)]`. The argument: in a braiding of `(x,0,0,…)` with
  `(y,0,0,…)`, all but at most one of the defining equations reads `0 = v μ + u μ`, so
  reducedness kills those `u`'s and `v`'s, and the surviving equations give `x = y`.

For `λ > ℵ₀` the hypothesis is vacuous — the analogue of Lemma 2.8 for `λ⁻`-monoids makes
reducedness automatic — so the gap really only concerns `λ = ℵ₀`, which is (per Lemma 3.4(4))
the interesting case. Example 2.3(1) of the paper already flags reducedness as necessary in
exactly this situation, so this looks like an omission in transcription rather than an
error in the mathematics.

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
distinct classes are non-isomorphic, and closure under `κ`-indexed direct sums and direct
summands. `V^κ(C)` is `carrier`, and `ModuleClass.instKMonoid` verifies (A1) and (A2) from
the corresponding isomorphisms of direct sums. `V^{λ⁻}(Cλ⁻)` is the subset
`lambdaSmallPart`, made into an `LMonoid` via `IsLSubset.lmonoid`.

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
