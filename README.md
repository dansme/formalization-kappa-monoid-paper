# A Lean 4 formalisation of Nazemian–Smertnig, *A monoid-theoretical approach to infinite direct-sum decompositions of modules*

Sections 2–4 of the paper. Section 5 is omitted, as requested.

## Honest status

**This is a scaffold, not a machine-checked formalisation.** Every definition and every
theorem statement is written out in full; most proofs are `sorry`, with the paper's argument
recorded in the docstring. It has **not** been compiled — building Mathlib was not possible
in this environment — so expect to fix Mathlib lemma names (`Cardinal.mk_ord_toType`,
`Cardinal.le_def`, `DirectSum.component`, …), universe annotations, and `letI` plumbing on
first `lake build`.

What this gives you is the hard part of a formalisation project of this kind: the
*encoding* decisions. Those are discussed below, and each is a place where a different
choice would change the shape of every downstream proof.

| File | Contents |
|---|---|
| `KappaMonoid/Basic.lean` | §2: `KMonoid`, `LMonoid` (= `λ⁻`-monoid), (A3)/(A4), sums over arbitrary small index types, cardinal scalar multiplication, reducedness (Lemma 2.8), homomorphisms, `⟨S⟩_κ`, induced structures on sub-objects |
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

**Index sets.** The paper indexes by the von Neumann cardinal `κ` itself. We use
`Idx κ := κ.ord.toType`, a fixed type of cardinality `κ`, and then *derive* summation over
any index type of cardinality `≤ κ` (`KMonoid.sumOf`), exactly as the paper does after
Lemma 2.5 by choosing an injection. Independence of the chosen injection
(`sumOf_eq_extend`) needs the zero-insertion lemma `ksum_extend`, which in turn needs (A3);
this is the one piece of §2 bookkeeping the paper leaves implicit.

**(A1) at every index.** The paper states (A1) only at the distinguished element `0 ∈ κ`,
and derives the general case from (A3). Since `Idx κ` has no distinguished element, `KMonoid`
states (A1) at every index. Equivalent, given (A2).

**The additive monoid.** By Lemma 2.5 a `κ`-monoid carries a canonical commutative monoid
structure with `a + b = Σ²(a,b)`. Rebuilding that structure on the fly is painful in Lean, so
`KMonoid extends AddCommMonoid` with a compatibility axiom `ksum_two`. Redundant but
harmless, and it means `+`, `∑`, `simp` lemmas and `AddSubmonoid` all work.

**`λ⁻`-monoids.** Definition 2.18 gives a partial operation (on families with support of
size `< λ`). Lean prefers total functions, so `LMonoid.lsum` is total with the junk
convention `lsum x = 0` for large support; the axioms are only imposed on the intended
domain. This pins down the data uniquely without changing the mathematics. Note that
`LMonoid ℵ₀ X` is equivalent to `AddCommMonoid X`.

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

## What formalising the remaining proofs would take

Roughly in order of effort:

1. **§2 infrastructure** (`ksum_perm`, `ksum_comm`, `ksum_extend`, `sumOf_*`, `cmul`,
   `isConical`). Routine but genuinely fiddly cardinal bookkeeping — the zero-insertion
   lemma needs a permutation argument on complements of ranges. A week or two of work, and
   everything else depends on it.
2. **Lemma 3.8 (transitivity)** via Lemma 3.7. The paper's proof is an eight-condition
   transfinite recursion building left-saturated `λ⁻`-intervals; it is the most intricate
   purely combinatorial argument in the paper. The `ι × ℕ` normal form should help
   substantially, since the alignment condition becomes a statement about `ℕ`-indexed
   blocks. Expect this to dominate §3.
3. **Theorem 3.11** is then short: Prop. 3.9 is a telescoping computation, and the quotient
   construction needs only that braidings concatenate.
4. **Theorem 4.3.** The recursion itself is not conceptually hard, but internal direct sums
   over transfinite index sets are awkward in Mathlib. The realistic route is to avoid
   internal sums: reformulate the invariant as a chain of split injections
   `⨁_{μ<α}⨁_{i∈I μ} A i ↪ M` with chosen complements, and carry the splittings as data
   through the recursion. `Submodule.IsCompl` plus `DirectSum.IsInternal` will do the work,
   but the equations `(5)`/`(6)` need to be stated in a form that survives `α ↦ α+1` without
   re-deriving the whole decomposition.

## Building

```
lake update                                  # fetches Mathlib
cp .lake/packages/mathlib/lean-toolchain .   # match toolchain
lake build
```

`lakefile.toml` tracks Mathlib `master`; pin a `rev` if you want reproducibility.
