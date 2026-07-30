# Handoff: `KappaMonoid/Braiding.lean` — COMPLETE

## Status

**`KappaMonoid/Braiding.lean` contains no `sorry` and no axioms** beyond `propext`,
`Classical.choice`, `Quot.sound` (verified with `#print axioms NS.IsBraided.trans_core`).
Section 3 of `kappa_monoids.tex` is fully formalized, for **all** `λ`:

- `IsBraided.trans_core` / `IsBraided.trans` — transitivity, for arbitrary `lam`.
- `braidingSetoid` — the braiding relation is an equivalence relation.

Remaining `sorry`s in the *project* are in `KappaMonoid/Universal.lean` (7) and
`KappaMonoid/Modules.lean` (11) — §4 material, untouched by this work.

Build: `cd /home/daniel/lean/kappa_formalized && lake build KappaMonoid` (cold ~200s for
`Braiding.lean`; incremental rebuilds of a scratch file importing it are ~10s).

## How transitivity is proved: two disjoint arguments

`trans_core` splits on `by_cases hlam : lam = ℵ₀`.

### `λ = ℵ₀`: the paper's Lemma 3.7 + Lemma 3.8 (`IsBraided.trans_aleph0`)

Everything lives in `section TransAleph0`.  For `λ = ℵ₀` all pieces are finite, so the whole
argument is carried out in Mathlib's `finsum` (`∑ᶠ`) language via the bridge
`LMonoid.lsumOf_eq_finsum`; `BraidingData.mk_finsum` builds braiding data from `finsum`
equations, and `regroup` + `regroup_finite/_disjoint/_cover/_finsum` regroups a partition along a
partition of the position set.

- **Lemma 3.8** (`IsBraided.of_aligned`): takes the alignment in purely *local* form —
  `e.I p ⊆ d.J p ∪ d.J (bsucc p)`, `d.J (bsucc p) ⊆ e.I p ∪ e.I (bsucc p)`,
  `d.J (a,0) ⊆ e.I (a,0)` — and merges blocks in threes (`grp3`).  Simplification found here:
  the paper's `s_μ` is an *actual set identity*
  (`J'_μ ∖ J_μ = J'_μ ∩ J_{μ+1} = J_{μ+1} ∖ J'_{μ+1}`), so `eq:subs1`/`eq:subs2` are never needed
  — three identities `G1/G2/G3` plus `abel`.
- **Lemma 3.7, Stage 1d** (`IsBraided.exists_repartition`): regroups a braiding along a family
  `A : ι×ℕ → Set (ι×ℕ)` of finite position blocks.  Defining `v μ := ∑ᶠ ν ∈ lep (A μ), d.v ν`
  (instead of the paper's `∑_{rep(𝒜_{μ-1})⁺}`) makes the `hI` equation immediate, and replaces the
  paper's property (6) with two strictly local, stronger conditions (`hsucc`, `hloc`).
- **Lemma 3.7, Stage 1c**: `transStep` / `transFam := kOrd_wf.fix (transStep d₁ d₂)` /
  `Afam` / `Bfam`, with `structure IsSatRec` abstracting the recursion shape.  Two more
  simplifications: seeding step `μ` with `{μ} \ usedBefore A μ` makes exhaustion trivial (no
  minimum-of-complement rank argument — the leftover `minCompl` declarations are now unused), and
  the interleaving invariants `I1`/`I2` need **no** transfinite induction (only `IsSatRec.disj`
  does).

### `λ > ℵ₀`: components (`IsBraided.trans_of_ne_aleph0`), in `section TransUncountable`

This follows the user's observation: for uncountable `λ`, take as `λ⁻`-intervals the unions of
`< λ` limit elements *together with all their successors* (full `ω`-blocks, i.e. right endpoint
`= ∞`).  For such an interval the braiding families telescope away entirely — which is exactly
`BraidingData.block_lsumOf_eq` and hence `isBraided_iff_of_ne_aleph0` (Lemma 3.4(4), already in
the file): for `lam ≠ ℵ₀`,

```
IsBraided lam x y ↔ ∃ partitions I, J into `< λ` pieces with `Σ_{I p} x = Σ_{J p} y`
```

so transitivity becomes purely combinatorial and *no* braiding families, `bsucc`-telescoping,
alignment or ordinal recursion are involved:

- `ccomp J J' i` — the connected component of `i` for "lie in a common piece of `J` or of `J'`",
  built as `⋃ n, cstep^[n] {i}`.  `mk_ccomp_lt`: each component has size `< λ`, because it is a
  *countable* union of `< λ`-sized sets and `λ` is regular and uncountable.  `crep` picks the
  `WellOrderingRel`-least element of a component as its canonical name.
- `exists_common_regrouping` — the combinatorial core: two partitions `J`, `J'` of `ι` can be
  grouped into `< λ`-sized groups (`groupA`, `groupB`) that **cover exactly the same sets**.
  Component groups sit at slots `(a, 0)`; the *empty* pieces of `J` are parked at `(a, 2m+1)` and
  those of `J'` at `(a, 2m+2)` (they cover nothing but still need a slot).
- `IsBraided.trans_of_ne_aleph0` — regroup `I` along `groupA` and `K` along `groupB`, then
  `Σ_{M μ} x = Σ_{Y μ} y = Σ_{N μ} z` and conclude by `IsBraided.of_partition`.

**Note on the "orphaned mass" objection recorded in earlier checkpoints**: a slot `p` with
`J p = ∅` but `I p ≠ ∅` is *not* a problem here.  Its sum satisfies `Σ_{I p} x = Σ_{∅} y = 0`, so
giving each such slot its own group (with empty partner) keeps the piecewise sums matched — and
there are at most `#(ι×ℕ)` such slots, which is exactly how many spare slots the `2m+1`/`2m+2`
encoding provides.  The earlier objection applied to *proving* Lemma 3.4(4) from one side only,
not to merging two partitions that already have equal partial sums.

## Lessons worth keeping

- IDE diagnostics after each `Write`/`Edit` are a good fast filter but **have missed real errors**
  (implicit-argument and `WellFounded.induction` motive-inference failures).  Confirm with
  `lake build`.
- Develop in a throwaway `KappaMonoid/Scratch.lean` that imports `KappaMonoid.Braiding`
  (rebuild ~10s), then merge.  When merging by script, check `namespace`/`section` balance first —
  two rounds were lost to an unclosed `namespace IsBraided`.
- `unfold f` + `rw [if_pos/if_neg (show … by omega)]` reliably discharges the defining equations of
  a function defined by nested `if`s on `%`/`/`; the same `rw` fails if the function is an
  un-beta-reduced lambda supplied by `refine ⟨fun μ => …, ?_⟩`, so give such functions a name.
- For `λ = ℵ₀`, always go through `finsum`; for general `λ`, the available tools are
  `LMonoid.lsumOf_add`, `LMonoid.lsumOf_biUnion_subset`, `LMonoid.lsumOf_of_subset`,
  `lsumOf_equiv`, `lsumOf_sigma`, and `Cardinal.card_iUnion_lt_iff_forall_of_isRegular`.

## Possible cleanups (optional)

`minCompl`, `minCompl_mem`, `exists_cover_step`, `exists_cover_of_seed`,
`not_mem_Ua_of_not_covered`, `kType`, `typein_kOrd_bsucc` are no longer used by any proof (they
were built for an earlier plan for the `λ = ℵ₀` recursion).  They are harmless; delete if desired.
