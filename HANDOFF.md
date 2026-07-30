# Handoff: formalizing `trans_core` in KappaMonoid/Braiding.lean

This file is a checkpoint for continuing this task in a fresh session. Read this whole file
before touching any code.

## Task

Formalize `kappa_monoids.tex` §3 in Lean/Mathlib. The user's standing instruction: **fill in
the remaining proofs in `KappaMonoid/Braiding.lean`; no axioms or `sorry`s may remain.**

Project root: `/home/daniel/lean/kappa_formalized`. Build with:

```
cd /home/daniel/lean/kappa_formalized && lake build KappaMonoid.Braiding
```

(A *cold* build of `KappaMonoid.Braiding` takes ~200s; once its dependencies are built,
*incremental* rebuilds after an edit are only ~10-30s, so iterating is cheap. **Must `cd` to the
project root first.**)

For fast feedback while editing, the IDE diagnostics that come back after each `Write`/`Edit` are
usually reliable, **but they missed two real errors** in the last session (both about implicit
arguments / motive inference in `WellFounded.induction`). Always confirm with `lake build`.

A useful trick: develop new material in a throwaway `KappaMonoid/Scratch.lean` that starts with
`import KappaMonoid.Braiding`, then merge into `Braiding.lean` at the end. Rebuilding the scratch
file is a few seconds, versus a full re-elaboration of `Braiding.lean`.

## Current status (as of this checkpoint)

- **0 axioms** beyond `propext`, `Classical.choice`, `Quot.sound`.
- **Exactly 1 `sorry`**, in `theorem trans_core`, and it is now confined to the branch
  `lam ≠ ℵ₀`. The `lam = ℵ₀` branch is fully proved:
  ```
  by_cases hlam : lam = ℵ₀
  · subst hlam; exact trans_aleph0 hxy hyz     -- DONE
  · sorry                                       -- λ > ℵ₀: still open, see below
  ```
- **Lemma 3.7 and Lemma 3.8 are fully formalized for `λ = ℵ₀`** (this was the previous session's
  task and it is complete). Confirmed by a full `lake build KappaMonoid`: succeeds with the single
  `declaration uses 'sorry'` warning pointing at `trans_core`.

## What was built (all inside `KappaMonoid/Braiding.lean`)

### Infrastructure

In `section Aux`:
- `LMonoid.lsumOf_eq_finsum (h : #S < ℵ₀) (f)` — **the key bridge**: for `λ = ℵ₀`,
  `lsumOf h (fun i : S => f i) = ∑ᶠ i ∈ S, f i`. All of the λ=ℵ₀ work is done in Mathlib's
  `finsum` (`∑ᶠ`) language, which has no finiteness side conditions *in the terms* and a rich
  `finsum_mem_*` API (`finsum_mem_union`, `finsum_mem_biUnion`, `finsum_mem_add_distrib`,
  `finsum_mem_image`, `finsum_mem_eq_zero_of_forall_eq_zero`, …). This was the single biggest
  simplification; do not go back to raw `lsumOf` for finite index sets.
- `finsum_mem_split`, `finsum_mem_eq_of_diff_eq_zero`, `finsum_mem_triple`.

After the `BraidingData` structure:
- `BraidingData.mk_finsum` — build a `BraidingData ℵ₀` from finite partitions and `finsum`
  equations. This is the constructor used everywhere below.
- `section Regroup`: `regroup P G p := ⋃ ν ∈ G p, P ν` plus `regroup_finite`,
  `regroup_disjoint`, `regroup_cover`, `regroup_finsum` (the latter is `finsum_mem_biUnion`).

### Lemma 3.8 (`IsBraided.of_aligned`)

`grp3` is the paper's "merge blocks in groups of three" grouping: `grp3 (a,0) = {(a,0)}` and
`grp3 (a,l+1) = {(a,3l+1),(a,3l+2),(a,3l+3)}`, with `grp3_finite/_disjoint/_cover`.

`of_aligned (d : BraidingData ℵ₀ x y) (e : BraidingData ℵ₀ y z)` takes the alignment purely in
**local** form (no cumulative unions over the well-order, no ordinals!):
```
h1 : ∀ p, e.I p ⊆ d.J p ∪ d.J (bsucc p)
h2 : ∀ p, d.J (bsucc p) ⊆ e.I p ∪ e.I (bsucc p)
h3 : ∀ a, d.J (a,0) ⊆ e.I (a,0)
```
and concludes `IsBraided ℵ₀ x z`. Key insight that made this easy: the paper's
`s_μ = Σ_{J'_μ ∖ J_μ} y = Σ_{J_{μ+1} ∖ J'_{μ+1}} y` is an *actual set identity*
(`J'_μ ∖ J_μ = J'_μ ∩ J_{μ+1} = J_{μ+1} ∖ J'_{μ+1}`), so `s`, `t` are defined directly as
`s p = ∑ᶠ j ∈ e.I p ∩ d.J (bsucc p), y j` and `t p = ∑ᶠ j ∈ d.J (bsucc p) ∩ e.I (bsucc p), y j`.
The paper's `eq:subs1`/`eq:subs2` are then never needed as separate lemmas: everything reduces to
three identities `G1/G2/G3` and the rest is `abel`.

### Lemma 3.7, Stage 1d (`IsBraided.exists_repartition`)

Given `d : BraidingData ℵ₀ x y` and a family `A : ι×ℕ → Set (ι×ℕ)` with
`hfin`/`hdisj`/`hcov`/`hsucc : repSucc (A μ) ⊆ A (bsucc μ)`/
`hloc : ∀ μ ν, bsucc ν ∈ A μ → ν ∉ A μ → ∃ ρ, μ = bsucc ρ ∧ ν ∈ rep (A ρ)`,
produces a braiding with pieces `regroup d.I A`, `regroup d.J A`, braiding families
```
u μ = (∑ᶠ ν ∈ A μ, d.u ν) + ∑ᶠ ν ∈ A μ ∖ lep (A μ), d.v ν      v μ = ∑ᶠ ν ∈ lep (A μ), d.v ν
```
**Improvement over the paper**: defining `v μ` as the sum over `lep (A μ)` (rather than over
`rep (A (μ-1))⁺`) makes the `hI` equation immediate; the paper's telescoping argument is then only
needed for `hJ`, where it reduces to the two set facts
`bsucc '' (A μ ∖ rep (A μ)) = A μ ∖ lep (A μ)` (`image_bsucc_diff_rep`) and
`repSucc (A μ) ⊆ lep (A (bsucc μ)) ⊆ repSucc (A μ) ∪ {limit positions}`.
The paper's property (6) ("right saturation", stated with an awkward `∀n, β+n < μ` quantifier) is
**replaced** by the strictly local `hsucc`/`hloc` above, which are strictly stronger and much
easier to both establish and use.

### Lemma 3.7, Stage 1c (the recursion)

- `usedBefore A μ = {ν | ∃ ρ, kOrd ι ρ μ ∧ ν ∈ A ρ}`, `prevOf A μ` (= `A (μ.1, μ.2-1)`, `∅` at
  limits), and `kOrd` helpers (`kOrd_irrefl`, `kOrd_trans`, `kOrd_pred`, `bsucc_prev`,
  `kOrd_lt_bsucc_iff`, `usedBefore_bsucc`, `usedBefore_mono`, `subset_usedBefore`).
- `transStep` / `transFam := kOrd_wf.fix (transStep d₁ d₂)` / `Afam` / `Bfam`, with unfolding
  lemmas `Afam_eq`, `Bfam_eq` (proved by `show (transFam …).1 = _; rw [transFam_eq]; rfl` — note
  `Bfam_eq` additionally needs `rw [Afam_eq]` because the `ℬ`-seed refers to the `𝒜` just built).
- **Exhaustion trick** (much simpler than the paper's "add the minimum of the complement"): seed
  step `μ` with `{μ} \ usedBefore A μ`. Then `∀ν, ν ∈ usedBefore A ν ∪ A ν`, so
  `IsSatRec.cover` is a two-line proof and no ordinal-rank argument is needed. The leftover
  `minCompl`/`minCompl_mem` declarations from the earlier session are now unused (harmless).
- `structure IsSatRec A C` abstracts "`A μ` = `satClosure (usedBefore A μ)` of a seed
  `C μ ∪ repSucc (prevOf A μ) ∪ ({μ} \ usedBefore A μ)`, with `C μ` disjoint from
  `usedBefore A μ` and every `A μ` finite". From it: `seed_subset`, `leftSat`, `succ_subset`,
  `cover`, `disj` (the only transfinite induction, using left saturation of the earlier steps),
  `pairwise`, `loc`. Instantiated twice: `isSatRec_A`, `isSatRec_B`. Finiteness needs a
  *simultaneous* induction over both families (`transFam_finite`), since the `𝒜`-seed uses
  `ℬ_{μ-1}` and the `ℬ`-seed uses `𝒜_μ`.
- `aligned_of_isSatRec` derives the local alignment `h1/h2/h3` from the two invariants
  `I1 : VaJ μ ⊆ VbI μ` and `I2 : VbI μ ⊆ VaJ μ ∪ J'_{μ-1}`. **Neither needs transfinite
  induction** — only the seed covering property, monotonicity, and `kOrd_not_between`.
- `exists_aligned` = Lemma 3.7, `trans_aleph0` = Lemma 3.8 for `λ = ℵ₀`.

## What is left

### The `λ ≠ ℵ₀` branch of `trans_core` (the only `sorry`)

This is the one deliberately deferred item, and the user has been told it is deferred. Status of
the mathematics: the paper's construction has an **apparent gap** for general `λ` — a
`λ⁻`-interval is required to have *finite* per-block ranges `[n_l, m_l)`, but for `λ > ℵ₀` the
covering target at one step could a priori need to touch a single block at an infinite (though
`< λ`) set of offsets, which no `λ⁻`-interval can do. For `λ = ℵ₀`, `< λ` means finite, so the
issue is vacuous — which is why that case was done first.

Concretely, to lift the present proof to `λ > ℵ₀` one would need to replace
`satClosure`/`satClosure_finite` (whose finiteness proof uses a *uniform finite bound*
`{p | p.1 ∈ F ∧ p.2 ≤ N}` on all iterates) by an argument bounding the closure's cardinality by
`< λ`. The rest of the development is already cardinal-agnostic in spirit: `Stage 1d`, the
`IsSatRec` machinery and `of_aligned` only use finiteness through `Set.Finite` and the `finsum`
API, so they would each need a `#… < lam` analogue (`lsumOf` + `lsumOf_union`/`lsumOf_sigma`
instead of `finsum`). **Discuss with the user before starting**: it is not clear the paper's
statement is provable as written for `λ > ℵ₀`.

### Optional cleanups

- `minCompl`, `minCompl_mem`, `exists_cover_step`, `exists_cover_of_seed`,
  `not_mem_Ua_of_not_covered`, `kType`, `typein_kOrd_bsucc` are now unused by the completed proof
  (they were built for the earlier plan). Keep or delete as taste dictates — `kType`/
  `typein_kOrd_bsucc` document the link between `bsucc` and ordinal successors and are cheap.

## Abandoned approaches — do not retry

A "connected components + cardinal regularity" shortcut was tried and abandoned. It collapsed
`IsBraided` to "exist partitions `I,J` with `lsum(I p) x = lsum(J p) y`" — but `I`,`J` are
independent partitions where only their SUMS are linked, not their supports. A slot `p` with
`J(p) = ∅` but `I(p) ≠ ∅` is invisible to any construction based only on `J`-side connectivity
(since `lsum(∅) y = 0` does NOT force `I(p) = ∅` as a SET, because `LMonoid` has no cancellation
law). **Conclusion**: work with the full `BraidingData` (`u`, `v`, `bsucc` telescoping), as the
completed proof now does.

## Reminders

- Test with the IDE diagnostics after every small addition, but **confirm with a full
  `lake build`** — diagnostics have missed real errors.
- The user has been carefully vetting the mathematical reasoning throughout and expects rigor; do
  not weaken statements to make them provable.
