# Working on this repository

A Lean 4 formalisation of Nazemian–Smertnig, *A monoid-theoretical approach to infinite direct-sum
decompositions of modules*. The paper is in the repo: `kappa_monoids.tex` (source of truth for
statements) and `kappa_monoids.pdf`.

`README.md` is the status and provenance document. `SECTION{3,4,5}-PLAN.md` are the work plans;
§§2–3 are done, §§4–5 are scaffolded.

## Build

```fish
lake build                          # root target: must stay green and sorry-free
lake build KappaMonoid.Section4     # the scaffolds are NOT imported by KappaMonoid.lean
lake exe cache get                  # after any manifest bump, before lake build
```

A scaffold file joins `KappaMonoid.lean` in the same commit that removes its last `sorry`, so the
root build is always sorry-free.

## Working efficiently

Most of the avoidable cost in a session is the edit/build/read loop, not the mathematics.

1. **Build once into a log, then grep the log.** Never run `lake build` twice in one message.
   ```fish
   lake build > /tmp/b.log 2>&1; grep -cE "^error|uses .sorry" /tmp/b.log   # one number
   grep -m1 -A12 "^error" /tmp/b.log                                       # only the first error
   ```
   `grep -c` costs a token; an `-A14` dump of every error costs hundreds, mostly instance lists
   nobody reads. Fix the *first* error and rebuild — later ones are usually downstream.
2. **Statements first, `sorry` bodies, one build.** Elaboration, universe and instance errors are
   where the iterations go, and this catches all of them in a single pass. Then fill proofs 3–5 at
   a time, not one at a time. This is what the scaffold files do at file scale; do it at block
   scale too.
3. **Batch Mathlib API lookups.** One scratch file with many `#check` / `example … := by exact?`
   lines, one run. `grep` in `.lake/packages/mathlib/Mathlib/…` first — it is far cheaper than
   `exact?` and usually enough. Import the specific Mathlib modules rather than all of `Mathlib`.
   Guessed names are often stale (`Nat.dvd_sub'` → `Nat.dvd_sub`, `Cardinal.nat_lt_aleph0` →
   `Cardinal.natCast_lt_aleph0`): check before writing a block that depends on them.
4. **Prefer `Edit` for small fixes.** The hook posts IDE diagnostics after every `Edit`, which is
   free error feedback with no build. Use bulk rewrites (python/`Write`) for whole blocks, `Edit`
   for the fix cycles.
5. **Generalise before the second copy, not after.** Two near-identical 80-line `BraidingData`
   assemblies (`ℕ₀`, `ℝ≥0`) should have been one builder lemma.
6. **Decide the encoding on paper first.** Ask: is the carrier reducible, and will I need to
   case-split *under* a projection of it? (See trap 8.) Two minutes here saved four build cycles
   in `RTilde`.
7. **Read narrowly.** `grep -n` for the name, then `sed -n 'a,bp'` around it. Whole-file reads are
   rarely worth it.
8. **One step = one commit**, with the build green. Commit messages: what changed and why, a few
   lines, not an essay.

## Lean conventions

- **Universes**: index types `Type u`, carriers `Type v`, a second carrier `Type w`; cardinals
  `lam κ : Cardinal.{u}`. Declare universes at the top of the file rather than relying on
  auto-binding (see trap 5).
- **Prove at the `λ⁻` level and specialise to `κ`.** `KMonoid κ H` *is* `LMonoid (Order.succ κ) H`
  plus `ℵ₀ ≤ κ`, and `#ι ≤ κ ↔ #ι < Order.succ κ`.
- **Docstrings** open with the bold paper reference — `**Lemma 3.13(2)**`, `**Examples 3.3(2)**` —
  and, when the argument is not obvious, carry a `Paper proof:` paragraph paraphrasing the source.
  This is the main navigation aid in the repo; keep it up.
- **Instances**: defs producing them carry `@[instance_reducible]`. Instances that depend on
  hypotheses are threaded through statements with `letI`, repeated verbatim at the top of the
  tactic proof.
- **No new axioms without asking.** The five assumed classical results live in
  `KappaMonoid/Axioms.lean` and are documented in `README.md`; run `#print axioms` on new headline
  results and keep that table in step. §3 needs no axiom at all.
- **Deviations from the paper are documented twice**: in the docstring of the affected result and
  in a `README.md` section. Two exist so far — the `IsConical` hypothesis in Theorem 3.11 and the
  `IsSaturatedFin` hypothesis in Proposition 3.14(2), the latter with a formalised counterexample
  showing the paper's claim is false. When the paper is wrong, formalise the repaired statement and
  say so; do not quietly weaken or restate it.

## Elaboration traps

Each of these has cost real time at least twice. Recognise them from the error rather than
re-deriving them.

1. **A plain `def` is not reducible**, and instance search runs at reducible transparency, so
   `(freeClass …).carrier` will not unify with an abbreviation of it. State results at the type
   instance search expects.
2. **Double coercions `↥↑m` defeat synthesis.** State subtype-of-subtype lemmas over a plain type
   variable and transport.
3. **`letI`-in-statement instance arguments often cannot be inferred** from the goal — pass them
   explicitly: `Fcard.instKMonoid_add (le_refl (ℵ₀ : Cardinal.{u}))`.
4. **Defeq is not syntactic.** `rw` will not turn `KMonoid.ksum` into `KMonoid.sumOf`, or
   `RTilde.sigma` into `ksum`; convert first with `show _ = _ from rfl`, a typed `have`, or
   `KMonoid.sumOf_Idx`.
5. **Pin universes in statements that do not mention them.** A hypothesis like
   `(hsat : sys.IsSaturatedFin)` elaborates before the `letI`s that fix `Cardinal.{u}`, so its
   universe is auto-bound to a *fresh* variable and the proof fails with `constant has level params
   [u, u_1]`. Write `LinSystem.IsSaturatedFin.{u} sys`. Same for a conjunction whose parts each
   mention a universe-polymorphic constant: without ascriptions they end up about *different*
   universes (`example_3_15` had three).
6. **`(u := u)` is never valid** for a universe parameter. Use a type ascription:
   `letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid`.
7. **`IsLMonoidHom`/`IsLHom` are plain `def`s**, so an expected type gets unfolded to a `∀` and
   unification will not solve for the function. Three consequences, all of which have bitten:
   give a transport lemma's maps as **explicit** arguments rather than implicit ones; always ascribe
   the type when `have`-ing such a hypothesis (`have h : IsLMonoidHom lam f := …`); and when the
   *conclusion* determines the maps (`hom_ext`, `of_base_iso`), state the expected type of the
   `have` — named arguments alone are not enough, because the arguments get elaborated before the
   metavariables are assigned.
8. **Universal properties do not cross universes.** `IsUniversalKExtension`'s `universal` field
   quantifies over test objects `K : Type w` in the *same* universe as the extension, so
   `isUniversalKExtension_unique` compares two extensions in one universe only. This is why
   Example 4.8(1) cannot say `V^κ(C) ≅ F_κ(B)`: `F_κ(B)` lives in `Type (u+1)` (it is built from
   cardinals) and `V^κ(C)` in `Type u`. Deliver the universal property instead, or lift. By
   contrast the *bases* of a braiding or a universal extension may live in different universes —
   both `of_base_iso` lemmas allow it.
9. **Do not case-split inside a projection of an opaque carrier.** A three-branch `dite` whose
   branches carry dependent proofs makes every `val`/`flag` lemma fight the motive, because the
   carrier `def` cannot be unfolded at `implicit` transparency. Compute the components separately
   (`RTilde.sigmaFlag`) so the constructor application is a single term and the projections are
   `rfl`.
10. **Term-mode proofs of `letI`-in-statement results fail.** Use tactic mode and repeat the
   `letI`s.
11. **Cardinality of unions**: `Cardinal.mk_iUnion_le_sum_mk` then
    `Cardinal.sum_lt_of_isRegular` gives `< λ` for a `< λ`-indexed union of `< λ` sets — this works
    uniformly at `λ = ℵ₀`, where a bound like `#Bad * ℵ₀` does not. For plain finiteness,
    `Set.Finite.biUnion`.
12. **`tsum` is cross-universe friendly**: `Equiv.tsum_eq` and the `ENNReal.tsum_*` lemmas accept
    index types in different universes, which is what lets an `ℕ`-indexed construction be
    transported to `ι : Type u`.

## Where things live

| File | Contents |
|---|---|
| `Basic.lean` | `LMonoid`/`KMonoid`, `SumData`, the `lsumOf` API (union, subset, sigma, pair, …), `IsConical`, `IsLHom`, `kclosure`, induced structures |
| `Braiding.lean` | `BraidingData`/`IsBraided`, Lemmas 3.2–3.8, `mk_finsum`, `ℕ`-interval helpers, `IsBraided.mk_support_lt` |
| `Universal.lean` | Prop. 3.9, Theorem 3.11 and its converse, the transports (`of_iso`, `of_base_iso`, `isLMonoidHom_aleph0_of_add`) |
| `Examples.lean` | `TrivExt` (Examples 2.3(1)), `LCard`/`Fcard`, the `ℝ≥0∞` monoid |
| `Free.lean`, `OrderUnit.lean`, `Cyclic.lean`, … | §2 |
| `Section32.lean` | §3.2: Lemma 3.13, Prop. 3.14, Example 3.15 |
| `Reals.lean` | Examples 3.3(2)(3): braiding in `ℝ≥0`, the monoid `ℝ≥0 ∪ ℝ̃>0 ∪ {∞}`, the `ℚ≥0` variant |
| `Modules.lean` | §4 |
| `Section4.lean` | §4 scaffold, not imported: Corollary 4.7(1) is what is left |
| `Section5.lean` | §5 scaffold, not imported |

Before writing a new construction, check whether the analogous one exists: the `ℕ₀` and `ℝ≥0`
braidings, the `Fcard`/`RTilde` `SumData`s, and the `TrivExt` extension are all templates.
