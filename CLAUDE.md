# Working on this repository

A Lean 4 formalisation of Nazemian–Smertnig, *A monoid-theoretical approach to infinite direct-sum
decompositions of modules*. The paper is in the repo: `kappa_monoids.tex` (source of truth for
statements) and `kappa_monoids.pdf`.

`README.md` is the status and provenance document. `SECTION{3,4,5}-PLAN.md` are the work plans and
`REFACTOR-PLAN.md` the reorganisation plan; §§2–5 are done, and steps 0–6 of the refactor.

## Build

```fish
lake build                          # root target: must stay green and sorry-free
lake exe cache get                  # after any manifest bump, before lake build
./scripts/check_layering.sh         # the layer discipline; CI runs it too
```

`lake build` on a fresh checkout rebuilds Mathlib from source if the cache is missing — hours.
Run `lake exe cache get` first and check that `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/`
is populated.

The toolchain and Mathlib are pinned to `v4.33.0`; do not run `lake update` — bumps go through
`.github/workflows/update.yml`, by hand, as their own commit.

A scaffold file joins `KappaMonoid.lean` in the same commit that removes its last `sorry`, so the
root build is always sorry-free.  As of §5 there is no scaffold left: every file is imported, and
CI rejects a `sorry` in the root target.

## Working efficiently

Most of the avoidable cost in a session is the edit/build/read loop, not the mathematics. The
`lean-lsp` MCP server (configured in `.mcp.json`, run via `uvx lean-lsp-mcp`) answers most of the
questions a build would answer, without a build. Prefer it throughout.

1. **Ask the LSP, don't rebuild.** `lean_diagnostic_messages` returns the errors and warnings of one
   file with no `lake build` at all; `lean_goal` the proof state at a position (omit `column` for
   before/after a line); `lean_term_goal` the expected type. Keep `lake build` for what only it can
   do: checking the *root target* end to end, and rechecking after an import change. When you do
   build, build once into a log and grep the log — never run `lake build` twice in one message.
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
3. **Try tactics without editing the file.** `lean_multi_attempt` runs a list of candidate tactics
   at a position and reports the resulting goal or error for each — much cheaper than an
   edit/diagnose cycle per candidate. `lean_code_actions` resolves the `Try this` text of `exact?` /
   `simp?` in place, and `lean_state_search` suggests closing lemmas from the goal.
4. **Look Mathlib names up, do not guess them.** `lean_local_search` for a name you half-remember,
   `lean_loogle` for a type pattern, `lean_leansearch` for a natural-language description,
   `lean_hover_info` for a signature, `lean_declaration_file` for the source. `lean_run_code`
   elaborates a self-contained snippet of `#check`s with no scratch file and no `lake env lean`;
   import the specific Mathlib modules rather than all of `Mathlib`. Plain `grep` in
   `.lake/packages/mathlib/Mathlib/…` remains the cheapest option when you know roughly where to
   look. Guessed names are often stale (`Nat.dvd_sub'` → `Nat.dvd_sub`, `Cardinal.nat_lt_aleph0` →
   `Cardinal.natCast_lt_aleph0`): check before writing a block that depends on them.
5. **Prefer `Edit` for small fixes.** The hook posts IDE diagnostics after every `Edit`, which is
   free error feedback with no build. Use bulk rewrites (python/`Write`) for whole blocks, `Edit`
   for the fix cycles.
6. **Generalise before the second copy, not after.** Two near-identical 80-line `BraidingData`
   assemblies (`ℕ₀`, `ℝ≥0`) should have been one builder lemma.
7. **Decide the encoding on paper first.** Ask: is the carrier reducible, and will I need to
   case-split *under* a projection of it? (See trap 8.) Two minutes here saved four build cycles
   in `RTilde`.
8. **Read narrowly.** `grep -n` for the name, then `sed -n 'a,bp'` around it. Whole-file reads are
   rarely worth it. `lean_file_outline` is the cheap way to see a file's declarations.
9. **One step = one commit**, with the build green. Commit messages: what changed and why, a few
   lines, not an essay. Scratch files are called `Scratch.lean` and are gitignored anywhere in the
   tree; do not commit one.

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
- **No new axioms without asking.** The one assumed classical result (A5) lives in
  `KappaMonoid/Axioms/` and is documented in `README.md`. A new headline result gets a line in
  `KappaMonoid/Paper/AxiomAudit.lean` — `#assert_axioms foo [bergmanDicksData]`, or `[]` for the
  usual case — which is checked by the build and fails in both directions, so it also tells you when
  a refactor has *removed* a dependency. §3 needs no axiom at all. CI enforces the list — `.github/workflows/lean_action_ci.yml` fails if the set of
  `axiom` declarations under `KappaMonoid/` changes, so a deliberate addition means editing the
  expected list there *and* the `README.md` table in the same commit.
- **Deviations from the paper are documented twice**: in the docstring of the affected result and
  in a `README.md` section. Four exist — the `m ≥ 1` hypothesis added to Leavitt's theorem,
  without which it is *false*, and was an axiom from which `False` was derivable; the `IsConical` hypothesis
  in Theorem 3.11; the
  `IsSaturatedFin` hypothesis in Proposition 3.14(2), with a formalised counterexample showing the
  paper's claim is false; and the six statements corrected in §5, chiefly `EveryProjectiveIsSumOfFG
  R` carried alongside hereditariness, which was forced when Corollary 4.6 was quoted rather than
  formalised and is now removable — see the `README.md` section, which says what the two
  restatements would be.
  (Examples 4.8(1) was a fifth until the test universe of `IsUniversalKExtension` became a
  parameter; `krsa_ascent_iso` is now the paper's statement.) When the paper is wrong, formalise the
  repaired statement and say so; do not quietly weaken or restate it.

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
8. **The test universe of `IsUniversalKExtension` is a parameter, and must be pinned.** It appears
   in no argument of the structure, so a statement that merely mentions `IsUniversalKExtension`
   leaves it a metavariable and fails with *"contains universe level metavariables"*. Write
   `IsUniversalKExtension.{u, v, w, t} lam κ X Hh hlk f` — `u` for the cardinals, `v` for the base,
   `w` for the extension, `t` for the test objects. Prefer stating a **braiding** where you can:
   `IsBraidedOver.isUniversalKExtension` then gives universality at every `t`, which is what makes
   `krsa_ascent_iso` (`V^κ(C) ≅ F_κ(B)`, across a universe gap) provable via
   `isUniversalKExtension_unique'`.
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
12. **A term whose type unfolds to a `∀` has its implicits inserted eagerly.** `IsLambdaSmall`
    unfolds to `∀ {ι}, …`, so `exact h` against the goal `a ∈ C.lambdaSmallPart lam` applies `h` to a
    fresh `?ι` and then fails by one binder. `show IsLambdaSmall R lam (C.rep a)` first, then
    `exact`. Same shape as trap 7, and it also explains why `IsLambdaSmall.of_prod_left`/`of_equiv`
    need their `M`, `M'` given by name in that position.
13. **`IsLSubset` is a `Prop`**, so two proofs that the same subset is `λ⁻`-closed give
    *definitionally equal* `IsLSubset.lmonoid` instances. That is what makes
    `IsBraidedOver.of_set_eq` a one-line `subst`, and it is the cheap way to move a braiding along an
    equality of subsets — no `of_base_iso` needed.
14. **`tsum` is cross-universe friendly**: `Equiv.tsum_eq` and the `ENNReal.tsum_*` lemmas accept
    index types in different universes, which is what lets an `ℕ`-indexed construction be
    transported to `ι : Type u`.

15. **Carry a repeated `letI` as an instance.** `add x` at `κ = ℵ₀` had its `LMonoid` structure
    written out by hand in 42 statements before `KMonoid.instLMonoidAddOf`. Because `IsLSubset` is a
    `Prop` (trap 13), two such structures are definitionally equal, so promoting one to an instance
    is free — no proof that relied on the defeq moves. Check the head is specific enough (`↥(addOf
    …)`) that instance search is not slowed.

## Where things live

The tree is layered by subject, not by paper section, and the layering is enforced by
`scripts/check_layering.sh` in CI: each layer may import only the layers below it, nothing below
`Modules/` may mention a module, and only `Axioms/*` and `Modules/Small.lean` may `import Mathlib`.

| Layer | Contents |
|---|---|
| `ForMathlib/` | no `κ`-monoid content, no repo dependencies, never rebuilt: `TraceIdeal.lean`, `NatBlocks.lean`, `Finprod.lean`, and the retired axioms `FreeRank.lean` (A1), `HomDirectSum.lean` + `SimpleMultiplicity.lean` (A3), `CyclicMonoid.lean` (A4, and `C_{m,n}` as a monoid), `Kaplansky.lean` (A6), `Albrecht.lean` (A7) |
| `Core/` | the monoid theory: `Index`, `SumData`, `LMonoid`, `KMonoid`, `Subobject` (homs, `⟨S⟩_κ`, `IsLSubset`), `Bare`, `LHom`, `Cardinal` (`F_κ`), `Free`, `OrderUnit`, `Cyclic`, `AddOf` |
| `Braiding/` | `Defs` (`BraidingData`, `IsBraided`, Lemma 3.6), `TransAleph0` (3.7, 3.8), `Sums` (3.2, 3.4, `mk_support_lt`), `TransUncountable`, `Over`, `UnivAux`, `Prop39`, `UnivExt` (Thm 3.11), `Saturated` (Lemma 3.13) |
| `Modules/` | `Small`, `DirectSum`, `Class`, `Theorem43`, `SmallPart`, `Projective` (Cor. 4.5, Kaplansky), `Corollary47`, and `Rings/` for §2.2–2.3 |
| `Examples/` | `TrivExt`, `ENNReal`, `Diophantine` (§3.2), `Reals` |
| `TwoGen/` | §5: `Forms`, `Prelim`, `Lemma52`, `Lemma51`, `Realization`, `Trace`, `Corollary55`, `Counterexample`.  Everything but `Lemma51` and after is monoid theory |
| `Axioms/` | `Modules` (A5 alone).  A1, A3, A4, A6 and A7 were here until they were proved — `ForMathlib/{FreeRank,SimpleMultiplicity,CyclicMonoid,Kaplansky,Albrecht}.lean` — and A2 until it was derived from A5 in `Modules/Rings/Leavitt.lean` |
| `Paper/` | the paper's numbered results and nothing else; nothing depends on it |

**When adding a result, put it in the lowest layer that can state it.**  A monoid-theoretic lemma
in a `Modules/` or `TwoGen/` file is how `add x` ended up behind axiom A5, and the layering check
will not catch that — it only catches imports.

**`Paper/` is the deliverable for a reader.**  `Paper/Section5.lean` restates §5 over `Setting5`,
which bundles the section's standing assumptions; `Paper/Section{2,3,4}.lean` are `alias` indices.
A new headline result belongs there too, and a numbered result that stops being formalised must
move to that file's "not formalised" section with a reason.

Before writing a new construction, check whether the analogous one exists: the `ℕ₀` and `ℝ≥0`
braidings, the `Fcard`/`RTilde` `SumData`s, and the `TrivExt` extension are all templates.

Anything with no `κ`-monoid content belongs in `KappaMonoid/ForMathlib/`, which imports only
Mathlib and so never gets rebuilt when the development changes.  Putting general lemmas in a leaf
file to dodge a `Basic.lean` rebuild is the wrong trade — it is how the trace ideals and the `ℕ`
block combinatorics ended up inside §5, and it cost a refactor to undo.
