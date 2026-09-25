# Working on this repository

A Lean 4 formalisation of Nazemian–Smertnig, *A monoid-theoretical approach to infinite direct-sum
decompositions of modules*. The paper is in the repo: `kappa_monoids.tex` (source of truth for
statements) and `kappa_monoids.pdf`.

`README.md` is the short, human-readable overview: status, the one assumed result, the differences
from the paper, what is deliberately not formalised, and the layer map.  Keep it short; detailed
rationale belongs in docstrings.

## Build

```fish
lake build                          # root target: must stay green and sorry-free
lake exe cache get                  # after any manifest bump, before lake build
./scripts/check_layering.sh         # the layer discipline; CI runs it too
lake env lean scripts/list_axioms.lean   # every `axiom` in the development; CI diffs it
lake build --no-build               # is the build up to date? (exit 0 = yes), no rebuild
```

A change low in the import graph is expensive: touching a file of `Bergman/` rebuilds all of
`Modules/`, `TwoGen/` and `Paper/` (~10 min), and touching `Core/` rebuilds nearly everything.
Batch such edits and build once.

`lake build` on a fresh checkout rebuilds Mathlib from source if the cache is missing — hours.
Run `lake exe cache get` first and check that `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/`
is populated.

The toolchain and Mathlib are pinned to `v4.33.0`; do not run `lake update` — bumps go through
`.github/workflows/update.yml`, by hand, as their own commit.

Every file is imported by `KappaMonoid.lean`, and CI rejects a `sorry` in the root target.  A file
still carrying one therefore joins the root only in the commit that removes its last `sorry`.

## Working efficiently

Most of the avoidable cost in a session is the edit/build/read loop, not the mathematics. The
`lean-lsp` MCP server (configured in `.mcp.json`, run via `uvx lean-lsp-mcp`) answers most of the
questions a build would answer, without a build. Prefer it throughout.

**Without the LSP** (it needs `uvx` on the `PATH`; the devcontainer image installs it, a container
built from an older image may not have it), the
cheap substitute is `lake env lean <file>`: it elaborates one file against the already-built oleans
of its imports, with no `lake build` — about 30–90 s, mostly import time.  Use it for a file you are
editing, and for a scratch file of `#check @foo`, `#print axioms foo` or test `example`s (put it in
the session scratchpad, not the repo).  Caveats: it reads the oleans as they are, so it does not see
unbuilt edits to the file's imports; and a new file importing another new file needs
`lake build KappaMonoid.X.NewFile` for the imported one first (building one new module is cheap).

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
   a time, not one at a time — at file scale as well as at block scale.
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
10. **Parallel work in one tree.** Several agents can work at once if each writes *new files only*
    and checks them with `lake env lean`; nobody runs `lake build` on an existing target, and nobody
    edits an existing file.  One person then integrates — imports in `KappaMonoid.lean` or the layer
    aggregator, the `Paper/` entries, `AxiomAudit.lean` — moves general lemmas to their proper layer,
    and builds once.  Never edit sources while a `lake build` is running: a module compiled late in
    the run picks up the half-finished edit.
11. **Inserting into the `Paper/` indices: never between a docstring and its `alias`.**  A
    substitution anchored on an `alias` line and inserting *before* it separates the docstring from
    its declaration; the error is `unexpected token '/--'; expected 'lemma'`.  Anchor on the `alias`
    line and insert after it.
12. **Docstrings drift from the paper.**  The paper has been revised, and docstrings that described
    an older version ("deviation", "correction to the paper", "the paper states this for a hereditary
    ring") survived long after they stopped being true.  When a docstring makes a claim about what
    the paper says, check it against `kappa_monoids.tex`, not against another docstring.

## Lean conventions

- **Universes**: index types `Type u`, carriers `Type v`, a second carrier `Type w`; cardinals
  `lam κ : Cardinal.{u}`. Declare universes at the top of the file rather than relying on
  auto-binding (see trap 5).
- **Prove at the `λ⁻` level and specialise to `κ`.** `KMonoid κ H` *is* `LMonoid (Order.succ κ) H`
  plus `ℵ₀ ≤ κ`, and `#ι ≤ κ ↔ #ι < Order.succ κ`.
- **Notation for the three ubiquitous idioms.** `ℵ₀∙x` is `KMonoid.cmul ℵ₀ le_rfl x` (the paper's
  `ℵ₀x`), `add(x)` is `KMonoid.addOf` at `κ = ℵ₀`, and `V(R)` is `projClass R ℵ₀ le_rfl`. All three
  are scoped `notation` in namespace `KappaMonoid`, not definitions: they expand to exactly the term
  that used to be written, so `rw` and every existing lemma still apply. State finite multiples as
  `n • x` (`KMonoid.cmul_natCast`) rather than `cmul (n : Cardinal) _ x`.
- **Docstrings** open with the bold paper reference — `**Lemma 3.14(2)**`, `**Examples 3.3(2)**` —
  and, when the argument is not obvious, carry a `Paper proof:` paragraph paraphrasing the source.
  This is the main navigation aid in the repo; keep it up.
- **Instances**: defs producing them carry `@[instance_reducible]`. Instances that depend on
  hypotheses are threaded through statements with `letI`, repeated at the top of the tactic proof —
  there as `let`, not `letI`, which Mathlib's `haveILetI` linter insists on inside a proof of a
  proposition. An anonymous `let := f x` sometimes leaves a universe metavariable where `letI :=`
  did not, because nothing inlines it into the goal; ascribe the type when that happens.
- **No axioms without asking.** The development declares none.  The Bergman–Dicks realisation
  theorem (`bergmanDicksData`), which the paper quotes and which used to be the one axiom, is proved
  in `KappaMonoid/Bergman/`; `BergmanDicksData` (`Bergman/Data.lean`) is its conclusion, and its
  `hereditary` field is the two-sided `IsHereditary`.  A new headline result gets a line in
  `KappaMonoid/Paper/AxiomAudit.lean` — `#assert_axioms foo []` — which is checked by the build and
  fails in both directions (update the count in `README.md` if you add lines).  CI enforces the
  list: `.github/workflows/lean_action_ci.yml` runs `scripts/list_axioms.lean`, which asks Lean for
  every `axiom` constant in a `KappaMonoid` module, and diffs it against the empty list; a
  deliberate addition means asking first, then editing that expected list *and* `README.md` in the
  same commit.
- **Left modules.** Mathlib's `Module R` is a left module and the paper's modules are right modules,
  so the paper's "right hereditary" is `IsLeftHereditary` here, and an unqualified "hereditary" is
  `IsHereditary`.  Every statement is the paper's statement for `Rᵐᵒᵖ`.
- **Anything the paper does not say is documented twice**: in the docstring of the affected result
  and as a one-line bullet in the "Differences from the paper" section of `README.md`, which is the
  authoritative list.  The current version of the paper states the four hypotheses that used to be
  deviations — `m ≥ 1` in Leavitt's theorem, `reduced` in Theorem 3.12, no inequalities in
  Proposition 3.15(2), `EveryProjectiveIsSumOfFG` in Theorem 5.3.  What remains are the places
  where the formalisation is deliberately *stronger* and the two hypotheses the paper leaves
  implicit (`κ > ℵ₀` in `LMonoid.ofCompatible`, `C` reduced in the §5 preamble).  Not every extra
  hypothesis is a deviation: `EveryProjectiveIsSumOfFG` in Corollary 5.5(1) and (3) is the paper's own condition,
  spelled out.  When the paper is wrong, formalise the repaired statement and say so; do not
  quietly weaken or restate it.

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
   instances there as `let`s.
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

15. **Carry a repeated `letI` as an instance.** `KMonoid.instLMonoidAddOf` is the `LMonoid`
    structure on `add x` at `κ = ℵ₀`, which otherwise has to be written out in every statement about
    it. Because `IsLSubset` is a `Prop` (trap 13), two such structures are definitionally equal, so
    promoting one to an instance is free — no proof that relied on the defeq moves. Check the head
    is specific enough (`↥(addOf …)`) that instance search is not slowed. The same was done at the
    fixed cardinal for `F_{ℵ₀}` (`Fcard.instKMonoidAleph0`), for `V^{ℵ₀}(R)`
    (`instKMonoidProjClassAleph0`) and for products (`KMonoid.instPiAleph0`); together they removed
    ~100 `letI`/`let` lines.

16. **A statement-level `letI` may be pinning a universe, not only carrying an instance.** In
    `Examples/`, `letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))` is the only mention of
    `Cardinal.{u}` in many statements; deleting it (now that the instance is global) leaves `ℵ₀`'s
    universe auto-bound afresh in *each* half of a conjunction, and the file fails with "contains
    universe level metavariables" a hundred lines later (trap 5). Where an instance is promoted,
    check whether the `letI` was load-bearing for universes before deleting it; there the
    statement-level `letI`s stay and only the proof-level ones go. Do not promote a structure whose
    carrier already has a Mathlib `AddCommMonoid` (`ℝ≥0`, `ℝ≥0∞`, `ℕ`): the promoted `LMonoid` would
    put a second `+` into instance search.

## Where things live

The tree is layered by subject, not by paper section, and the layering is enforced by
`scripts/check_layering.sh` in CI: each layer may import only the layers below it, nothing below
`Modules/` other than `Bergman/` may mention a module, and only `Modules/Small.lean` (and, until
their imports are trimmed, the files of `Bergman/`) may `import Mathlib`.

| Layer | Contents |
|---|---|
| `ForMathlib/` | no `κ`-monoid content, no repo dependencies, never rebuilt: `TraceIdeal.lean`, `NatBlocks.lean`, `Finprod.lean`, `Hereditary.lean` (`IsLeftHereditary`/`IsRightHereditary`/`IsHereditary`), `FreeRank.lean` (invariance of infinite rank), `HomDirectSum.lean` + `SimpleMultiplicity.lean` (multiplicities of simple modules), `CyclicMonoid.lean` (the classification, and `C_{m,n}` as a monoid), `Kaplansky.lean`, `Albrecht.lean`, `ProjectiveSplit.lean` (a surjection onto a projective splits; a one-sided inverse gives an idempotent), `CardinalSum.lean` (cardinal sums over a support, sums of naturals).  Mathlib has none of them |
| `Bergman/` | the Bergman–Dicks realisation theorem, ring theory with no `κ`-monoids; imports only Mathlib and `ForMathlib/`.  `Realization.lean` (the statement, `bergmanDicksData`, and the route), `MainRing` (the presented ring), `QuasiFree` (heredity), `Steps`/`Stages` (`V` one relation at a time), `Morita`, `Coprod`, and `Core/` for Bergman's coproduct theorem (§§4–9 of *Modules over coproducts of rings*: `Std`, `Support`, `Pure`, `Moves`, `Prop62`, `Prop82`, `Prop8`, `Main`) |
| `Core/` | the monoid theory: `Index`, `SumData`, `LMonoid`, `KMonoid`, `Subobject` (homs, `⟨S⟩_κ`, `IsLSubset`), `Bare`, `LHom`, `Cardinal` (`F_κ`), `Free`, `OrderUnit`, `Cyclic`, `AddOf`, `OrderUnitTransfer`, `OrderUnitIso`, `CyclicExtra` (Lemma 2.15 as a `κ`-iso), `Compatible` (Remark 2.19) |
| `Braiding/` | `Defs` (`BraidingData`, `IsBraided`, Lemma 3.6), `TransAleph0` (3.7, 3.8 at `λ = ℵ₀`), `Sums` (3.2, 3.4, `mk_support_lt`), `TransUncountable` (3.7, 3.8 at `λ > ℵ₀`, and the uniform statements), `Over`, `WellOrder` (Lemmas 3.4(2)(3) and 3.5: the `ι × ℕ` normal form *is* Definition 3.1(1) over any limit well-order), `UnivAux`, `Prop310`, `UnivExt` (Thm 3.12), `Saturated` (Lemma 3.14), `Components` (Remark 3.9), `BaseIso` (isomorphic bases, isomorphic extensions) |
| `Modules/` | `Small`, `DirectSum`, `Class`, `Theorem43`, `SmallPart`, `Projective` (Cor. 4.5, Kaplansky), `Corollary47`, `Transport` (Example 4.2, "`V^{ℵ₀}(R)` determines `V^κ(R)`", Cor. 4.6 hereditary), and `Rings/` for §2.2–2.3 (incl. `Progenerator`, `CyclicRealisable`) |
| `Examples/` | `TrivExt`, `ENNReal`, `NatBraiding` (Examples 3.3(1), `ℕ₀ ∪ {∞}`), `Diophantine` (§3.2, Examples 3.16 and 3.17), `NNReal` (braiding in `ℝ≥0`), `Reals` (`ℝ≥0 ∪ ℝ̃>0 ∪ {∞}`, and `ℚ≥0`), `RealsExtra`, `DiophantineExtra` (Examples 3.16, 3.17 in full, slack variables), `Dedekind` (Examples 4.8(4)) |
| `TwoGen/` | §5: `Forms`, `Prelim`, `Lemma52`, `Lemma51`, `Realization`, `Trace`, `Corollary55`, `Counterexample`, `Extra` (the §5 preamble, monoid side), `ExtraRealization`.  `Forms`, `Prelim`, `Lemma52`, `Counterexample` and `Extra` are pure monoid theory |
| `Paper/` | the paper's numbered results and nothing else; nothing depends on it.  Besides the four `Section` indices: `Definition21`/`Definition218` (literal transcriptions), `Section5Extra`, `Examples48` |

**When adding a result, put it in the lowest layer that can state it.**  A monoid-theoretic lemma
in a `Modules/` or `TwoGen/` file puts it needlessly behind the module theory, and the layering
check will not catch that — it only catches imports.

**`Paper/` is the deliverable for a reader.**  `Paper/Section5.lean` restates §5 over `Setting5`,
which bundles the section's standing assumptions, and `Section5Extra.lean` adds the unnumbered
claims of §5; `Paper/Section{2,3,4}.lean` are `alias` indices.  A new headline result belongs there
too, and a numbered result that stops being formalised must move to that file's "Not formalised"
section with a reason.  Index conventions:

- the docstring reads `**Item N.M(k)** — \`KappaMonoid.decl\`, in \`Dir/File.lean\`: <what it says>`;
- an alias that covers only part of an item says so (`generation clause only`, `λ = ℵ₀ only`, `the
  braiding clause`), so the index never overstates coverage;
- unnumbered claims the paper relies on get entries too (the "Unnumbered claims" block of
  `Section2.lean`, the prose entries of `Section3.lean`);
- an `alias` only checks that the declaration exists, not its type — `#check` it to see what it
  states.

**Keep the documents in step.**  When a result is added or a gap closed, update the `Paper/` entry,
the "Not formalised" section, the "What is not formalised" list in `README.md` (and its count of
`AxiomAudit` assertions).  `README.md` stays short and for humans; detail goes in docstrings.

Before writing a new construction, check whether the analogous one exists, and prefer the builder
to a hand-rolled `BraidingData`: `IsBraided.of_partition`, `of_levels`, `of_nat_blocks` (a bijection
`ℕ ≃ ι` plus two block-boundary sequences — this is Examples 3.3(1) and (2)) and `of_aggregation`
(pairwise disjoint small sets over which one family sums to the other — this is Proposition 3.10's
two braidings). The `Fcard`/`RTilde` `SumData`s and the `TrivExt` extension are the other
templates.

Anything with no `κ`-monoid content belongs in `KappaMonoid/ForMathlib/`, which imports only
Mathlib and so never gets rebuilt when the development changes.  Putting a general lemma in a leaf
file to dodge a rebuild of a lower layer is the wrong trade.
