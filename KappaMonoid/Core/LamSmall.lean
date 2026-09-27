/-
The `lam_small` tactic: side conditions `#ι < λ` for index types built from small pieces.

Every `λ⁻`-sum `lsumOf h x` carries a proof `h : #ι < λ`.  When `ι` is built from index types
already known to be small, that proof is bookkeeping the paper never writes: `ι × J` is small
because `ι` and `J` are.  `lam_small` proves such goals, and lemmas take it as the default value of
their cardinality hypotheses (`(h : #(ι × J) < lam := by lam_small)`), so callers may omit them.
Proof irrelevance makes this safe: any two proofs of `#ι < λ` are equal, so it does not matter
which one the tactic finds.

Facts that some *piece* of a construction is small, such as `BraidingData.I_small`, are
registered with the attribute `@[lam_small_rule]`, and the tactic uses them as well as hypotheses
of the form `∀ p, #(I p) < λ`.

The notation `∑[λ] i ∈ S, f i` (and `∑[λ] i : ι, f i`, `∑[λ] i, f i`) is the `λ⁻`-sum with its bound found by
`lam_small`: the paper's `Σ_{i ∈ S} f_i`, with the standing convention `|S| < λ` left implicit.
-/
import KappaMonoid.Core.SumData

open Cardinal

/-- Facts `#(P p) < λ` about the pieces of a construction, for `lam_small` to use. -/
register_label_attr lam_small_rule

namespace KappaMonoid

/-- The structural part of `lam_small`, given a proof `reg` of `lam.IsRegular`.  Closes
`#ι < lam` by a hypothesis, by finiteness, or by splitting a product, disjoint union, sigma type or
union of sets into its pieces.  `reg` is passed along rather than put into the context, so that a
goal closed by a hypothesis `h` gets exactly `h` as its proof term: a statement written with the
notation below is then the same term as one written with `h`, and callers can still leave `h` to
unification. -/
syntax "lam_small_core " term:max : tactic

-- `hygiene false`: the attribute name `lam_small_rule` must reach `solve_by_elim` unrenamed
set_option hygiene false in
macro_rules
  | `(tactic| lam_small_core $reg) => `(tactic| first
      | assumption
      | exact KappaMonoid.mk_lt_of_finite $reg _
      | exact lt_of_eq_of_lt (KappaMonoid.mk_Idx _) ‹_›
      | solve_by_elim (exfalso := false) (symm := false) (maxDepth := 3) using lam_small_rule
      | (refine KappaMonoid.mk_prod_lt $reg ?_ ?_ <;> lam_small_core $reg)
      | (refine KappaMonoid.mk_sum_lt $reg ?_ ?_ <;> lam_small_core $reg)
      | (refine KappaMonoid.mk_sigma_lt $reg ?_ fun _ => ?_ <;> lam_small_core $reg)
      | (refine KappaMonoid.mk_union_lt $reg ?_ ?_ <;> lam_small_core $reg)
      | fail "lam_small: cannot split this goal into hypotheses and finite types")

open Lean Meta Elab Tactic in
/-- Proves `#ι < lam` when `ι` is built, by products, disjoint unions, sigma types and unions of
sets, from finite types, from hypotheses in the context (also of the form `∀ p, #(P p) < lam`) and
from facts registered with `@[lam_small_rule]`.

The regularity of `lam`, which the product, sum and sigma rules need, is taken from a hypothesis
`lam.IsRegular` or from a `λ⁻`-monoid structure `[LMonoid lam X]` in the context. -/
elab "lam_small" : tactic => do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some (_, _, _, lam) := ty.app4? ``LT.lt
    | throwError "lam_small: the goal is not of the form `#ι < lam`"
  let reg ← mkAppM ``Cardinal.IsRegular #[lam]
  let mut proof? : Option Expr := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if ← isDefEq t reg then
      proof? := some d.toExpr
      break
    if t.isAppOfArity ``KappaMonoid.LMonoid 2 then
      if ← isDefEq t.appFn!.appArg! lam then
        proof? := some (← mkAppOptM ``KappaMonoid.LMonoid.isRegular #[lam, t.appArg!, d.toExpr])
        break
  let some proof := proof?
    | throwError "lam_small: no proof of `{lam}.IsRegular` and no `LMonoid {lam} _` in the context"
  let p ← Term.exprToSyntax proof
  evalTactic (← `(tactic| lam_small_core $p))

/-- `∑[lam] i ∈ S, f i` is the `λ⁻`-sum of `f` over the set `S`, its bound `#S < lam` found by
`lam_small`. -/
scoped syntax (name := lsumMem) "∑[" term "] " Lean.binderIdent " ∈ " term ", " term:67 : term

/-- `∑[lam] i : ι, f i` is the `λ⁻`-sum of `f` over the type `ι`, its bound `#ι < lam` found by
`lam_small`. -/
scoped syntax (name := lsumType) "∑[" term "] " Lean.binderIdent " : " term ", " term:67 : term

/-- `∑[lam] i, f i` is the `λ⁻`-sum of `f` over the index type determined by `f`, its bound found
by `lam_small`. -/
scoped syntax (name := lsum) "∑[" term "] " Lean.binderIdent ", " term:67 : term

macro_rules
  | `(∑[$lam] $i:ident ∈ $S, $f) =>
    `(KappaMonoid.LMonoid.lsumOf (lam := $lam) (by lam_small) (fun $i : ↥$S => $f))
  | `(∑[$lam] _ ∈ $S, $f) =>
    `(KappaMonoid.LMonoid.lsumOf (lam := $lam) (by lam_small) (fun _ : ↥$S => $f))
  | `(∑[$lam] $i:ident : $ι, $f) =>
    `(KappaMonoid.LMonoid.lsumOf (lam := $lam) (by lam_small) (fun $i : $ι => $f))
  | `(∑[$lam] _ : $ι, $f) =>
    `(KappaMonoid.LMonoid.lsumOf (lam := $lam) (by lam_small) (fun _ : $ι => $f))
  | `(∑[$lam] $i:ident, $f) =>
    `(KappaMonoid.LMonoid.lsumOf (lam := $lam) (by lam_small) (fun $i => $f))
  | `(∑[$lam] _, $f) =>
    `(KappaMonoid.LMonoid.lsumOf (lam := $lam) (by lam_small) (fun _ => $f))

end KappaMonoid
