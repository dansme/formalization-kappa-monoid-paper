/-
The `lam_small` tactic: side conditions `#ι < λ` for index types built from small pieces.

Every `λ⁻`-sum `lsumOf h x` carries a proof `h : #ι < λ`.  When `ι` is built from index types
already known to be small, that proof is bookkeeping the paper never writes: `ι × J` is small
because `ι` and `J` are.  `lam_small` proves such goals, and lemmas take it as the default value of
their cardinality hypotheses (`(h : #(ι × J) < lam := by lam_small)`), so callers may omit them.
Proof irrelevance makes this safe: any two proofs of `#ι < λ` are equal, so it does not matter
which one the tactic finds.
-/
import KappaMonoid.Core.SumData

open Cardinal

namespace KappaMonoid

/-- The structural part of `lam_small`, run once a proof of `lam.IsRegular` is in the context.
Closes `#ι < lam` by a hypothesis, by finiteness, or by splitting a product, disjoint union, sigma
type or union of sets into its pieces. -/
syntax "lam_small_core" : tactic

macro_rules
  | `(tactic| lam_small_core) => `(tactic| first
      | assumption
      | exact KappaMonoid.mk_lt_of_finite ‹_› _
      | (refine KappaMonoid.mk_prod_lt ‹_› ?_ ?_ <;> lam_small_core)
      | (refine KappaMonoid.mk_sum_lt ‹_› ?_ ?_ <;> lam_small_core)
      | (refine KappaMonoid.mk_sigma_lt ‹_› ?_ fun _ => ?_ <;> lam_small_core)
      | (refine KappaMonoid.mk_union_lt ‹_› ?_ ?_ <;> lam_small_core)
      | fail "lam_small: cannot split this goal into hypotheses and finite types")

open Lean Meta Elab Tactic in
/-- Proves `#ι < lam` when `ι` is built, by products, disjoint unions, sigma types and unions of
sets, from finite types and from index types whose smallness is a hypothesis in the context.

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
  evalTactic (← `(tactic| (have _hreg := $p; lam_small_core)))

end KappaMonoid
