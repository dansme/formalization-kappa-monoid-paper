/-
**Section 5: the counterexample `ℕ₀² ∪ {∞}`.**

Corollary 5.5(2) and 5.5(3) each assert "the converse is not true", both witnessed by the trivial
`ℵ₀`-extension of `ℕ₀²` with `x₁ = (1,0)`, `x₂ = (0,1)`.  That is Example 2.3(1), so the monoid is
`TrivExt.instKMonoid` from `KappaMonoid/Examples.lean`; what is proved here is that its two
generators are `add`-incomparable while `ℵ₀ x₂` still absorbs every `β x₁`, and that it has exactly
one element with an infinite form.
-/
import KappaMonoid.Section5.Forms

universe u v

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

/-! ## The counterexample `ℕ₀² ∪ {∞}`

Corollary 5.5(2) and 5.5(3) each assert "the converse is not true", both witnessed by the trivial
`ℵ₀`-extension of `ℕ₀²` with `x₁ = (1,0)`, `x₂ = (0,1)`.  That is Example 2.3(1), already
formalised in `KappaMonoid/Examples.lean`, so both are cheap — and worth doing early as a check on
the encoding above. -/

section Counterexample

/-- The underlying monoid `ℕ₀²` of the counterexample, lifted into `Type u`. -/
abbrev NatSq : Type u := ULift.{u} (ℕ × ℕ)

theorem isConical_natSq : IsConical NatSq.{u} := by
  rintro ⟨a⟩ ⟨b⟩ hab
  have h : a + b = (0 : ℕ × ℕ) := congrArg ULift.down hab
  have h1 : a.1 + b.1 = 0 := congrArg Prod.fst h
  have h2 : a.2 + b.2 = 0 := congrArg Prod.snd h
  have ha : a = (0, 0) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
  have hb : b = (0, 0) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
  exact ⟨congrArg ULift.up ha, congrArg ULift.up hb⟩

/-- `n` copies of `(a, b)` are `(n·a, n·b)`. -/
theorem nsmul_natSq (n a b : ℕ) : n • (⟨(a, b)⟩ : NatSq.{u}) = ⟨(n * a, n * b)⟩ := by
  induction n with
  | zero =>
      rw [zero_nsmul]
      show (0 : NatSq.{u}) = ⟨(0 * a, 0 * b)⟩
      rw [Nat.zero_mul, Nat.zero_mul]
      rfl
  | succ p hp =>
      rw [succ_nsmul, hp]
      show (⟨(p * a + a, p * b + b)⟩ : NatSq.{u}) = ⟨((p + 1) * a, (p + 1) * b)⟩
      rw [Nat.succ_mul, Nat.succ_mul]

/-- The counterexample `H := ℕ₀² ∪ {∞}`, the trivial `ℵ₀`-extension of `ℕ₀²`. -/
noncomputable instance : KMonoid (ℵ₀ : Cardinal.{u}) (WithTop NatSq.{u}) :=
  TrivExt.instKMonoid isConical_natSq le_rfl

/-- `x₁ = (1,0)`. -/
def cex₁ : WithTop NatSq.{u} := ((⟨(1, 0)⟩ : NatSq.{u}) : WithTop NatSq.{u})

/-- `x₂ = (0,1)`. -/
def cex₂ : WithTop NatSq.{u} := ((⟨(0, 1)⟩ : NatSq.{u}) : WithTop NatSq.{u})

/-- A nonzero element of `ℕ₀²` stays nonzero in `ℕ₀² ∪ {∞}`. -/
theorem coe_natSq_ne_zero {a b : ℕ} (h : a ≠ 0 ∨ b ≠ 0) :
    ((⟨(a, b)⟩ : NatSq.{u}) : WithTop NatSq.{u}) ≠ 0 := by
  intro hz
  have h0 : (⟨(a, b)⟩ : NatSq.{u}) = 0 := WithTop.coe_eq_zero.mp hz
  rcases h with h | h
  · exact h (congrArg (fun x : NatSq.{u} => x.down.1) h0)
  · exact h (congrArg (fun x : NatSq.{u} => x.down.2) h0)

theorem cex₁_ne_zero : cex₁.{u} ≠ 0 := coe_natSq_ne_zero (Or.inl one_ne_zero)

theorem cex₂_ne_zero : cex₂.{u} ≠ 0 := coe_natSq_ne_zero (Or.inr one_ne_zero)

/-- `n` copies of `x₁ = (1,0)` are `(n,0)`. -/
theorem cmul_cex₁ (n : ℕ) (h : ((n : ℕ) : Cardinal.{u}) ≤ ℵ₀) :
    KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u}) h cex₁.{u}
      = ((⟨(n, 0)⟩ : NatSq.{u}) : WithTop NatSq.{u}) := by
  have h1 : KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u}) h cex₁.{u} = n • cex₁.{u} :=
    KMonoid.cmul_natCast cex₁.{u} n
  rw [h1, cex₁, ← TrivExt.coe_nsmul, nsmul_natSq]
  norm_num

/-- `n` copies of `x₂ = (0,1)` are `(0,n)`. -/
theorem cmul_cex₂ (n : ℕ) (h : ((n : ℕ) : Cardinal.{u}) ≤ ℵ₀) :
    KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u}) h cex₂.{u}
      = ((⟨(0, n)⟩ : NatSq.{u}) : WithTop NatSq.{u}) := by
  have h1 : KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u}) h cex₂.{u} = n • cex₂.{u} :=
    KMonoid.cmul_natCast cex₂.{u} n
  rw [h1, cex₂, ← TrivExt.coe_nsmul, nsmul_natSq]
  norm_num

/-- In `ℕ₀² ∪ {∞}` a finite element divides another only coordinatewise. -/
theorem le_of_add_eq_coe (z : WithTop NatSq.{u}) (p q : ℕ × ℕ)
    (hz : ((⟨p⟩ : NatSq.{u}) : WithTop NatSq.{u}) + z = ((⟨q⟩ : NatSq.{u}) : WithTop NatSq.{u})) :
    p.1 ≤ q.1 ∧ p.2 ≤ q.2 := by
  have hzt : z ≠ ⊤ := by
    intro h
    rw [h, WithTop.add_top] at hz
    exact WithTop.top_ne_coe hz
  lift z to NatSq.{u} using hzt with z'
  rw [← WithTop.coe_add] at hz
  have h' : (⟨p⟩ : NatSq.{u}) + z' = ⟨q⟩ := WithTop.coe_injective hz
  have h1 : p.1 + z'.down.1 = q.1 := congrArg (fun x : NatSq.{u} => x.down.1) h'
  have h2 : p.2 + z'.down.2 = q.2 := congrArg (fun x : NatSq.{u} => x.down.2) h'
  omega

/-- In `ℕ₀² ∪ {∞}` the two generators have incomparable `add` sets. -/
theorem cex_incomparable :
    cex₁.{u} ∉ KMonoid.addOf (κ := ℵ₀) cex₂.{u} ∧
      cex₂.{u} ∉ KMonoid.addOf (κ := ℵ₀) cex₁.{u} := by
  constructor
  · rintro ⟨z, n, hzn⟩
    have hzn' : cex₁.{u} + z = ((⟨(0, n)⟩ : NatSq.{u}) : WithTop NatSq.{u}) :=
      hzn.trans (cmul_cex₂ n _)
    exact absurd (le_of_add_eq_coe z (1, 0) (0, n) hzn').1 (by omega)
  · rintro ⟨z, n, hzn⟩
    have hzn' : cex₂.{u} + z = ((⟨(n, 0)⟩ : NatSq.{u}) : WithTop NatSq.{u}) :=
      hzn.trans (cmul_cex₁ n _)
    exact absurd (le_of_add_eq_coe z (0, 1) (n, 0) hzn').2 (by omega)

/-- `ℵ₀` copies of either generator are `∞`. -/
theorem cmul_top_cex₁ : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₁.{u} = (⊤ : WithTop NatSq.{u}) :=
  TrivExt.cmul_top_eq_top isConical_natSq le_rfl cex₁_ne_zero

theorem cmul_top_cex₂ : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} = (⊤ : WithTop NatSq.{u}) :=
  TrivExt.cmul_top_eq_top isConical_natSq le_rfl cex₂_ne_zero

/-- Yet `ℵ₀ x₂ + β x₁ = ℵ₀ x₂` for every `β`, both sides being `∞`.  With `cex_incomparable`
this refutes the converse asserted in Corollary 5.5(3). -/
theorem cex_absorb (β : ℕ∞) :
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} + ecmul β cex₁.{u}
      = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} :=
  calc KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} + ecmul β cex₁.{u}
      = (⊤ : WithTop NatSq.{u}) + ecmul β cex₁.{u} := by rw [cmul_top_cex₂]
    _ = (⊤ : WithTop NatSq.{u}) := WithTop.top_add _
    _ = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} := cmul_top_cex₂.symm

/-- And `∞` is the only element with an infinite form, although `add x₁ ≠ add x₂`.  With
`cex_incomparable` this refutes the converse asserted in Corollary 5.5(2). -/
theorem cex_unique_infinite :
    (∀ F G : Form, F.IsInfinite → G.IsInfinite →
        eval cex₁.{u} cex₂.{u} F = eval cex₁.{u} cex₂.{u} G) ∧
      KMonoid.addOf (κ := ℵ₀) cex₁.{u} ≠ KMonoid.addOf (κ := ℵ₀) cex₂.{u} := by
  have htop : ∀ F : Form, F.IsInfinite → eval cex₁.{u} cex₂.{u} F = (⊤ : WithTop NatSq.{u}) := by
    intro F hF
    rcases hF with h | h
    · rw [eval, h, ecmul_top, cmul_top_cex₁, WithTop.top_add]
    · rw [eval, h, ecmul_top, cmul_top_cex₂, WithTop.add_top]
  refine ⟨fun F G hF hG => (htop F hF).trans (htop G hG).symm, fun hset => ?_⟩
  -- `x₁ ∈ add x₁`, so equality of the two sets would contradict incomparability
  exact cex_incomparable.1 (hset ▸ KMonoid.self_mem_addOf cex₁.{u})

end Counterexample

end TwoGen

end KappaMonoid
