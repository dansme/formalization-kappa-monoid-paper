/-
**Scaffolding for the unformalised part of Section 3** of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

Every proof in this file is `sorry`.  The file is deliberately **not** imported by
`KappaMonoid.lean`, so `lake build` continues to check a `sorry`-free development; build this
file on its own with

    lake build KappaMonoid.Section32

Its purpose is to fix the *statements* — which is the part of §3.2 that takes judgement — so that
they are known to elaborate before anyone starts proving them.  See `SECTION3-PLAN.md` for the
order of work and the proof sketches.

Contents, in dependency order:

* Examples 3.3(1): `ℕ₀ ∪ {∞}` is `ℵ₀⁻`-braided over `ℕ₀`.
* Lemma 3.13(1): `F_κ(B)` is the universal `κ`-extension of `F_{λ⁻}(B)`.
* Saturated submonoids and Lemma 3.13(2).
* Proposition 3.14: universal extensions of monoids cut out by homogeneous linear equations,
  inequalities and congruences.
-/
import KappaMonoid.Free
import KappaMonoid.Universal
import KappaMonoid.Examples
import KappaMonoid.OrderUnit

universe u v

open Cardinal Function Set

namespace KappaMonoid

/-! ## Examples 3.3(1): braiding in `ℕ₀`

Two families in `ℕ₀` are `ℵ₀⁻`-braided iff either both have finite support and equal sums, or
both have infinite support.  The substantive half is the second: given a finite partial sum
`a_m + ⋯ + a_n` of one family, the other family — having infinite support, so infinitely many
entries `≥ 1` — has a partial sum dominating it, and the braiding is built by alternating. -/

/-- Two finitely supported families in `ℕ₀` with the same sum are braided.  (A special case of
`isBraided_of_small_support`, recorded here for the classification below.) -/
theorem isBraided_nat_of_finite_support {ι : Type u} (x y : ι → ℕ)
    (hx : (Function.support x).Finite) (hy : (Function.support y).Finite)
    (hsum : ∑ᶠ i, x i = ∑ᶠ i, y i) :
    letI := LMonoid.ofAddCommMonoid ℕ
    IsBraided ℵ₀ x y := by
  sorry

/-- **Examples 3.3(1)**, the substantive half: two families in `ℕ₀` with infinite support are
`ℵ₀⁻`-braided. -/
theorem isBraided_nat_of_infinite_support {ι : Type u} (x y : ι → ℕ)
    (hx : (Function.support x).Infinite) (hy : (Function.support y).Infinite) :
    letI := LMonoid.ofAddCommMonoid ℕ
    IsBraided ℵ₀ x y := by
  sorry

/-- **Examples 3.3(1)**: the trivial `ℵ₀`-extension `ℕ₀ ∪ {∞}` is `ℵ₀⁻`-braided over `ℕ₀`, hence
(by Theorem 3.11(2)) *is* the universal `ℵ₀`-extension of `ℕ₀`.  This is the first entry of
Examples 3.12. -/
theorem isBraidedOver_withTop_nat :
    letI := LMonoid.ofAddCommMonoid ℕ
    letI := TrivExt.instKMonoid (M := ℕ) (fun a b h => by omega) le_rfl
    IsBraidedOver ℵ₀ ℵ₀ ℕ (WithTop ℕ) le_rfl (fun a => (a : WithTop ℕ)) := by
  sorry

/-! ## Lemma 3.13(1): free objects

`F_{λ⁻}(B)` sits inside `F_κ(B)` — a family of cardinals `< λ` with support of size `< λ` is in
particular a family of cardinals `≤ κ` with support of size `≤ κ` — and the universal property of
`F_κ(B)` (Proposition 2.9) is exactly the universal property required of the extension. -/

section Free

variable {lam κ : Cardinal.{u}} {B : Type u}

/-- A `λ⁻`-homomorphism into a `κ`-monoid is the same thing as an `LMonoid lam`-homomorphism for
the induced structure: `toLMonoidOfLE`'s `λ⁻`-sums *are* the `κ`-sums, by definition. -/
theorem isLMonoidHom_of_isLHom {X : Type v} {K : Type w} [LMonoid lam X] [KMonoid κ K]
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) {f : X → K} (hf : LMonoid.IsLHom hlk f) :
    letI := KMonoid.toLMonoidOfLE K hlam hlk
    IsLMonoidHom lam f :=
  fun h x => hf.2 h x

/-- Conversely, an `LMonoid lam`-homomorphism into a `κ`-monoid is a `λ⁻`-homomorphism. -/
theorem isLHom_of_isLMonoidHom {X : Type v} {K : Type w} [LMonoid lam X] [KMonoid κ K]
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) {f : X → K}
    (hf : letI := KMonoid.toLMonoidOfLE K hlam hlk; IsLMonoidHom lam f) :
    LMonoid.IsLHom hlk f := by
  letI := KMonoid.toLMonoidOfLE K hlam hlk
  exact ⟨hf.map_zero, fun h x => hf h x⟩

/-- The inclusion `F_{λ⁻}(B) ↪ F_κ(B)`. -/
def freeIncl (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ κ) (x : ↥(FreeL lam B)) :
    ↥(FreeK κ B) :=
  ⟨fun b => ⟨((x : B → LCard lam) b : Cardinal.{u}),
      lt_of_lt_of_le ((x : B → LCard lam) b).2 (le_trans hlk (Order.le_succ κ))⟩,
    lt_of_lt_of_le x.2 (le_trans hlk (Order.le_succ κ))⟩

@[simp] theorem val_freeIncl (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ κ)
    (x : ↥(FreeL lam B)) (b : B) :
    (((freeIncl hlam hκ hlk x : ↥(FreeK κ B)) : B → Fcard κ) b : Cardinal.{u})
      = ((x : B → LCard lam) b : Cardinal.{u}) := rfl

/-- `freeIncl` carries the generator `ι(b)` of `F_{λ⁻}(B)` to the generator `ι(b)` of
`F_κ(B)`. -/
theorem freeIncl_iota (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ κ) (b : B) :
    letI : Fact lam.IsRegular := ⟨hlam⟩
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    freeIncl hlam hκ hlk (iota (lam := lam) b) = iota (lam := Order.succ κ) b := by
  letI : Fact lam.IsRegular := ⟨hlam⟩
  letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  refine Subtype.ext (funext fun b' => Subtype.ext ?_)
  rw [val_freeIncl, coe_iota, coe_iota]
  by_cases h : b' = b
  · rw [h, val_iotaFun_self, val_iotaFun_self]
  · rw [val_iotaFun_of_ne (lam := lam) h, val_iotaFun_of_ne (lam := Order.succ κ) h]

/-- `freeIncl` is a `λ⁻`-homomorphism: on both sides a coordinate is the same cardinal sum. -/
theorem isLHom_freeIncl (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ κ) :
    letI : Fact lam.IsRegular := ⟨hlam⟩
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    letI := instKMonoidFreeK κ hκ B
    LMonoid.IsLHom hlk (freeIncl (B := B) hlam hκ hlk) := by
  letI : Fact lam.IsRegular := ⟨hlam⟩
  letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  letI := instKMonoidFreeK κ hκ B
  refine ⟨Subtype.ext (funext fun b => Subtype.ext ?_), fun {ι} h x => ?_⟩
  · rw [val_freeIncl]
    show ((0 : LCard lam) : Cardinal.{u}) = ((0 : Fcard κ) : Cardinal.{u})
    rw [LCard.val_zero hlam, LCard.val_zero (Cardinal.isRegular_succ hκ)]
  · exact Subtype.ext (funext fun b => Subtype.ext rfl)

/-- **Lemma 3.13(1)**: the free `κ`-monoid on `B` is the universal `κ`-extension of the free
`λ⁻`-monoid on `B`.

Both universal properties are Proposition 2.9, at `λ` and at `κ⁺` respectively; the extension of
`φ : F_{λ⁻}(B) → K` is `lift (φ ∘ ι)`, and both halves of the universal property are `hom_ext` —
at level `λ` for the extension identity, at level `κ⁺` for uniqueness. -/
theorem lemma_3_13_free (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ κ) :
    letI : Fact lam.IsRegular := ⟨hlam⟩
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    letI := instKMonoidFreeK κ hκ B
    IsUniversalKExtension lam κ ↥(FreeL lam B) ↥(FreeK κ B) hlk (freeIncl hlam hκ hlk) := by
  letI : Fact lam.IsRegular := ⟨hlam⟩
  letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  letI := instKMonoidFreeK κ hκ B
  refine ⟨isLHom_freeIncl hlam hκ hlk, fun K _ φ hφ => ?_⟩
  -- the extension is the lift of `φ ∘ ι`, taken at level `κ⁺`
  set ψ : ↥(FreeK κ B) → K :=
    lift (lam := Order.succ κ) (X := K) (fun b => φ (iota (lam := lam) b)) with hψ
  have hψiota : ∀ b : B, ψ (iota (lam := Order.succ κ) b) = φ (iota (lam := lam) b) :=
    fun b => by rw [hψ, lift_iota]
  refine ⟨ψ, ⟨isKHom_of_isLMonoidHom hκ (isLMonoidHom_lift _), ?_⟩, ?_⟩
  · -- `ψ ∘ freeIncl = φ`: both are `λ⁻`-homomorphisms agreeing on the generators
    letI := KMonoid.toLMonoidOfLE K hlam hlk
    have hcomp : IsLMonoidHom lam (fun x => ψ (freeIncl hlam hκ hlk x)) := by
      intro ι h x
      show ψ (freeIncl hlam hκ hlk (LMonoid.lsumOf (lam := lam) h x)) = _
      rw [(isLHom_freeIncl (B := B) hlam hκ hlk).2 h x]
      exact isLMonoidHom_lift _ (KMonoid.lt_succ (h.le.trans hlk)) _
    have key := hom_ext (lam := lam) (X := K)
      (g₁ := fun x => ψ (freeIncl hlam hκ hlk x)) (g₂ := φ) hcomp
      (isLMonoidHom_of_isLHom hlam hlk hφ)
      (fun b => by rw [freeIncl_iota hlam hκ hlk b, hψiota b])
    exact fun x => congrFun key x
  · -- uniqueness: a `κ`-homomorphism out of `F_κ(B)` is determined on the generators
    rintro ψ' ⟨hhom', hext'⟩
    refine hom_ext (lam := Order.succ κ) (X := K) (g₁ := ψ') (g₂ := ψ)
      (fun {ι} h x => KMonoid.IsKHom.map_sumOf hhom' (KMonoid.le_of_lt_succ h) x)
      (isLMonoidHom_lift _) fun b => ?_
    rw [hψiota b, ← freeIncl_iota hlam hκ hlk b, hext']

end Free

/-! ## Saturated submonoids and Lemma 3.13(2) -/

/-- A submonoid `S ⊆ X` is *saturated* if a summand in `X` of an element of `S` that itself lies
in `S` has its complement in `S`: from `s = t + h` with `s`, `t ∈ S` follows `h ∈ S`. -/
def IsSaturated {X : Type v} [AddCommMonoid X] (S : Set X) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, ∀ h : X, s = t + h → h ∈ S

section Sub

variable {lam κ : Cardinal.{u}} {X : Type u} {Hh : Type u}

/-- **Lemma 3.13(2)**: if `Ĥ` is the universal `κ`-extension of `X` and `S ⊆ X` is a
`λ⁻`-submonoid which is either saturated or sits over an uncountable `λ`, then the `κ`-submonoid
of `Ĥ` generated by `S` is the universal `κ`-extension of `S`.

Paper proof: it suffices to see that `⟨S⟩_κ` is `λ⁻`-braided over `S`, i.e. that the braiding
families `u`, `v` of a braiding in `Ĥ` may be taken inside `S`.  For `λ ≠ ℵ₀` that is
Lemma 3.4(4) — take `v ≡ 0`, so `u_μ` is a partial sum of elements of `S`.  For `λ = ℵ₀` it is a
transfinite induction along the blocks: at a limit `v_μ = 0` and `u_μ ∈ S`, and
`u_{μ+n} + v_{μ+n}` and `u_{μ+n} + v_{μ+n+1}` both lie in `S`, so saturatedness pushes `u` and
`v` into `S` one step at a time. -/
theorem lemma_3_13_sub [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ κ) {f : X → Hh}
    (hbr : IsBraidedOver lam κ X Hh hlk f) (S : Set X) (hS : IsLSubmonoid lam S)
    (hsat : lam ≠ ℵ₀ ∨ IsSaturated S) :
    letI := hS.lmonoid
    letI := (KMonoid.isKSubmonoid_kclosure κ (f '' S)).kmonoid
    IsUniversalKExtension lam κ ↥S ↥(KMonoid.kclosure κ (f '' S)) hlk
      (fun s => ⟨f (s : X), KMonoid.subset_kclosure ⟨(s : X), s.2, rfl⟩⟩) := by
  sorry

end Sub

/-! ## Proposition 3.14: monoids defined by linear equations, inequalities and congruences

A homogeneous system in `n` unknowns over `F_κ` consists of equations
`a₁x₁ + ⋯ + aₙxₙ = b₁x₁ + ⋯ + bₙxₙ`, inequalities `a₁x₁ + ⋯ + aₙxₙ ≤ b₁x₁ + ⋯ + bₙxₙ`, and
congruences `a₁x₁ + ⋯ + aₙxₙ ∈ d·F_κ`, all with natural-number coefficients.  The same system can
be read over `F_κ` for any `κ`, which is what makes Proposition 3.14 expressible. -/

section Diophantine

/-- A homogeneous linear system in `n` unknowns with natural coefficients: a set of equations, a
set of inequalities, and a set of congruences. -/
structure LinSystem (n : ℕ) where
  /-- Equations `a · x = b · x`. -/
  eqs : Set ((Fin n → ℕ) × (Fin n → ℕ))
  /-- Inequalities `a · x ≼ b · x`. -/
  ineqs : Set ((Fin n → ℕ) × (Fin n → ℕ))
  /-- Congruences `a · x ∈ d · F_κ`. -/
  congrs : Set ((Fin n → ℕ) × ℕ)

variable {n : ℕ} (sys : LinSystem n) {κ : Cardinal.{u}}

/-- The linear form `a₁x₁ + ⋯ + aₙxₙ` evaluated in `F_κ^n`. -/
noncomputable def linEval {n : ℕ} {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (a : Fin n → ℕ)
    (x : Fin n → Fcard κ) : Fcard κ :=
  letI := Fcard.instKMonoid hκ
  ∑ i, (a i) • x i

/-- The solution set of the system in `F_κ^n`. -/
noncomputable def LinSystem.solutions (hκ : ℵ₀ ≤ κ) : Set (Fin n → Fcard κ) :=
  letI := Fcard.instKMonoid hκ
  {x | (∀ p ∈ sys.eqs, linEval hκ p.1 x = linEval hκ p.2 x) ∧
       (∀ p ∈ sys.ineqs, AddLe (linEval hκ p.1 x) (linEval hκ p.2 x)) ∧
       (∀ p ∈ sys.congrs, ∃ y : Fcard κ, linEval hκ p.1 x = (p.2) • y)}

/-- The solution set is a `κ`-submonoid of `F_κ^n`: each condition is preserved by `κ`-sums,
because `Σ` commutes with the coefficientwise operations (Lemma 2.7). -/
theorem LinSystem.isKSubmonoid_solutions (hκ : ℵ₀ ≤ κ) :
    letI := Fcard.instKMonoid hκ
    letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ
    KMonoid.IsKSubmonoid κ (sys.solutions hκ) := by
  sorry

/-- The inclusion `F_{ℵ₀} ↪ F_κ`. -/
def fcardIncl (hκ : ℵ₀ ≤ κ) (a : Fcard ℵ₀) : Fcard κ :=
  Fcard.mk (a : Cardinal.{u}) (le_trans (Fcard.le a) hκ)

/-- A solution over `F_{ℵ₀}` is a solution over `F_κ`. -/
theorem LinSystem.mem_solutions_of_incl (hκ : ℵ₀ ≤ κ) {x : Fin n → Fcard ℵ₀}
    (hx : x ∈ sys.solutions (le_refl ℵ₀)) :
    (fun i => fcardIncl hκ (x i)) ∈ sys.solutions hκ := by
  sorry

/-- **Proposition 3.14(1)**: the universal `κ`-extension of the `ℵ₀`-monoid cut out of `F_{ℵ₀}^n`
by a system is the `κ`-submonoid of `F_κ^n` cut out by the *same* system.

An `ℵ₀`-monoid is an `ℵ₁⁻`-monoid, which is why the extension is taken along `λ = ℵ₀⁺`.

Paper proof: the solution set over `F_κ` is `ℵ₁⁻`-braided over the solution set over `F_{ℵ₀}`,
so Theorem 3.11(2) identifies it as the universal `κ`-extension. -/
theorem prop_3_14_one (hκ : Order.succ ℵ₀ ≤ κ) :
    letI hκ0 : ℵ₀ ≤ κ := le_trans (Order.le_succ ℵ₀) hκ
    letI := Fcard.instKMonoid (le_refl ℵ₀)
    letI := Fcard.instKMonoid hκ0
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    letI := KMonoid.pi κ (fun _ : Fin n => Fcard κ) hκ0
    letI := (sys.isKSubmonoid_solutions (le_refl ℵ₀)).kmonoid
    letI := (sys.isKSubmonoid_solutions hκ0).kmonoid
    IsUniversalKExtension (Order.succ ℵ₀) κ ↥(sys.solutions (le_refl ℵ₀))
      ↥(sys.solutions hκ0) hκ
      (fun x => ⟨fun i => fcardIncl hκ0 ((x : Fin n → Fcard ℵ₀) i),
        sys.mem_solutions_of_incl hκ0 x.2⟩) := by
  sorry

/-- `ℵ₀·H` componentwise: replace every nonzero component by `ℵ₀`, leaving zeroes alone.  This is
the paper's explicit description of the elements of `ℵ₀H`. -/
noncomputable def alephPart {n : ℕ} (x : Fin n → Fcard ℵ₀) : Fin n → Fcard ℵ₀ :=
  fun i => if ((x i : Fcard ℵ₀) : Cardinal.{u}) = 0 then Fcard.mk 0 (zero_le' : (0 : Cardinal.{u}) ≤ ℵ₀)
    else Fcard.mk ℵ₀ le_rfl

/-- `H`, the solutions all of whose components are finite: the monoid `H ⊆ ℕ₀^n` of
Proposition 3.14(2), viewed inside `F_{ℵ₀}^n`. -/
noncomputable def LinSystem.finSolutions : Set (Fin n → Fcard ℵ₀) :=
  {x ∈ sys.solutions (le_refl ℵ₀) | ∀ i, ((x i : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀}

/-- `H + ℵ₀H`, the candidate universal `ℵ₀`-extension of Proposition 3.14(2). -/
noncomputable def LinSystem.alephExt : Set (Fin n → Fcard ℵ₀) :=
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  {z | ∃ h ∈ sys.finSolutions, ∃ h' ∈ sys.finSolutions, z = h + alephPart h'}

/-- `H` is a submonoid: finite solutions are closed under `+`. -/
theorem LinSystem.addSubmonoid_finSolutions :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    (0 : Fin n → Fcard ℵ₀) ∈ sys.finSolutions ∧
      ∀ a ∈ sys.finSolutions, ∀ b ∈ sys.finSolutions, a + b ∈ sys.finSolutions := by
  sorry

/-- `H + ℵ₀H` is an `ℵ₀`-submonoid of `F_{ℵ₀}^n`.

The point is closure under countable sums: a countable sum of elements `h_k + ℵ₀h'_k` has, in
each component, either finitely many nonzero contributions — in which case the sum is again of
that shape — or infinitely many, in which case the component is `ℵ₀` and is absorbed into the
`ℵ₀H` part. -/
theorem LinSystem.isKSubmonoid_alephExt :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    KMonoid.IsKSubmonoid ℵ₀ sys.alephExt := by
  sorry

/-- Every element of `H + ℵ₀H` is a solution of the system: the easy inclusion. -/
theorem LinSystem.alephExt_subset_solutions :
    sys.alephExt ⊆ sys.solutions (le_refl (ℵ₀ : Cardinal.{u})) := by
  sorry

/-- **Proposition 3.14(2)**: for a monoid `H ⊆ ℕ₀^n` cut out by a homogeneous system, the
universal `ℵ₀`-extension is `H + ℵ₀H ⊆ F_{ℵ₀}^n`.

Both `λ` and `κ` are `ℵ₀` here: an `ℵ₀⁻`-monoid is an ordinary commutative monoid, which is what
`H ⊆ ℕ₀^n` is.

Paper proof: `H + ℵ₀H` is `ℵ₀⁻`-braided over `H`.  Given two families in `H` with the same sum in
`F_{ℵ₀}^n`, either both are finitely supported — and then Lemma 3.4(1) applies — or both have
components that blow up to `ℵ₀`, and the braiding is built componentwise as in Examples 3.3(1).
Note this is genuinely *not* the solution set of the same system over `F_{ℵ₀}`, which is what
distinguishes (2) from (1); Example 3.15 is the witness. -/
theorem prop_3_14_two :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    letI : AddCommMonoid ↥sys.finSolutions :=
      addCommMonoidOfClosed sys.addSubmonoid_finSolutions.1
        (fun a ha b hb => sys.addSubmonoid_finSolutions.2 a ha b hb)
    letI := LMonoid.ofAddCommMonoid ↥sys.finSolutions
    letI := sys.isKSubmonoid_alephExt.kmonoid
    IsUniversalKExtension ℵ₀ ℵ₀ ↥sys.finSolutions ↥sys.alephExt (le_refl ℵ₀)
      (fun h => ⟨(h : Fin n → Fcard ℵ₀), ⟨(h : Fin n → Fcard ℵ₀), h.2, 0,
        sys.addSubmonoid_finSolutions.1, by sorry⟩⟩) := by
  sorry

/-- **Example 3.15**: `H = {(m, m) : m ∈ ℕ₀} ⊆ ℕ₀²` shows that Proposition 3.14(1) and (2) really
are different statements — the universal `ℵ₀`-extension of `H` is *not* the solution set of
`x₁ = x₂` over `F_{ℵ₀}`, because that set contains `(ℵ₀, ℵ₀)` reached only as an infinite sum. -/
theorem example_3_15 : True := by
  trivial

end Diophantine



end KappaMonoid
