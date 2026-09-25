/-
**Standard presentations** (Bergman §§1–2, without tensor products).

A *standard presentation* of a `C`-module `M` is a family of `R_μ`-modules `A μ` with
`R_μ`-linear maps `j μ : A μ → M` having the universal property of `⊕_μ C ⊗_{R_μ} A μ`: every
family of `R_μ`-linear maps `A μ → P` into a `C`-module extends uniquely to a `C`-linear map
`M → P`.  Bergman thinks of this as a distinguished family of `R_μ`-submodules of `M` generating it
"freely" (§1); keeping `M` fixed and changing the presentation is how basic transfers and
transvections act (the remark after Theorem 2.3).

`StdPres.Step` records how the isomorphism types of the components change under one basic
transfer (a summand `R_λ e_j` of `A λ` becomes a summand `k^ι e_j` of `A none`, or conversely) or
under a transvection (no change).  Corollary 2.6 and Theorem 2.3, in terms of these, are in
`Core/Main.lean`.
-/
import KappaMonoid.Bergman.Core.Std

universe u

set_option linter.unusedSectionVars false

namespace Bergman.Core

open Module

variable {k : Type u} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  (σ : ∀ l, (ι → k) →ₐ[k] R l) [Fact (∀ l, Function.Injective (σ l))]
  {C : Type u} [Ring C] [Algebra k C] (σC : (ι → k) →ₐ[k] C) (inc : ∀ l, R l →ₐ[k] C)
  [Fact (IsCoprod k σ C σC inc)]

/-- The left ideal `R_μ e_j`. -/
abbrev lid (μ : Option Λ) (j : ι) : Submodule (Rμ k ι R μ) (Rμ k ι R μ) :=
  Submodule.span (Rμ k ι R μ) {eμ σ μ j}

variable (M : Type u) [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]

/-- A **standard presentation** of the `C`-module `M`. -/
structure StdPres where
  /-- The ring is a coproduct (records `σ`). -/
  coprod : IsCoprod k σ C σC inc
  /-- The components. -/
  A : Option Λ → Type u
  [addCommGroup : ∀ μ, AddCommGroup (A μ)]
  [module : ∀ μ, Module (Rμ k ι R μ) (A μ)]
  [moduleK : ∀ μ, Module k (A μ)]
  [tower : ∀ μ, IsScalarTower k (Rμ k ι R μ) (A μ)]
  /-- The maps into `M`. -/
  j : ∀ μ, A μ →ₗ[k] M
  j_smul : ∀ μ (r : Rμ k ι R μ) a, j μ (r • a) = incμ σC inc μ r • j μ a
  /-- The universal property of `⊕_μ C ⊗_{R_μ} A μ`. -/
  lift : ∀ (P : Type u) [AddCommGroup P] [Module C P] [Module k P] [IsScalarTower k C P]
    (g : ∀ μ, A μ →ₗ[k] P), (∀ μ (r : Rμ k ι R μ) a, g μ (r • a) = incμ σC inc μ r • g μ a) →
    ∃! f : M →ₗ[C] P, ∀ μ a, f (j μ a) = g μ a

attribute [instance] StdPres.addCommGroup StdPres.module StdPres.moduleK StdPres.tower

variable {σ σC inc M}

/-- The components are finitely generated. -/
def StdPres.FG (p : StdPres σ σC inc M) : Prop := ∀ μ, Module.Finite (Rμ k ι R μ) (p.A μ)

/-- The components are finitely generated and projective. -/
def StdPres.FGP (p : StdPres σ σC inc M) : Prop :=
  ∀ μ, Module.Finite (Rμ k ι R μ) (p.A μ) ∧ Module.Projective (Rμ k ι R μ) (p.A μ)

/-- The components of `p` and `q` are isomorphic, for all `μ` except possibly those in `s`. -/
def StdPres.IsoExcept (p : StdPres σ σC inc M) {M' : Type u} [AddCommGroup M'] [Module C M']
    [Module k M'] [IsScalarTower k C M'] (q : StdPres σ σC inc M') (s : Set (Option Λ)) : Prop :=
  ∀ μ ∉ s, Nonempty (p.A μ ≃ₗ[Rμ k ι R μ] q.A μ)

/-- **One basic transfer or transvection**, on the isomorphism types of the components:
a transvection changes nothing; a transfer moves a summand `R_λ e_j` of `A λ` to a summand
`k^ι e_j` of `A none`, or conversely. -/
def StdPres.Step (p p' : StdPres σ σC inc M) : Prop :=
  p.IsoExcept p' ∅ ∨
  (∃ (l : Λ) (j : ι), p.IsoExcept p' {none, some l} ∧
    Nonempty (p.A (some l) ≃ₗ[Rμ k ι R (some l)] p'.A (some l) × lid σ (some l) j) ∧
    Nonempty (p'.A none ≃ₗ[Rμ k ι R none] p.A none × lid σ none j)) ∨
  (∃ (l : Λ) (j : ι), p.IsoExcept p' {none, some l} ∧
    Nonempty (p.A none ≃ₗ[Rμ k ι R none] p'.A none × lid σ none j) ∧
    Nonempty (p'.A (some l) ≃ₗ[Rμ k ι R (some l)] p.A (some l) × lid σ (some l) j))

/-- Reachability by finitely many transfers and transvections. -/
def StdPres.Reach : StdPres σ σC inc M → StdPres σ σC inc M → Prop := Relation.ReflTransGen StdPres.Step

variable (σC inc) in
/-- The explicit standard module is standard. -/
noncomputable def Std.pres {N : Option Λ → Type u} [∀ μ, AddCommGroup (N μ)]
    [∀ μ, Module (Rμ k ι R μ) (N μ)] [∀ μ, Module k (N μ)]
    [∀ μ, IsScalarTower k (Rμ k ι R μ) (N μ)] (B : HomBases σ N) :
    StdPres σ σC inc (Std σC inc B) where
  coprod := Fact.out
  A := N
  j := Std.incl σC inc B
  j_smul := Std.incl_smul σC inc B
  lift P _ _ _ _ g hg := Std.exists_unique_lift σC inc B P g hg

end Bergman.Core
