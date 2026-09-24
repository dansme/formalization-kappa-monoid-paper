/-
**Standard modules and their normal form** (Bergman §4, Proposition 4.1 and Proposition 2.1).

For a family of modules `N_μ` over `R_μ` with homogeneous `k`-bases, the *standard module*
`Std = ⊕_μ C ⊗_{R_μ} N_μ` is constructed directly on the `k`-vector space with basis the
monomials: `R_μ` acts through the `k`-linear isomorphism

  `Φ μ : Std ≅ N_μ ⊕ ⊕_{u, side u ≠ μ} R_μ e_{left u}`

(a monomial `s ∈ S_μ` goes to `s`, a monomial `u` of another side to `e_{left u}` at `u`, and
`t u` with `t` a letter of `R_μ` to `t` at `u`), and `C` acts by the universal property of the
coproduct.  The construction gives at once

* the universal property of standard modules (`Std.exists_unique_lift`),
* the normal form (the monomials are a `k`-basis),
* Proposition 2.1: `N_μ → Std` is injective and `Std = N_μ ⊕ (free R_μ-module)` over `R_μ`.
-/
import KappaMonoid.Bergman.Core.Mono

universe u

namespace Bergman.Core

open Module

variable {k : Type u} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  (σ : ∀ l, (ι → k) →ₐ[k] R l) [Fact (∀ l, Function.Injective (σ l))]
  {C : Type u} [Ring C] [Algebra k C] (σC : (ι → k) →ₐ[k] C) (inc : ∀ l, R l →ₐ[k] C)
  [Fact (IsCoprod k σ C σC inc)]

/-- The structure maps `R_μ → C`. -/
def incμ : ∀ μ : Option Λ, Rμ k ι R μ →ₐ[k] C
  | none => σC
  | some l => inc l

variable (N : Option Λ → Type u) [∀ μ, AddCommGroup (N μ)] [∀ μ, Module (Rμ k ι R μ) (N μ)]
  [∀ μ, Module k (N μ)] [∀ μ, IsScalarTower k (Rμ k ι R μ) (N μ)]

/-- `e_j N_μ`, a `k`-subspace. -/
def eSub (μ : Option Λ) (j : ι) : Submodule k (N μ) where
  carrier := {x | eμ σ μ j • x = x}
  add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [smul_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha; simp only [Set.mem_setOf_eq] at *
    rw [smul_comm, ha]

/-- Homogeneous `k`-bases of the modules `N_μ`: a basis of each `e_j N_μ`. -/
structure HomBases where
  /-- The index types. -/
  S : Option Λ → ι → Type u
  /-- The bases. -/
  b : ∀ μ j, Basis (S μ j) k (eSub σ N μ j)

theorem nonempty_homBases : Nonempty (HomBases σ N) := sorry

variable {σ N} (B : HomBases σ N)

/-- The homogeneous basis of `N_μ`, `N_μ = ⊕_j e_j N_μ`. -/
noncomputable def HomBases.basis (μ : Option Λ) : Basis (Σ j, B.S μ j) k (N μ) := sorry

theorem HomBases.basis_mem (μ : Option Λ) (j : ι) (s : B.S μ j) :
    B.basis μ ⟨j, s⟩ ∈ eSub σ N μ j := sorry

/-- **The standard module** on the family `N`, with the monomial basis. -/
@[nolint unusedArguments]
def Std (_σC : (ι → k) →ₐ[k] C) (_inc : ∀ l, R l →ₐ[k] C) (B : HomBases σ N) : Type u :=
  Mono σ B.S →₀ k

noncomputable instance : AddCommGroup (Std σC inc B) := inferInstanceAs (AddCommGroup (Mono σ B.S →₀ k))

noncomputable instance : Module k (Std σC inc B) := inferInstanceAs (Module k (Mono σ B.S →₀ k))

/-- A monomial, as an element of the standard module. -/
noncomputable def Std.mono (w : Mono σ B.S) : Std σC inc B := Finsupp.single w 1

/-- The monomials form a `k`-basis. -/
noncomputable def Std.monoBasis : Basis (Mono σ B.S) k (Std σC inc B) := Finsupp.basisSingleOne

/-! ## The action of `R_μ` -/

/-- The monomials not on side `μ`: Bergman's `U_{~μ}`. -/
abbrev NotSide (μ : Option Λ) : Type u := {w : Mono σ B.S // w.side ≠ μ}

/-- `⊕_{u ∈ U_{~μ}} R_μ e_{left u}`, the free part of `Std` over `R_μ`. -/
abbrev FreePart (μ : Option Λ) : Type u :=
  Π₀ u : NotSide B μ, ↥(Submodule.span (Rμ k ι R μ) {eμ σ μ u.1.left})

/-- The three kinds of monomial relative to `μ`. -/
noncomputable def monoSplit (μ : Option Λ) :
    Mono σ B.S ≃ (Σ j, B.S μ j) ⊕ Σ u : NotSide B μ, Option (Σ i, Tl σ μ i u.1.left) := sorry

/-- **`Std = N_μ ⊕ (free R_μ-module)`**, as `k`-spaces. -/
noncomputable def Std.Φ (μ : Option Λ) : Std σC inc B ≃ₗ[k] N μ × FreePart B μ := sorry

/-- The action of `R_μ` on `Std`, transported along `Φ μ`. -/
noncomputable def Std.act (μ : Option Λ) : Rμ k ι R μ →ₐ[k] Module.End k (Std σC inc B) := sorry

theorem Std.act_compat (l : Λ) :
    (Std.act σC inc B (some l)).comp (σ l) = Std.act σC inc B none := sorry

/-- The action of `C`, from the universal property of the coproduct. -/
noncomputable def Std.toEnd : C →ₐ[k] Module.End k (Std σC inc B) := sorry

noncomputable instance : Module C (Std σC inc B) :=
  Module.compHom (Std σC inc B) (Std.toEnd σC inc B).toRingHom

instance : IsScalarTower k C (Std σC inc B) := sorry

theorem Std.incμ_smul (μ : Option Λ) (r : Rμ k ι R μ) (x : Std σC inc B) :
    incμ σC inc μ r • x = Std.act σC inc B μ r x := sorry

theorem Std.Φ_incμ_smul (μ : Option Λ) (r : Rμ k ι R μ) (x : Std σC inc B) :
    Std.Φ σC inc B μ (incμ σC inc μ r • x) = r • Std.Φ σC inc B μ x := sorry

/-! ## The components and the universal property -/

/-- The inclusion `N_μ → Std`, `s ↦ s` on basis elements. -/
noncomputable def Std.incl (μ : Option Λ) : N μ →ₗ[k] Std σC inc B := sorry

theorem Std.incl_basis (μ : Option Λ) (j : ι) (s : B.S μ j) :
    Std.incl σC inc B μ (B.basis μ ⟨j, s⟩) = Std.mono σC inc B
      (Mono.ofBase ⟨μ, j, s⟩) := sorry

theorem Std.incl_smul (μ : Option Λ) (r : Rμ k ι R μ) (n : N μ) :
    Std.incl σC inc B μ (r • n) = incμ σC inc μ r • Std.incl σC inc B μ n := sorry

/-- **Proposition 2.1(1)**: `N_μ` embeds in `Std`. -/
theorem Std.incl_injective (μ : Option Λ) : Function.Injective (Std.incl σC inc B μ) := sorry

theorem Std.Φ_incl (μ : Option Λ) (n : N μ) :
    Std.Φ σC inc B μ (Std.incl σC inc B μ n) = (n, 0) := sorry

/-- Left multiplication by a letter on a monomial it may be applied to. -/
theorem Std.mono_cons (t : Letter σ) (w : Mono σ B.S) (h₁ h₂) :
    Std.mono σC inc B (Mono.cons t w h₁ h₂) =
      inc t.side t.val • Std.mono σC inc B w := sorry

/-- **The universal property of standard modules.** -/
theorem Std.exists_unique_lift (P : Type u) [AddCommGroup P] [Module C P] [Module k P]
    [IsScalarTower k C P] (g : ∀ μ, N μ →ₗ[k] P)
    (hg : ∀ μ (r : Rμ k ι R μ) (n : N μ), g μ (r • n) = incμ σC inc μ r • g μ n) :
    ∃! f : Std σC inc B →ₗ[C] P, ∀ μ n, f (Std.incl σC inc B μ n) = g μ n := sorry

/-- `Std` is generated by its components. -/
theorem Std.span_incl :
    Submodule.span C (⋃ μ, Set.range (Std.incl σC inc B μ)) = ⊤ := sorry

end Bergman.Core
