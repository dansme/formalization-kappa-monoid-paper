import Mathlib

/-!
# The main results of Nazemian–Smertnig, from Mathlib alone

Z. Nazemian and D. Smertnig, *A monoid-theoretical approach to infinite direct-sum decompositions
of modules* (`kappa_monoids.tex`): the main theorems with every definition they need, from
Mathlib alone.  This is the challenge for the
[comparator](https://github.com/leanprover/comparator); `Comparator/Solution.lean` proves the
same statements, with the standard axioms only.

Conventions.
* `κ`, `λ` are cardinals in `Cardinal.{u}`.  The paper's index set `κ` is `Idx κ`, a type of
  cardinality `κ`; its well-order only names the index `0` of (A1) and (B1).
* Mathlib's modules are left modules, the paper's are right modules: each statement here is the
  paper's for the opposite ring.
* A ring, its modules and `κ` share the universe `u`.  Modules are objects of `ModuleCat.{u} R`.
* `V^κ(C)` is not built as a quotient.  "`H ≅ V^κ(C)`" is a choice `P : H → ModuleCat R` of one
  module in each isomorphism class, turning `Σ` into `⨁` (`IsVMonoidOf`).

The rest of the paper (lemmas, examples, Corollaries 4.4, 4.7, 5.5, …) is proved in the
library; see `KappaMonoid/Paper/`.
-/

universe u v w t

open Cardinal Set Function DirectSum

namespace KappaChallenge

/-- The paper's index set `κ`: a type of cardinality `κ`, well-ordered by the initial ordinal of
`κ`.  For infinite `κ` every element has a successor `Order.succ i`. -/
abbrev Idx (κ : Cardinal.{u}) : Type u := κ.ord.ToType

/-! ## §2: `κ`-monoids and `λ⁻`-monoids -/

/-- **Definition 2.1.**  For an infinite cardinal `κ`, a `κ`-monoid is a set `H` with an element
`0` and a map `Σ : H^κ → H` such that
* (A1) if `x i = 0` for all `i ≠ 0` (with `0` the least index), then `Σ x = x 0`;
* (A2) `Σ_i Σ_j x i j = Σ_k x (π⁻¹ k)` for every bijection `π : κ × κ → κ`. -/
class KMonoid (κ : outParam Cardinal.{u}) (H : Type v) extends Zero H where
  aleph0_le : ℵ₀ ≤ κ
  sum : (Idx κ → H) → H
  sum_single : ∀ (x : Idx κ → H) (i₀ : Idx κ), IsMin i₀ → (∀ i, i ≠ i₀ → x i = 0) → sum x = x i₀
  sum_sum : ∀ (x : Idx κ → Idx κ → H) (π : Idx κ × Idx κ ≃ Idx κ),
    sum (fun i => sum (x i)) = sum fun k => x (π.symm k).1 (π.symm k).2

/-- **Definition 2.18.**  For a regular cardinal `λ`, a `λ⁻`-monoid is a set `X` with an element
`0` and a map `Σ : X^(λ) → X` on the families `λ → X` of support `< λ`, such that
* (B1) if `x i = 0` for all `i ≠ 0` (with `0` the least index), then `Σ x = x 0`;
* (B2) if `x : λ × λ → X` has fewer than `λ` nonzero rows and fewer than `λ` nonzero columns and
  `π : λ × λ → λ` is a bijection, then `Σ_i Σ_j x i j = Σ_k x (π⁻¹ k)`.

`Σ` is taken to be a total function on `X^λ`.  Its values on families of support `≥ λ` are
irrelevant: no axiom and no statement below constrains or uses them. -/
class LMonoid (lam : outParam Cardinal.{u}) (X : Type v) extends Zero X where
  isRegular : lam.IsRegular
  sum : (Idx lam → X) → X
  sum_single : ∀ (x : Idx lam → X) (i₀ : Idx lam), IsMin i₀ → (∀ i, i ≠ i₀ → x i = 0) → sum x = x i₀
  sum_sum : ∀ x : Idx lam → Idx lam → X, #{i | ∃ j, x i j ≠ 0} < lam →
    #{j | ∃ i, x i j ≠ 0} < lam → ∀ π : Idx lam × Idx lam ≃ Idx lam,
      sum (fun i => sum (x i)) = sum fun k => x (π.symm k).1 (π.symm k).2

namespace KMonoid

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

open Classical in
/-- `∑ i : ι, x i` for an index type `ι` of cardinality `≤ κ`: the `κ`-sum of `x`, padded with
zeros along some injection `ι ↪ κ`.  (By Lemma 2.5 the injection does not matter; the value
for `#ι > κ` is a junk `0` and is never used.) -/
noncomputable def sumOf {ι : Type u} (x : ι → H) : H :=
  if h : Nonempty (ι ↪ Idx κ) then sum (extend h.some x 0) else 0

/-- `x + y`, the sum of a two-element family. -/
noncomputable instance instAdd : Add H :=
  ⟨fun x y => sumOf fun b : ULift.{u} Bool => if b.down then x else y⟩

/-- `a • x` for `a ∈ ℕ∞ = {0, 1, 2, …, ℵ₀}`: the sum of `a` copies of `x`.  So `∞ • x` is the
paper's `ℵ₀x`, where `∞` is `⊤ : ℕ∞`. -/
noncomputable instance instSMul : SMul ℕ∞ H :=
  ⟨fun a x => sumOf fun _ : ULift.{u} {n : ℕ // (n : ℕ∞) < a} => x⟩

/-- `∞ = ⊤ : ℕ∞`, standing for `ℵ₀` in `∞ • x`. -/
scoped notation "∞" => (⊤ : ℕ∞)

/-- A homomorphism of `κ`-monoids: it preserves `0` and `Σ`. -/
def IsHom {K : Type w} [KMonoid κ K] (f : H → K) : Prop :=
  f 0 = 0 ∧ ∀ x : Idx κ → H, f (sum x) = sum (f ∘ x)

/-- `H = ⟨S⟩_κ`: every element of `H` is a `κ`-sum of elements of `S ∪ {0}`. -/
def Generates (S : Set H) : Prop :=
  ∀ h : H, ∃ x : Idx κ → H, (∀ i, x i ∈ S ∨ x i = 0) ∧ sum x = h

/-- `add(x) = {y : y + z = n x for some z ∈ H, n ∈ ℕ₀}`. -/
def addOf (x : H) : Set H := {y | ∃ (z : H) (n : ℕ), y + z = (n : ℕ∞) • x}

/-- `X ⊆ H` is a `λ⁻`-submonoid: it contains `0` and the sums of its families of fewer than `λ`
elements. -/
def IsLSubmonoid (lam : Cardinal.{u}) (X : Set H) : Prop :=
  0 ∈ X ∧ ∀ (ι : Type u) (x : ι → H), #ι < lam → (∀ i, x i ∈ X) → sumOf x ∈ X

end KMonoid

namespace LMonoid

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X]

open Classical in
/-- `∑ i : ι, x i` for `#ι < λ`, as `KMonoid.sumOf`. -/
noncomputable def sumOf {ι : Type u} (x : ι → X) : X :=
  if h : Nonempty (ι ↪ Idx lam) then sum (extend h.some x 0) else 0

/-- `a + b`, the sum of a two-element family. -/
noncomputable instance instAdd : Add X :=
  ⟨fun a b => sumOf fun c : ULift.{u} Bool => if c.down then a else b⟩

/-- A `λ⁻`-homomorphism into a `κ`-monoid (used only with `λ ≤ κ⁺`): it preserves `0` and sums of
fewer than `λ` elements. -/
def IsHom {κ : Cardinal.{u}} {K : Type w} [KMonoid κ K] (f : X → K) : Prop :=
  f 0 = 0 ∧ ∀ (ι : Type u) (x : ι → X), #ι < lam → f (sumOf x) = KMonoid.sumOf (f ∘ x)

end LMonoid

/-! ## §3: braidings and universal `κ`-extensions -/

open KMonoid

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-- `Σ_{i ∈ S} x i`. -/
noncomputable def sumOn {ι : Type u} (S : Set ι) (x : ι → H) : H := sumOf fun i : S => x i

/-- An indexed partition `(I μ)_{μ ∈ ι}` of `ι` into pieces of size `< λ` (some may be empty). -/
def IsSmallPartition {ι : Type u} (lam : Cardinal.{u}) (I : ι → Set ι) : Prop :=
  Pairwise (Disjoint on I) ∧ (⋃ μ, I μ) = Set.univ ∧ ∀ μ, #(I μ) < lam

/-! Braidings are indexed by `κ` with a limit well-order, arbitrary but fixed: a type `ι` of
cardinality `κ` (the hypothesis `#ι = κ` of the theorems), well-ordered, in which every element
has a successor `Order.succ μ`.  The theorems hold for every such order. -/

variable {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] [NoMaxOrder ι] [SuccOrder ι]

/-- **Definition 3.1(1).**  Families `x`, `y : ι → H` (in use, with values in `X`) are
`λ⁻`-braided in `X ⊆ H`: there are indexed partitions `I`, `J` of `ι` into pieces of size `< λ`
and families `u`, `v : ι → X`, with `v μ = 0` at every limit `μ` (`Order.IsSuccPrelimit μ`: not a
successor; the least element counts as a limit), such that for all `μ`
  `Σ_{i ∈ I μ} x i = v μ + u μ`   and   `Σ_{j ∈ J μ} y j = v (μ + 1) + u μ`. -/
def IsBraided (lam : Cardinal.{u}) (X : Set H) (x y : ι → H) : Prop :=
  ∃ (I J : ι → Set ι) (u v : ι → H),
    IsSmallPartition lam I ∧ IsSmallPartition lam J ∧ (∀ μ, u μ ∈ X ∧ v μ ∈ X) ∧
    (∀ μ, Order.IsSuccPrelimit μ → v μ = 0) ∧
    ∀ μ, sumOn (I μ) x = v μ + u μ ∧ sumOn (J μ) y = v (Order.succ μ) + u μ

variable (ι) in
/-- **Definition 3.1(2).**  `H` is `λ⁻`-braided over its `λ⁻`-submonoid `X`: `H = ⟨X⟩_κ`, and any
two families `ι → X` with the same sum are `λ⁻`-braided.  *Braided* means `ℵ₀⁻`-braided. -/
def IsBraidedOver (lam : Cardinal.{u}) (X : Set H) : Prop :=
  IsLSubmonoid lam X ∧ Generates X ∧
    ∀ x y : ι → H, (∀ i, x i ∈ X) → (∀ i, y i ∈ X) → sumOf x = sumOf y → IsBraided lam X x y

/-- **Definition 3.11**, for a `λ⁻`-submonoid `X ⊆ H` with its inclusion: `H` is a universal
`κ`-extension of `X` if every `λ⁻`-homomorphism `φ : X → K` into a `κ`-monoid `K` extends to a
unique `κ`-homomorphism `H → K`.  (`φ` is given as a map on `H` whose values off `X` are ignored.)
`K` ranges over `Type t`. -/
def IsUniversalOver (lam : Cardinal.{u}) (X : Set H) : Prop :=
  IsLSubmonoid lam X ∧
    ∀ (K : Type t) [KMonoid κ K] (φ : H → K), φ 0 = 0 →
      (∀ (T : Type u) (x : T → H), #T < lam → (∀ i, x i ∈ X) → φ (sumOf x) = sumOf (φ ∘ x)) →
      ∃! ψ : H → K, IsHom ψ ∧ ∀ h ∈ X, ψ h = φ h

/-- **Theorem 3.12.**  Let `λ ≤ κ⁺` and let `X` be a reduced `λ⁻`-monoid.  There is a `κ`-monoid
`Ĥ ⊇ X` (via the injective `λ⁻`-homomorphism `f`) which is `λ⁻`-braided over `X`, and which is
the universal `κ`-extension of `X`. -/
theorem theorem_3_12 (hι : #ι = κ) {lam : Cardinal.{u}} (hlk : lam ≤ Order.succ κ) (X : Type v)
    [LMonoid lam X] (hred : ∀ a b : X, a + b = 0 → a = 0 ∧ b = 0) :
    ∃ (Hh : Type (max u v)) (_ : KMonoid κ Hh) (f : X → Hh), Injective f ∧ LMonoid.IsHom f ∧
      IsBraidedOver ι lam (range f) ∧ IsUniversalOver.{u, max u v, t} lam (range f) :=
  sorry

/-! ## §4: monoids of modules -/

section Modules

variable (R : Type u) [Ring R]

/-- **Definition 2.4(1)**, as a property of `P`.  `P : H → ModuleCat R` identifies the `κ`-monoid
`H` with `V^κ(C)` for the class `C` of modules isomorphic to some `P h`: distinct elements give
non-isomorphic modules, `P 0 = 0`, and `P (Σ x) ≅ ⨁ P (x i)`. -/
structure IsVMonoidOf {H : Type u} [KMonoid κ H] (P : H → ModuleCat.{u} R) : Prop where
  zero : Subsingleton (P 0)
  inj : ∀ a b, Nonempty (P a ≃ₗ[R] P b) → a = b
  sum_iso : ∀ x : Idx κ → H, Nonempty (P (sum x) ≃ₗ[R] ⨁ i, P (x i))

/-- **Definition 2.4(2)**, as a property of `P`: it identifies `H` with `V^κ(R)`, the projective
modules generated by at most `κ` elements. -/
structure IsVProjOf {H : Type u} [KMonoid κ H] (P : H → ModuleCat.{u} R) : Prop
    extends IsVMonoidOf R P where
  projective : ∀ h, Module.Projective R (P h)
  gen : ∀ h, ∃ s : Set (P h), #s ≤ κ ∧ Submodule.span R s = ⊤
  surj : ∀ M : ModuleCat.{u} R, Module.Projective R M →
    (∃ s : Set M, #s ≤ κ ∧ Submodule.span R s = ⊤) → ∃ h, Nonempty (M ≃ₗ[R] P h)

/-- `H ≅ V^κ(R)`. -/
def IsoV (H : Type u) [KMonoid κ H] : Prop := ∃ P : H → ModuleCat.{u} R, IsVProjOf R P

/-- **Definition 4.1.**  `M` is `λ⁻`-small: the image of any map `M → ⨁_{i ∈ I} N i` lies in
`⨁_{i ∈ I'} N i` for some `I' ⊆ I` of size `< λ`. -/
def IsLambdaSmall (lam : Cardinal.{u}) (M : ModuleCat.{u} R) : Prop :=
  ∀ {ι : Type u} (N : ι → ModuleCat.{u} R) (f : M →ₗ[R] ⨁ i, N i),
    ∃ s : Set ι, #s < lam ∧ ∀ m, ∀ i ∉ s, f m i = 0

/-- Every projective module is a direct sum of finitely generated modules. -/
def ProjectivesAreSumsOfFG : Prop :=
  ∀ M : ModuleCat.{u} R, Module.Projective R M →
    ∃ (ι : Type u) (N : ι → ModuleCat.{u} R), (∀ i, Module.Finite R (N i)) ∧
      Nonempty (M ≃ₗ[R] ⨁ i, N i)

/-- *Hereditary*: every left ideal and every right ideal (a left ideal of `Rᵐᵒᵖ`) is projective. -/
def IsHereditary : Prop :=
  (∀ I : Ideal R, Module.Projective R I) ∧ ∀ I : Ideal Rᵐᵒᵖ, Module.Projective Rᵐᵒᵖ I

/-- **Theorem 4.3.**  Let `H ≅ V^κ(C)` for a class `C` closed under direct summands, let `λ ≤ κ⁺`
be regular, and let `X ⊆ H` be the classes of a subclass `C_{λ⁻}` of `λ⁻`-small modules closed
under direct sums of fewer than `λ` modules and under direct summands (for the latter,
`a + b ∈ X → a ∈ X`, as `P (a + b) ≅ P a ⊕ P b`).  Then `⟨X⟩_κ` is `λ⁻`-braided over `X`:
families in `X` with the same sum are `λ⁻`-braided.  In particular, if `H = ⟨X⟩_κ` then `H` is
`λ⁻`-braided over `X`. -/
theorem theorem_4_3 {H : Type u} [KMonoid κ H] (hι : #ι = κ) (P : H → ModuleCat.{u} R)
    (hP : IsVMonoidOf R P)
    (hsummand : ∀ h (N N' : Submodule R (P h)), IsCompl N N' → ∃ h', Nonempty (P h' ≃ₗ[R] N))
    {lam : Cardinal.{u}} (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ) (X : Set H)
    (hsmall : ∀ h ∈ X, IsLambdaSmall R lam (P h)) (hX : IsLSubmonoid lam X)
    (hXsummand : ∀ a b : H, a + b ∈ X → a ∈ X) :
    (∀ x y : ι → H, (∀ i, x i ∈ X) → (∀ i, y i ∈ X) → sumOf x = sumOf y → IsBraided lam X x y) ∧
      (Generates X → IsBraidedOver ι lam X) :=
  sorry

/-- **Corollary 4.5(1).**  For regular `λ` with `ℵ₁ ≤ λ ≤ κ⁺`, `V^κ(R)` is `λ⁻`-braided over,
and is the universal `κ`-extension of, `V^{λ⁻}(R)`: the projective modules generated by fewer
than `λ` elements. -/
theorem corollary_4_5_one {H : Type u} [KMonoid κ H] (hι : #ι = κ) (P : H → ModuleCat.{u} R)
    (hP : IsVProjOf R P) {lam : Cardinal.{u}} (hlam : lam.IsRegular) (h₁ : ℵ₁ ≤ lam)
    (hlk : lam ≤ Order.succ κ) :
    IsBraidedOver ι lam {h | ∃ s : Set (P h), #s < lam ∧ Submodule.span R s = ⊤} ∧
      IsUniversalOver.{u, u, t} lam {h | ∃ s : Set (P h), #s < lam ∧ Submodule.span R s = ⊤} :=
  sorry

/-- **Corollary 4.5(2).**  `V^κ(R)` is `ℵ₁⁻`-braided over, and is the universal `κ`-extension
of, the `ℵ₀`-monoid `V^{ℵ₀}(R)` of countably generated projective modules. -/
theorem corollary_4_5_two {H : Type u} [KMonoid κ H] (hι : #ι = κ) (P : H → ModuleCat.{u} R)
    (hP : IsVProjOf R P) :
    IsBraidedOver ι ℵ₁ {h | ∃ s : Set (P h), #s ≤ ℵ₀ ∧ Submodule.span R s = ⊤} ∧
      IsUniversalOver.{u, u, t} ℵ₁ {h | ∃ s : Set (P h), #s ≤ ℵ₀ ∧ Submodule.span R s = ⊤} :=
  sorry

/-- **Corollary 4.5(3).**  If every projective module is a direct sum of finitely generated
modules, then `V^κ(R)` is braided over, and is the universal `κ`-extension of, the monoid `V(R)`
of finitely generated projective modules. -/
theorem corollary_4_5_three {H : Type u} [KMonoid κ H] (hι : #ι = κ) (P : H → ModuleCat.{u} R)
    (hP : IsVProjOf R P) (hfg : ProjectivesAreSumsOfFG R) :
    IsBraidedOver ι ℵ₀ {h | Module.Finite R (P h)} ∧
      IsUniversalOver.{u, u, t} ℵ₀ {h | Module.Finite R (P h)} :=
  sorry

end Modules

/-! ## §5: two-generated `ℵ₀`-monoids

Throughout, `H` is a non-cyclic `ℵ₀`-monoid generated by `x₁`, `x₂`.  Every element of `H` has a
*form* `α x₁ + β x₂` with `α, β ∈ ℕ∞ = {0, 1, …, ℵ₀}`; the form is *infinite* if `α` or `β` is. -/

section TwoGen

variable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]

/-- Conditions (i) and (ii) of Theorem 5.3, for the ordered pair `(a, b) = (x_i, x_j)`. -/
def Conditions53 (a b : H) : Prop :=
  (∀ n : ℕ, (n : ℕ∞) • a + ∞ • b = ∞ • a + ∞ • b → ∞ • b = ∞ • a + ∞ • b ∧ a ∈ addOf b) ∧
    (a ∉ addOf b → ∀ m n : ℕ, (m : ℕ∞) • a + ∞ • b = (n : ℕ∞) • a + ∞ • b →
      ∃ k k' : ℕ, (m : ℕ∞) • a + (k : ℕ∞) • b = (n : ℕ∞) • a + (k' : ℕ∞) • b)

/-- Condition (iii) of Theorem 5.3: no element has both a finite and an infinite form. -/
def NoMixedForms (x₁ x₂ : H) : Prop :=
  ∀ α β γ δ : ℕ∞, α • x₁ + β • x₂ = γ • x₁ + δ • x₂ → α ≠ ⊤ → β ≠ ⊤ → γ ≠ ⊤ ∧ δ ≠ ⊤

/-- **Theorem 5.3.**  `H ≅ V^{ℵ₀}(R)` for a ring `R` whose projective modules are direct sums
of finitely generated modules if and only if (i)–(iii) hold for `{i, j} = {1, 2}`.  In fact these
conditions give `H ≅ V^{ℵ₀}(R)` for a hereditary `k`-algebra `R`, for any field `k`. -/
theorem theorem_5_3 (x₁ x₂ : H) (hgen : Generates {x₁, x₂}) (hnc : ∀ x : H, ¬ Generates {x}) :
    ((∃ (R : Type u) (_ : Ring R), ProjectivesAreSumsOfFG R ∧ IsoV R H) ↔
        Conditions53 x₁ x₂ ∧ Conditions53 x₂ x₁ ∧ NoMixedForms x₁ x₂) ∧
      ∀ (k : Type u) [Field k], Conditions53 x₁ x₂ ∧ Conditions53 x₂ x₁ ∧ NoMixedForms x₁ x₂ →
        ∃ (R : Type u) (_ : Ring R) (_ : Algebra k R), IsHereditary R ∧ IsoV R H :=
  sorry

end TwoGen

end KappaChallenge
