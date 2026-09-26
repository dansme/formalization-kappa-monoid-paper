/-
**Quasi-free algebras are hereditary.**

A `k`-algebra `S` is *quasi-free* (Cuntz–Quillen) when every algebra map into a square-zero
quotient `T → T'` lifts to `T`.  Over a field this forces `S` to be left and right hereditary.

The classical route goes through the bimodule of noncommutative differentials
`Ω¹S = ker(μ : S ⊗ S → S)`: quasi-free ⇒ `Ω¹S` is a projective `S ⊗ Sᵐᵒᵖ`-module ⇒ every left
module has projective dimension `≤ 1`.  The formalisation takes a shortcut that avoids tensor
products over noncommutative rings altogether.  For a left ideal `I ≠ S`:

1. quasi-free ⇒ derivations lift along surjective bimodule maps (via the square-zero extensions
   `S ⊕ N → S ⊕ N'`, `QuasiFree.exists_lift_derivation`);
2. pick a `k`-linear section `τ` of `π : S → S ⧸ I` with `τ (π 1) = 1`; then
   `D s = s τ - τ (s •)` is a derivation of `S` into the bimodule `Hom_k(S ⧸ I, I)`;
3. lift `D` along `Hom_k(S ⧸ I, F) → Hom_k(S ⧸ I, I)` for a free cover `p : F → I` to a
   derivation `E`; then `x ↦ E x (π 1)` is an `S`-linear section of `p`, so `I` is a direct
   summand of a free module.

This replaces the universal-derivation computations of Bergman–Dicks (1978): the realising ring
is presented by idempotents and isomorphisms between their images, both of which lift along
square-zero extensions (`Bergman/MainRing.lean`).
-/
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Dual.Lemmas
import KappaMonoid.ForMathlib.Hereditary

universe u

namespace Bergman

open MulOpposite TrivSqZeroExt

variable (k : Type u) [Field k]

/-- **Quasi-free**: algebra maps into square-zero quotients lift. -/
def QuasiFree (S : Type u) [Ring S] [Algebra k S] : Prop :=
  ∀ (T T' : Type u) [Ring T] [Ring T'] [Algebra k T] [Algebra k T'] (π : T →ₐ[k] T'),
    Function.Surjective π → (∀ x y, π x = 0 → π y = 0 → x * y = 0) →
    ∀ φ : S →ₐ[k] T', ∃ ψ : S →ₐ[k] T, π.comp ψ = φ

/-! ### The bimodule `Hom_k(M, F)` -/

/-- `Hom_k(M, F)` for left `S`-modules `M` and `F`, as an `S`-bimodule:
`(s • f • t) m = s • f (t • m)`.  A type synonym, because `M →ₗ[k] F` may already carry a
different `Sᵐᵒᵖ`-action through `F`. -/
@[nolint unusedArguments]
def BiHom (S : Type u) [Ring S] [Algebra k S]
    (M : Type u) [AddCommGroup M] [Module k M] (F : Type u) [AddCommGroup F] [Module k F] :
    Type u :=
  M →ₗ[k] F

section BiHom

variable {k} {S : Type u} [Ring S] [Algebra k S]
variable {M : Type u} [AddCommGroup M] [Module S M] [Module k M] [IsScalarTower k S M]
variable {F : Type u} [AddCommGroup F] [Module S F] [Module k F] [IsScalarTower k S F]

namespace BiHom

instance : AddCommGroup (BiHom k S M F) := inferInstanceAs (AddCommGroup (M →ₗ[k] F))
instance : Module k (BiHom k S M F) := inferInstanceAs (Module k (M →ₗ[k] F))
instance : Module S (BiHom k S M F) := inferInstanceAs (Module S (M →ₗ[k] F))
instance : FunLike (BiHom k S M F) M F := inferInstanceAs (FunLike (M →ₗ[k] F) M F)
instance : LinearMapClass (BiHom k S M F) k M F :=
  inferInstanceAs (LinearMapClass (M →ₗ[k] F) k M F)

/-- View a `k`-linear map as an element of `BiHom`. -/
def mk (f : M →ₗ[k] F) : BiHom k S M F := f

omit [Module S M] [IsScalarTower k S M] [Module S F] [IsScalarTower k S F] in
@[simp] theorem mk_apply (f : M →ₗ[k] F) (m : M) : mk (S := S) f m = f m := rfl

omit [Module S M] [IsScalarTower k S M] [Module S F] [IsScalarTower k S F] in
@[ext] theorem ext {f g : BiHom k S M F} (h : ∀ m, f m = g m) : f = g := LinearMap.ext h

omit [Module S M] [IsScalarTower k S M] [Module S F] [IsScalarTower k S F] in
@[simp] theorem add_apply (f g : BiHom k S M F) (m : M) : (f + g) m = f m + g m := rfl
omit [Module S M] [IsScalarTower k S M] [Module S F] [IsScalarTower k S F] in
@[simp] theorem zero_apply (m : M) : (0 : BiHom k S M F) m = 0 := rfl
omit [Module S M] [IsScalarTower k S M] in
@[simp] theorem smul_apply (s : S) (f : BiHom k S M F) (m : M) : (s • f) m = s • f m := rfl
omit [Module S M] [IsScalarTower k S M] [Module S F] [IsScalarTower k S F] in
@[simp] theorem ksmul_apply (c : k) (f : BiHom k S M F) (m : M) : (c • f) m = c • f m := rfl

instance : SMul Sᵐᵒᵖ (BiHom k S M F) :=
  ⟨fun t f => mk ((f : M →ₗ[k] F) ∘ₗ DistribSMul.toLinearMap k M t.unop)⟩

omit [Module S F] [IsScalarTower k S F] in
@[simp] theorem op_smul_apply (t : Sᵐᵒᵖ) (f : BiHom k S M F) (m : M) :
    (t • f) m = f (t.unop • m) := rfl

instance : Module Sᵐᵒᵖ (BiHom k S M F) where
  one_smul f := by ext m; simp
  mul_smul t t' f := by ext m; simp [mul_smul]
  smul_zero t := by ext m; simp
  smul_add t f g := by ext m; simp
  add_smul t t' f := by ext m; simp [add_smul]
  zero_smul f := by ext m; simp

instance : SMulCommClass S Sᵐᵒᵖ (BiHom k S M F) := ⟨fun s t f => by ext m; simp⟩
instance : IsScalarTower k S (BiHom k S M F) := ⟨fun c s f => by ext m; simp⟩
instance : IsScalarTower k Sᵐᵒᵖ (BiHom k S M F) := ⟨fun c t f => by ext m; simp⟩

variable {G : Type u} [AddCommGroup G] [Module S G] [Module k G] [IsScalarTower k S G]

/-- Postcomposition with an `S`-linear map, a map of bimodules. -/
def postcomp (g : F →ₗ[S] G) : BiHom k S M F →ₗ[k] BiHom k S M G where
  toFun f := mk ((g.restrictScalars k) ∘ₗ (f : M →ₗ[k] F))
  map_add' f f' := by ext m; exact map_add g (f m) (f' m)
  map_smul' c f := by ext m; exact g.map_smul_of_tower c (f m)

omit [Module S M] [IsScalarTower k S M] in
@[simp] theorem postcomp_apply (g : F →ₗ[S] G) (f : BiHom k S M F) (m : M) :
    postcomp g f m = g (f m) := rfl

omit [Module S M] [IsScalarTower k S M] in
theorem postcomp_smul (g : F →ₗ[S] G) (s : S) (f : BiHom k S M F) :
    postcomp g (s • f) = s • postcomp g f := by ext m; simp

theorem postcomp_op_smul (g : F →ₗ[S] G) (t : Sᵐᵒᵖ) (f : BiHom k S M F) :
    postcomp g (t • f) = t • postcomp g f := by ext m; simp

end BiHom

end BiHom

variable {k} {S : Type u} [Ring S] [Algebra k S]

/-- Quasi-freeness is left–right symmetric. -/
theorem QuasiFree.op (h : QuasiFree k S) : QuasiFree k Sᵐᵒᵖ := by
  intro T T' _ _ _ _ π hπ hsq φ
  let φ' : S →ₐ[k] T'ᵐᵒᵖ := AlgHom.unop ((AlgEquiv.opOp k T').toAlgHom.comp φ)
  obtain ⟨ψ, hψ⟩ := h Tᵐᵒᵖ T'ᵐᵒᵖ (AlgHom.op π)
    (fun y => ⟨MulOpposite.op (hπ y.unop).choose, by
      simp [(hπ y.unop).choose_spec]⟩)
    (fun x y hx hy => by
      have hx' : π x.unop = 0 := by simpa using congrArg MulOpposite.unop hx
      have hy' : π y.unop = 0 := by simpa using congrArg MulOpposite.unop hy
      simpa using congrArg MulOpposite.op (hsq _ _ hy' hx')) φ'
  refine ⟨(AlgEquiv.opOp k T).symm.toAlgHom.comp (AlgHom.op ψ), AlgHom.ext fun x => ?_⟩
  have := congrArg MulOpposite.unop (AlgHom.congr_fun hψ x.unop)
  simpa [φ'] using this

/-- **Derivations out of a quasi-free algebra lift** along surjective maps of bimodules.  The
derivations are `k`-linear maps `D` with `D (s * t) = s • D t + D s • t`; the proof lifts
`s ↦ (s, D s)` along the square-zero extension `S ⊕ N → S ⊕ N'`. -/
theorem QuasiFree.exists_lift_derivation (h : QuasiFree k S)
    {N N' : Type u} [AddCommGroup N] [Module S N] [Module Sᵐᵒᵖ N] [SMulCommClass S Sᵐᵒᵖ N]
    [Module k N] [IsScalarTower k S N] [IsScalarTower k Sᵐᵒᵖ N]
    [AddCommGroup N'] [Module S N'] [Module Sᵐᵒᵖ N'] [SMulCommClass S Sᵐᵒᵖ N']
    [Module k N'] [IsScalarTower k S N'] [IsScalarTower k Sᵐᵒᵖ N']
    (q : N →ₗ[k] N') (hq : Function.Surjective q) (hqS : ∀ (s : S) n, q (s • n) = s • q n)
    (hqS' : ∀ (t : Sᵐᵒᵖ) n, q (t • n) = t • q n)
    (D : S →ₗ[k] N') (hD : ∀ s t, D (s * t) = s • D t + MulOpposite.op t • D s) :
    ∃ E : S →ₗ[k] N, (∀ s t, E (s * t) = s • E t + MulOpposite.op t • E s) ∧
      ∀ s, q (E s) = D s := by
  have hD1 : D 1 = 0 := by
    have h1 := hD 1 1
    simp only [mul_one, one_smul, op_one] at h1
    simpa using h1
  let π : TrivSqZeroExt S N →ₐ[k] TrivSqZeroExt S N' :=
    { toFun := fun x => inl x.fst + inr (q x.snd)
      map_one' := by ext <;> simp
      map_mul' := fun x y => by ext <;> simp [hqS, hqS']
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp
      commutes' := fun c => by ext <;> simp [algebraMap_eq_inl'] }
  let φ : S →ₐ[k] TrivSqZeroExt S N' :=
    { toFun := fun s => inl s + inr (D s)
      map_one' := by ext <;> simp [hD1]
      map_mul' := fun s t => by ext <;> simp [hD]
      map_zero' := by ext <;> simp
      map_add' := fun s t => by ext <;> simp
      commutes' := fun c => by
        have : D (algebraMap k S c) = 0 := by
          rw [Algebra.algebraMap_eq_smul_one, map_smul, hD1, smul_zero]
        ext <;> simp [algebraMap_eq_inl', this] }
  have hπs : Function.Surjective π := fun y => by
    obtain ⟨n, hn⟩ := hq y.snd
    exact ⟨inl y.fst + inr n, by ext <;> simp [π, hn]⟩
  have hsq : ∀ x y, π x = 0 → π y = 0 → x * y = 0 := fun x y hx hy => by
    have hx1 : x.fst = 0 := by simpa [π] using congrArg TrivSqZeroExt.fst hx
    have hy1 : y.fst = 0 := by simpa [π] using congrArg TrivSqZeroExt.fst hy
    ext <;> simp [hx1, hy1]
  obtain ⟨ψ, hψ⟩ := h _ _ π hπs hsq φ
  have hψ' : ∀ s, π (ψ s) = φ s := fun s => by rw [← AlgHom.comp_apply, hψ]
  have h1 : ∀ s, (ψ s).fst = s := fun s => by
    simpa [π, φ] using congrArg TrivSqZeroExt.fst (hψ' s)
  refine ⟨{ toFun := fun s => (ψ s).snd
            map_add' := fun s t => by simp
            map_smul' := fun c s => by simp }, fun s t => ?_, fun s => ?_⟩
  · simp [h1]
  · simpa [π, φ] using congrArg TrivSqZeroExt.snd (hψ' s)

/-- A proper left ideal has a `k`-linear section `τ` of `S → S ⧸ I` with `τ (π 1) = 1`. -/
theorem exists_section_mkQ (I : Ideal S) (hI : I ≠ ⊤) :
    ∃ τ : (S ⧸ I) →ₗ[k] S, (∀ m, I.mkQ (τ m) = m) ∧ τ (I.mkQ 1) = 1 := by
  set π := I.mkQ with hπ
  have h1 : π 1 ≠ 0 := fun h0 =>
    hI ((Ideal.eq_top_iff_one I).2 ((Submodule.Quotient.mk_eq_zero I).1 h0))
  obtain ⟨τ₀, hτ₀⟩ := Module.projective_lifting_property (π.restrictScalars k) LinearMap.id
    (Submodule.mkQ_surjective I)
  have hτ₀' : ∀ m, π (τ₀ m) = m := fun m => LinearMap.congr_fun hτ₀ m
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual k (S ⧸ I), g (π 1) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h1 ((Module.forall_dual_apply_eq_zero_iff k _).1 hc)
  refine ⟨τ₀ + ((g (π 1))⁻¹ • g).smulRight (1 - τ₀ (π 1)), fun m => ?_, ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smulRight_apply, map_add,
      LinearMap.map_smul_of_tower, map_sub, hτ₀', sub_self, smul_zero, add_zero]
  · simp [hg]

/-- **Every left ideal of a quasi-free algebra is projective.**  For `I ≠ S`, with `τ` a
`k`-linear section of `π : S → S ⧸ I` normalised by `τ (π 1) = 1`, the inner-type derivation
`D s = s τ - τ (s •) : S → Hom_k(S ⧸ I, I)` lifts along a free cover `p : F → I` to a derivation
`E : S → Hom_k(S ⧸ I, F)`, and `x ↦ E x (π 1)` is an `S`-linear section of `p`. -/
theorem QuasiFree.projective_ideal (h : QuasiFree k S) (I : Ideal S) :
    Module.Projective S I := by
  by_cases hI : I = ⊤
  · subst hI
    exact Module.Projective.of_equiv Submodule.topEquiv.symm
  set π := I.mkQ with hπ
  obtain ⟨τ, hτ, hτ1⟩ := exists_section_mkQ (k := k) I hI
  -- the derivation `D s = s τ - τ (s •)` into `Hom_k(S ⧸ I, I)`
  have hmem : ∀ (s : S) (m : S ⧸ I), s * τ m - τ (s • m) ∈ I := fun s m => by
    rw [← Submodule.Quotient.mk_eq_zero I]
    change π (s • τ m - τ (s • m)) = 0
    rw [map_sub, map_smul, hτ, hτ, sub_self]
  let D0 : S → (S ⧸ I) →ₗ[k] I := fun s =>
    { toFun := fun m => ⟨s * τ m - τ (s • m), hmem s m⟩
      map_add' := fun m m' => by ext; simp [smul_add, mul_add]; abel
      map_smul' := fun c m => by ext; simp [smul_sub, smul_comm s c] }
  let D : S →ₗ[k] BiHom k S (S ⧸ I) I :=
    { toFun := fun s => BiHom.mk (D0 s)
      map_add' := fun s s' => by ext m; simp [D0, add_mul, add_smul]; abel
      map_smul' := fun c s => by ext m; simp [D0, smul_sub, smul_assoc] }
  have hD : ∀ s t, D (s * t) = s • D t + MulOpposite.op t • D s := fun s t => by
    ext m
    simp [D, D0, mul_smul, mul_sub, mul_assoc]
  -- a free cover of `I`, and the induced surjection of bimodules
  let p : (I →₀ S) →ₗ[S] I := Finsupp.linearCombination S id
  have hp : Function.Surjective p := Finsupp.linearCombination_id_surjective S I
  have hq : Function.Surjective (BiHom.postcomp (k := k) (M := S ⧸ I) p) := fun g => by
    obtain ⟨l, hl⟩ := Module.projective_lifting_property (p.restrictScalars k)
      (g : (S ⧸ I) →ₗ[k] I) hp
    exact ⟨BiHom.mk l, BiHom.ext fun m => LinearMap.congr_fun hl m⟩
  obtain ⟨E, hE, hED⟩ := h.exists_lift_derivation (BiHom.postcomp p) hq
    (BiHom.postcomp_smul p) (BiHom.postcomp_op_smul p) D hD
  -- the section of `p`
  have hx : ∀ x : I, (x : S) • π 1 = 0 := fun x => by
    rw [← map_smul, smul_eq_mul, mul_one]
    exact (Submodule.Quotient.mk_eq_zero I).2 x.2
  let σ : I →ₗ[S] (I →₀ S) :=
    { toFun := fun x => E x (π 1)
      map_add' := fun x y => by simp
      map_smul' := fun s x => by simp [hE, hx] }
  refine Module.Projective.of_split σ p (LinearMap.ext fun x => ?_)
  have := congrArg (fun f => f (π 1)) (hED x)
  simp only [BiHom.postcomp_apply] at this
  change p (E x (π 1)) = x
  rw [this]
  ext
  change (x : S) * τ (π 1) - τ ((x : S) • π 1) = x
  rw [hx, map_zero, hτ1, mul_one, sub_zero]

/-- **Quasi-free algebras are left hereditary.** -/
theorem QuasiFree.isLeftHereditary (h : QuasiFree k S) : IsLeftHereditary S :=
  ⟨h.projective_ideal⟩

/-- **Quasi-free algebras are hereditary.** -/
theorem QuasiFree.isHereditary (h : QuasiFree k S) : IsHereditary S :=
  ⟨h.isLeftHereditary, isRightHereditary_iff_isLeftHereditary_op.2 h.op.isLeftHereditary⟩

end Bergman
