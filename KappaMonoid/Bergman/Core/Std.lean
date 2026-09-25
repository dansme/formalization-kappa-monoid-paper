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
import KappaMonoid.Bergman.Corner

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

theorem nonempty_homBases : Nonempty (HomBases σ N) :=
  ⟨⟨fun μ j => Basis.ofVectorSpaceIndex k (eSub σ N μ j),
    fun μ j => Basis.ofVectorSpace k (eSub σ N μ j)⟩⟩

theorem eμ_smul_eSub {μ : Option Λ} {j : ι} (i : ι) {x : N μ} (hx : x ∈ eSub σ N μ j) :
    eμ σ μ i • x = if i = j then x else 0 := by
  have hx' : eμ σ μ j • x = x := hx
  rw [← hx', smul_smul, eμ_mul_eμ]
  split_ifs with h
  · subst h; rfl
  · simp

/-- `N_μ = ⊕_j e_j N_μ`, as `k`-spaces. -/
noncomputable def homEquiv (μ : Option Λ) : N μ ≃ₗ[k] ∀ j, eSub σ N μ j where
  toFun x j := ⟨eμ σ μ j • x, by
    show eμ σ μ j • eμ σ μ j • x = eμ σ μ j • x
    rw [smul_smul, eμ_mul_eμ, if_pos rfl]⟩
  invFun p := ∑ j, (p j : N μ)
  map_add' x y := by ext j; simp
  map_smul' c x := by ext j; simp [smul_comm (eμ σ μ j) c x]
  left_inv x := by simp [← Finset.sum_smul, sum_eμ]
  right_inv p := by
    ext j
    simp only [Finset.smul_sum]
    rw [Finset.sum_eq_single j]
    · rw [eμ_smul_eSub σ N j (p j).2, if_pos rfl]
    · intro j' _ hj'
      rw [eμ_smul_eSub σ N j (p j').2, if_neg (Ne.symm hj')]
    · simp

variable {σ N} (B : HomBases σ N)

/-- The homogeneous basis of `N_μ`, `N_μ = ⊕_j e_j N_μ`. -/
noncomputable def HomBases.basis (μ : Option Λ) : Basis (Σ j, B.S μ j) k (N μ) :=
  (Pi.basis fun j => B.b μ j).map (homEquiv σ N μ).symm

theorem HomBases.basis_apply (μ : Option Λ) (j : ι) (s : B.S μ j) :
    B.basis μ ⟨j, s⟩ = (B.b μ j s : N μ) := by
  classical
  rw [HomBases.basis, Basis.map_apply, Pi.basis_apply]
  change ∑ j', ((Pi.single j (B.b μ j s) : ∀ j, eSub σ N μ j) j' : N μ) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'; simp [Pi.single_apply, hj']
  · simp

theorem HomBases.basis_mem (μ : Option Λ) (j : ι) (s : B.S μ j) :
    B.basis μ ⟨j, s⟩ ∈ eSub σ N μ j := by
  rw [B.basis_apply]; exact (B.b μ j s).2

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

/-- The monomials, from the three kinds relative to `μ`: a base element of `N_μ`, a monomial
not on side `μ`, or a letter of `R_μ` times one. -/
def monoJoin : ∀ μ : Option Λ,
    ((Σ j, B.S μ j) ⊕ Σ u : NotSide B μ, Option (Σ i, Tl σ μ i u.1.left)) → Mono σ B.S
  | μ, .inl ⟨j, s⟩ => Mono.ofBase ⟨μ, j, s⟩
  | _, .inr ⟨u, none⟩ => u.1
  | none, .inr ⟨_, some ⟨i, t⟩⟩ => (isEmpty_Tl_none σ i _).elim t
  | some l, .inr ⟨u, some ⟨i, t⟩⟩ => Mono.cons ⟨l, i, u.1.left, t⟩ u.1 rfl (fun h => u.2 h.symm)

theorem monoJoin_side_inl (μ : Option Λ) (j : ι) (s : B.S μ j) :
    (monoJoin B μ (.inl ⟨j, s⟩)).side = μ := rfl

theorem monoJoin_side_some (l : Λ) (u : NotSide B (some l)) (i : ι)
    (t : Tl σ (some l) i u.1.left) : (monoJoin B (some l) (.inr ⟨u, some ⟨i, t⟩⟩)).side = some l :=
  rfl

theorem monoJoin_injective (μ : Option Λ) : Function.Injective (monoJoin B μ) := by
  intro x y h
  have hs := congrArg Mono.side h
  have hw := congrArg Mono.word h
  rcases x with ⟨j, s⟩ | ⟨u, _ | ⟨i, t⟩⟩ <;> rcases y with ⟨j', s'⟩ | ⟨u', _ | ⟨i', t'⟩⟩
  · have hb := congrArg Mono.base h
    simp only [monoJoin, Mono.ofBase, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hb
    obtain ⟨rfl, hs⟩ := hb
    rw [eq_of_heq hs]
  · exact absurd hs.symm u'.2
  · cases μ with
    | none => exact (isEmpty_Tl_none σ i' _).elim t'
    | some l => exact absurd hw (by simp [monoJoin, Mono.ofBase, Mono.cons])
  · exact absurd hs u.2
  · have : u = u' := Subtype.ext h
    subst this; rfl
  · cases μ with
    | none => exact (isEmpty_Tl_none σ i' _).elim t'
    | some l => exact absurd hs u.2
  · cases μ with
    | none => exact (isEmpty_Tl_none σ i _).elim t
    | some l => exact absurd hw (by simp [monoJoin, Mono.ofBase, Mono.cons])
  · cases μ with
    | none => exact (isEmpty_Tl_none σ i _).elim t
    | some l => exact absurd hs.symm u'.2
  · cases μ with
    | none => exact (isEmpty_Tl_none σ i _).elim t
    | some l =>
      obtain ⟨hl, hu⟩ := Mono.cons_injective (h₁ := rfl) (h₂ := fun h => u.2 h.symm)
        (h₁' := rfl) (h₂' := fun h => u'.2 h.symm) h
      have : u = u' := Subtype.ext hu
      subst this
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at hl
      obtain ⟨rfl, ht⟩ := hl
      have ht' := eq_of_heq ht
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at ht'
      rw [ht']

theorem monoJoin_surjective (μ : Option Λ) : Function.Surjective (monoJoin B μ) := by
  rintro ⟨⟨ν, j, s⟩, word, hc⟩
  cases word with
  | nil =>
    by_cases h : ν = μ
    · subst h; exact ⟨.inl ⟨j, s⟩, rfl⟩
    · exact ⟨.inr ⟨⟨⟨⟨ν, j, s⟩, [], hc⟩, h⟩, none⟩, rfl⟩
  | cons t ts =>
    by_cases h : some t.side = μ
    · subst h
      obtain ⟨l, i, j', t'⟩ := t
      obtain ⟨hc1, hc2, hc3⟩ := hc
      change j' = _ at hc2
      subst hc2
      exact ⟨.inr ⟨⟨⟨⟨ν, j, s⟩, ts, hc1⟩, fun h' => hc3 h'.symm⟩, some ⟨i, t'⟩⟩, rfl⟩
    · exact ⟨.inr ⟨⟨⟨⟨ν, j, s⟩, t :: ts, hc⟩, h⟩, none⟩, rfl⟩

/-- The three kinds of monomial relative to `μ`. -/
noncomputable def monoSplit (μ : Option Λ) :
    Mono σ B.S ≃ (Σ j, B.S μ j) ⊕ Σ u : NotSide B μ, Option (Σ i, Tl σ μ i u.1.left) :=
  (Equiv.ofBijective (monoJoin B μ) ⟨monoJoin_injective B μ, monoJoin_surjective B μ⟩).symm

theorem monoSplit_symm_apply (μ : Option Λ) (x) : (monoSplit B μ).symm x = monoJoin B μ x := rfl

theorem monoSplit_monoJoin (μ : Option Λ) (x) : monoSplit B μ (monoJoin B μ x) = x :=
  (monoSplit B μ).apply_symm_apply x

/-- The basis of `N_μ × FreePart μ` matching the monomials. -/
noncomputable def targetBasis (μ : Option Λ) :
    Basis ((Σ j, B.S μ j) ⊕ Σ u : NotSide B μ, Option (Σ i, Tl σ μ i u.1.left)) k
      (N μ × FreePart B μ) :=
  (B.basis μ).prod (DFinsupp.basis fun u : NotSide B μ => leftIdealBasis σ μ u.1.left)

theorem targetBasis_inl (μ : Option Λ) (j : ι) (s : B.S μ j) :
    targetBasis B μ (.inl ⟨j, s⟩) = (B.basis μ ⟨j, s⟩, 0) := by
  simp [targetBasis, Basis.prod_apply]

theorem targetBasis_inr (μ : Option Λ) (u : NotSide B μ) (o : Option (Σ i, Tl σ μ i u.1.left)) :
    targetBasis B μ (.inr ⟨u, o⟩) = (0, DFinsupp.single u (leftIdealBasis σ μ u.1.left o)) := by
  simp [targetBasis, Basis.prod_apply, DFinsupp.basis]

theorem dfinsupp_basis_apply {ι' : Type*} {M : ι' → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] [DecidableEq ι'] {η : ι' → Type*} (b : ∀ i, Basis (η i) k (M i))
    (x : Σ i, η i) : DFinsupp.basis b x = DFinsupp.single x.1 (b x.1 x.2) := by
  rw [DFinsupp.basis, Basis.coe_ofRepr]
  simp [sigmaFinsuppLequivDFinsupp]

/-- **`Std = N_μ ⊕ (free R_μ-module)`**, as `k`-spaces. -/
noncomputable def Std.Φ (μ : Option Λ) : Std σC inc B ≃ₗ[k] N μ × FreePart B μ :=
  (Std.monoBasis σC inc B).equiv (targetBasis B μ) (monoSplit B μ)

theorem Std.monoBasis_apply (w : Mono σ B.S) :
    Std.monoBasis σC inc B w = Std.mono σC inc B w := by
  change (Finsupp.basisSingleOne : Basis (Mono σ B.S) k (Mono σ B.S →₀ k)) w = Finsupp.single w 1
  simp

theorem Std.Φ_mono (μ : Option Λ) (w : Mono σ B.S) :
    Std.Φ σC inc B μ (Std.mono σC inc B w) = targetBasis B μ (monoSplit B μ w) := by
  rw [← Std.monoBasis_apply, Std.Φ, Basis.equiv_apply]

theorem Std.Φ_mono_join (μ : Option Λ) (x) :
    Std.Φ σC inc B μ (Std.mono σC inc B (monoJoin B μ x)) = targetBasis B μ x := by
  rw [Std.Φ_mono, monoSplit_monoJoin]

theorem Std.Φ_symm_target (μ : Option Λ) (x) :
    (Std.Φ σC inc B μ).symm (targetBasis B μ x) = Std.mono σC inc B (monoJoin B μ x) := by
  rw [LinearEquiv.symm_apply_eq, Std.Φ_mono_join]

/-- Scalar multiplication by `r ∈ R_μ`, as a `k`-linear map. -/
def smulLin {M : Type*} [AddCommGroup M] [Module k M] {A : Type*} [Ring A] [Algebra k A]
    [Module A M] [IsScalarTower k A M] (r : A) : M →ₗ[k] M where
  toFun y := r • y
  map_add' := smul_add r
  map_smul' c y := smul_comm r c y

@[simp] theorem smulLin_apply {M : Type*} [AddCommGroup M] [Module k M] {A : Type*} [Ring A]
    [Algebra k A] [Module A M] [IsScalarTower k A M] (r : A) (y : M) :
    smulLin (k := k) r y = r • y := rfl

/-- The action of `R_μ` on `Std`, transported along `Φ μ`. -/
noncomputable def Std.act (μ : Option Λ) : Rμ k ι R μ →ₐ[k] Module.End k (Std σC inc B) where
  toFun r := (Std.Φ σC inc B μ).symm.toLinearMap ∘ₗ smulLin r ∘ₗ (Std.Φ σC inc B μ).toLinearMap
  map_one' := by ext x; simp
  map_mul' r s := by ext x; simp [mul_smul]
  map_zero' := by
    ext x
    simp only [LinearMap.comp_apply, smulLin_apply, LinearEquiv.coe_coe]
    have h0 : (0 : Rμ k ι R μ) • Std.Φ σC inc B μ x = 0 :=
      Prod.ext (zero_smul _ _) (DFinsupp.ext fun u => Subtype.ext (by simp))
    rw [h0, map_zero]; rfl
  map_add' r s := by ext x; simp [add_smul]
  commutes' c := by ext x; simp [algebraMap_smul]

theorem Std.act_apply (μ : Option Λ) (r : Rμ k ι R μ) (x : Std σC inc B) :
    Std.act σC inc B μ r x = (Std.Φ σC inc B μ).symm (r • Std.Φ σC inc B μ x) := rfl

theorem eμ_smul_targetBasis (μ : Option Λ) (i : ι) (x) :
    eμ σ μ i • targetBasis B μ x =
      if (monoJoin B μ x).left = i then targetBasis B μ x else 0 := by
  rcases x with ⟨j, s⟩ | ⟨u, _ | ⟨i', t⟩⟩
  · rw [targetBasis_inl, Prod.smul_mk, smul_zero, eμ_smul_eSub σ N i (B.basis_mem μ j s)]
    change _ = if j = i then _ else _
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [targetBasis_inr, Prod.smul_mk, smul_zero, ← DFinsupp.single_smul]
    change _ = if u.1.left = i then _ else _
    have : eμ σ μ i • leftIdealBasis σ μ u.1.left none =
        if u.1.left = i then leftIdealBasis σ μ u.1.left none else 0 := by
      apply Subtype.ext
      rw [Submodule.coe_smul, leftIdealBasis_none, smul_eq_mul, eμ_mul_eμ]
      by_cases h : u.1.left = i
      · subst h; simp [leftIdealBasis_none]
      · simp [h, Ne.symm h]
    rw [this]
    split_ifs <;> simp
  · cases μ with
    | none => exact (isEmpty_Tl_none σ i' _).elim t
    | some l =>
      rw [targetBasis_inr, Prod.smul_mk, smul_zero, ← DFinsupp.single_smul]
      change _ = if i' = i then _ else _
      have : eμ σ (some l) i • leftIdealBasis σ (some l) u.1.left (some ⟨i', t⟩) =
          if i' = i then leftIdealBasis σ (some l) u.1.left (some ⟨i', t⟩) else 0 := by
        apply Subtype.ext
        rw [Submodule.coe_smul, leftIdealBasis_some, smul_eq_mul, ← eμ_mul_tval σ t,
          ← mul_assoc, eμ_mul_eμ]
        by_cases h : i' = i
        · subst h; simp [leftIdealBasis_some, eμ_mul_tval]
        · simp [h, Ne.symm h]
      rw [this]
      split_ifs <;> simp

theorem Std.act_eμ_mono (μ : Option Λ) (i : ι) (w : Mono σ B.S) :
    Std.act σC inc B μ (eμ σ μ i) (Std.mono σC inc B w) =
      if w.left = i then Std.mono σC inc B w else 0 := by
  obtain ⟨x, rfl⟩ := monoJoin_surjective B μ w
  rw [Std.act_apply, Std.Φ_mono_join, eμ_smul_targetBasis]
  split_ifs
  · exact Std.Φ_symm_target σC inc B μ x
  · simp

theorem Std.act_compat (l : Λ) :
    (Std.act σC inc B (some l)).comp (σ l) = Std.act σC inc B none := by
  refine Bergman.algHom_pi_ext fun i => (Std.monoBasis σC inc B).ext fun w => ?_
  rw [Std.monoBasis_apply]
  exact (Std.act_eμ_mono σC inc B (some l) i w).trans (Std.act_eμ_mono σC inc B none i w).symm

theorem Std.exists_toEnd : ∃ g : C →ₐ[k] Module.End k (Std σC inc B),
    g.comp σC = Std.act σC inc B none ∧ ∀ l, g.comp (inc l) = Std.act σC inc B (some l) :=
  (Fact.out : IsCoprod k σ C σC inc).lift _ _ _ (Std.act_compat σC inc B)

/-- The action of `C`, from the universal property of the coproduct. -/
noncomputable def Std.toEnd : C →ₐ[k] Module.End k (Std σC inc B) :=
  (Std.exists_toEnd σC inc B).choose

theorem Std.toEnd_comp_σC : (Std.toEnd σC inc B).comp σC = Std.act σC inc B none :=
  (Std.exists_toEnd σC inc B).choose_spec.1

theorem Std.toEnd_comp_inc (l : Λ) :
    (Std.toEnd σC inc B).comp (inc l) = Std.act σC inc B (some l) :=
  (Std.exists_toEnd σC inc B).choose_spec.2 l

noncomputable instance : Module C (Std σC inc B) :=
  Module.compHom (Std σC inc B) (Std.toEnd σC inc B).toRingHom

theorem Std.smul_def (c : C) (x : Std σC inc B) : c • x = Std.toEnd σC inc B c x := rfl

instance : IsScalarTower k C (Std σC inc B) :=
  ⟨fun a c x => by rw [Std.smul_def, Std.smul_def, map_smul]; rfl⟩

theorem Std.incμ_smul (μ : Option Λ) (r : Rμ k ι R μ) (x : Std σC inc B) :
    incμ σC inc μ r • x = Std.act σC inc B μ r x := by
  cases μ with
  | none => rw [Std.smul_def, ← Std.toEnd_comp_σC]; rfl
  | some l => rw [Std.smul_def, ← Std.toEnd_comp_inc]; rfl

theorem Std.Φ_incμ_smul (μ : Option Λ) (r : Rμ k ι R μ) (x : Std σC inc B) :
    Std.Φ σC inc B μ (incμ σC inc μ r • x) = r • Std.Φ σC inc B μ x := by
  rw [Std.incμ_smul, Std.act_apply, LinearEquiv.apply_symm_apply]

/-! ## The components and the universal property -/

/-- The inclusion `N_μ → Std`, `s ↦ s` on basis elements. -/
noncomputable def Std.incl (μ : Option Λ) : N μ →ₗ[k] Std σC inc B :=
  (Std.Φ σC inc B μ).symm.toLinearMap ∘ₗ LinearMap.inl k (N μ) (FreePart B μ)

theorem Std.Φ_incl (μ : Option Λ) (n : N μ) :
    Std.Φ σC inc B μ (Std.incl σC inc B μ n) = (n, 0) := by
  simp [Std.incl]

theorem Std.incl_basis (μ : Option Λ) (j : ι) (s : B.S μ j) :
    Std.incl σC inc B μ (B.basis μ ⟨j, s⟩) = Std.mono σC inc B
      (Mono.ofBase ⟨μ, j, s⟩) := by
  rw [Std.incl, LinearMap.comp_apply, LinearMap.inl_apply, ← targetBasis_inl]
  exact Std.Φ_symm_target σC inc B μ _

theorem Std.incl_smul (μ : Option Λ) (r : Rμ k ι R μ) (n : N μ) :
    Std.incl σC inc B μ (r • n) = incμ σC inc μ r • Std.incl σC inc B μ n := by
  apply (Std.Φ σC inc B μ).injective
  rw [Std.Φ_incμ_smul, Std.Φ_incl, Std.Φ_incl, Prod.smul_mk, smul_zero]

/-- **Proposition 2.1(1)**: `N_μ` embeds in `Std`. -/
theorem Std.incl_injective (μ : Option Λ) : Function.Injective (Std.incl σC inc B μ) :=
  fun a b h => by simpa [Std.Φ_incl] using congrArg (Std.Φ σC inc B μ) h

/-- Left multiplication by a letter on a monomial it may be applied to. -/
theorem Std.mono_cons (t : Letter σ) (w : Mono σ B.S) (h₁ h₂) :
    Std.mono σC inc B (Mono.cons t w h₁ h₂) =
      inc t.side t.val • Std.mono σC inc B w := by
  obtain ⟨l, i, j, t'⟩ := t
  change j = w.left at h₁
  subst h₁
  let u : NotSide B (some l) := ⟨w, fun h => h₂ h.symm⟩
  apply (Std.Φ σC inc B (some l)).injective
  have h1 : Mono.cons ⟨l, i, w.left, t'⟩ w rfl h₂ = monoJoin B (some l) (.inr ⟨u, some ⟨i, t'⟩⟩) :=
    rfl
  have h2 : Std.Φ σC inc B (some l) (Std.mono σC inc B w) = targetBasis B (some l) (.inr ⟨u, none⟩) :=
    Std.Φ_mono_join σC inc B (some l) (.inr ⟨u, none⟩)
  rw [h1, Std.Φ_mono_join, targetBasis_inr]
  change _ = Std.Φ σC inc B (some l) (incμ σC inc (some l) (tval σ t') • Std.mono σC inc B w)
  rw [Std.Φ_incμ_smul, h2, targetBasis_inr, Prod.smul_mk, smul_zero,
    ← DFinsupp.single_smul]
  congr 2
  apply Subtype.ext
  rw [Submodule.coe_smul, leftIdealBasis_some, leftIdealBasis_none, smul_eq_mul]
  exact (tval_mul_eμ σ t').symm

/-- `Std` is generated by its components. -/
theorem Std.mono_mem_span (w : Mono σ B.S) :
    Std.mono σC inc B w ∈ Submodule.span C (⋃ μ, Set.range (Std.incl σC inc B μ)) := by
  suffices h : ∀ n, ∀ w : Mono σ B.S, w.deg = n →
      Std.mono σC inc B w ∈ Submodule.span C (⋃ μ, Set.range (Std.incl σC inc B μ)) from
    h _ w rfl
  intro n
  induction n with
  | zero =>
    intro w hw
    obtain ⟨⟨μ, j, s⟩, word, hc⟩ := w
    have : word = [] := List.length_eq_zero_iff.1 hw
    subst this
    refine Submodule.subset_span (Set.mem_iUnion.2 ⟨μ, B.basis μ ⟨j, s⟩, ?_⟩)
    exact Std.incl_basis σC inc B μ j s
  | succ n ih =>
    intro w hw
    obtain ⟨t, ts, hts⟩ : ∃ t ts, w.word = t :: ts := by
      match h : w.word, hw with
      | t :: ts, _ => exact ⟨t, ts, rfl⟩
      | [], hw' => simp [Mono.deg, h] at hw'
    obtain ⟨h₁, h₂, hw'⟩ := Mono.eq_cons_of_word_eq_cons hts
    rw [hw', Std.mono_cons]
    refine Submodule.smul_mem _ _ (ih _ ?_)
    have := congrArg Mono.deg hw'
    rw [Mono.deg_cons] at this
    omega

theorem Std.span_incl :
    Submodule.span C (⋃ μ, Set.range (Std.incl σC inc B μ)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hk : x ∈ Submodule.span k (Set.range (Std.mono σC inc B)) := by
    rw [show Set.range (Std.mono σC inc B) = Set.range (Std.monoBasis σC inc B) from by
      ext; simp [Std.monoBasis_apply], (Std.monoBasis σC inc B).span_eq]
    trivial
  refine (Submodule.span_le.2 ?_ : Submodule.span k _ ≤
    (Submodule.span C (⋃ μ, Set.range (Std.incl σC inc B μ))).restrictScalars k) hk
  rintro _ ⟨w, rfl⟩
  exact Std.mono_mem_span σC inc B w

/-- A property of elements of the coproduct, closed under the algebra operations and true on
the images of the factors, holds everywhere. -/
theorem IsCoprod.mem_of_subalgebra (hC : IsCoprod k σ C σC inc) (A : Subalgebra k C)
    (h₀ : ∀ r, σC r ∈ A) (h : ∀ l r, inc l r ∈ A) (c : C) : c ∈ A := by
  obtain ⟨g, hg₀, hg⟩ := hC.lift A (σC.codRestrict A h₀) (fun l => (inc l).codRestrict A (h l))
    (fun l => AlgHom.ext fun r => Subtype.ext (by
      show inc l (σ l r) = σC r
      rw [← AlgHom.comp_apply, hC.comm l]))
  have hid : A.val.comp g = AlgHom.id k C := hC.ext C _ _
    (by rw [AlgHom.comp_assoc, hg₀]; rfl)
    (fun l => by rw [AlgHom.comp_assoc, hg l]; rfl)
  have : ((g c : A) : C) = c := AlgHom.congr_fun hid c
  rw [← this]
  exact (g c).2

variable (P : Type u) [AddCommGroup P] [Module C P] [Module k P] [IsScalarTower k C P]
  (g : ∀ μ, N μ →ₗ[k] P)

/-- The candidate lift on monomials: `tₙ ⋯ t₁ s ↦ tₙ ⋯ t₁ g(s)`. -/
noncomputable def liftMono (w : Mono σ B.S) : P :=
  w.word.foldr (fun t acc => inc t.side t.val • acc)
    (g w.base.1 (B.basis w.base.1 ⟨w.base.2.1, w.base.2.2⟩))

theorem liftMono_ofBase (μ : Option Λ) (j : ι) (s : B.S μ j) :
    liftMono inc B P g (Mono.ofBase ⟨μ, j, s⟩) = g μ (B.basis μ ⟨j, s⟩) := rfl

theorem liftMono_cons (t : Letter σ) (w : Mono σ B.S) (h₁ h₂) :
    liftMono inc B P g (Mono.cons t w h₁ h₂) = inc t.side t.val • liftMono inc B P g w :=
  rfl

theorem incμ_eμ (μ : Option Λ) (i : ι) : incμ σC inc μ (eμ σ μ i) = σC (ee i) := by
  cases μ with
  | none => rfl
  | some l =>
    change inc l (σ l (ee i)) = σC (ee i)
    rw [← AlgHom.comp_apply, (Fact.out : IsCoprod k σ C σC inc).comm l]

variable {P g} in
theorem liftMono_homog
    (hg : ∀ μ (r : Rμ k ι R μ) (n : N μ), g μ (r • n) = incμ σC inc μ r • g μ n)
    (w : Mono σ B.S) : σC (ee w.left) • liftMono inc B P g w = liftMono inc B P g w := by
  obtain ⟨⟨ν, j, s⟩, word, hc⟩ := w
  cases word with
  | nil =>
    change σC (ee j) • g ν (B.basis ν ⟨j, s⟩) = g ν (B.basis ν ⟨j, s⟩)
    rw [← incμ_eμ (σ := σ) σC inc ν j, ← hg, B.basis_mem ν j s]
  | cons t ts =>
    change σC (ee t.left) • (inc t.side t.val • liftMono inc B P g ⟨⟨ν, j, s⟩, ts, hc.1⟩) =
      inc t.side t.val • liftMono inc B P g ⟨⟨ν, j, s⟩, ts, hc.1⟩
    have e : σC (ee t.left) * inc t.side t.val = inc t.side t.val := by
      rw [← incμ_eμ (σ := σ) σC inc (some t.side) t.left]
      change inc t.side _ * inc t.side _ = _
      exact (map_mul (inc t.side) (eμ σ (some t.side) t.left) t.val).symm.trans
        (congrArg (inc t.side) (eμ_mul_tval σ t.2.2.2))
    rw [smul_smul, e]

variable {P g} in
theorem liftMono_join_inr
    (hg : ∀ μ (r : Rμ k ι R μ) (n : N μ), g μ (r • n) = incμ σC inc μ r • g μ n)
    (μ : Option Λ) (u : NotSide B μ) (o : Option (Σ i, Tl σ μ i u.1.left)) :
    liftMono inc B P g (monoJoin B μ (.inr ⟨u, o⟩)) =
      incμ σC inc μ (leftIdealBasis σ μ u.1.left o) • liftMono inc B P g u.1 := by
  rcases o with _ | ⟨i, t⟩
  · rw [leftIdealBasis_none, incμ_eμ σC inc]
    exact (liftMono_homog σC inc B hg u.1).symm
  · cases μ with
    | none => exact (isEmpty_Tl_none σ i _).elim t
    | some l =>
      rw [leftIdealBasis_some]
      rfl

/-- The candidate lift, `k`-linearly. -/
noncomputable def liftLin : Std σC inc B →ₗ[k] P :=
  Finsupp.linearCombination k (liftMono inc B P g)

theorem liftLin_mono (w : Mono σ B.S) :
    liftLin σC inc B P g (Std.mono σC inc B w) = liftMono inc B P g w :=
  (Finsupp.linearCombination_single k (v := liftMono inc B P g) (c := 1) (a := w)).trans
    (one_smul k _)

theorem liftLin_incl (μ : Option Λ) (n : N μ) :
    liftLin σC inc B P g (Std.incl σC inc B μ n) = g μ n := by
  have : (liftLin σC inc B P g).comp (Std.incl σC inc B μ) = g μ :=
    (B.basis μ).ext fun ⟨j, s⟩ => by
      rw [LinearMap.comp_apply, Std.incl_basis, liftLin_mono, liftMono_ofBase]
  exact LinearMap.congr_fun this n

variable {P g} in
theorem liftLin_smul_mono
    (hg : ∀ μ (r : Rμ k ι R μ) (n : N μ), g μ (r • n) = incμ σC inc μ r • g μ n)
    (μ : Option Λ) (r : Rμ k ι R μ) (w : Mono σ B.S) :
    liftLin σC inc B P g (incμ σC inc μ r • Std.mono σC inc B w) =
      incμ σC inc μ r • liftLin σC inc B P g (Std.mono σC inc B w) := by
  -- the case of a monomial not on side `μ`
  have key : ∀ (r : Rμ k ι R μ) (u : NotSide B μ),
      liftLin σC inc B P g (incμ σC inc μ r • Std.mono σC inc B u.1) =
        incμ σC inc μ r • liftMono inc B P g u.1 := by
    intro r u
    set b := leftIdealBasis σ μ u.1.left
    set v : Submodule.span (Rμ k ι R μ) {eμ σ μ u.1.left} :=
      ⟨r * eμ σ μ u.1.left, Submodule.mem_span_singleton.2 ⟨r, rfl⟩⟩
    have hv : r • b none = v := by
      apply Subtype.ext
      rw [Submodule.coe_smul, leftIdealBasis_none, smul_eq_mul]
    have hsum : v = ∑ o ∈ (b.repr v).support, b.repr v o • b o := by
      conv_lhs => rw [← b.linearCombination_repr v]
      rfl
    have hx : incμ σC inc μ r • Std.mono σC inc B u.1 =
        ∑ o ∈ (b.repr v).support, b.repr v o • Std.mono σC inc B (monoJoin B μ (.inr ⟨u, o⟩)) := by
      apply (Std.Φ σC inc B μ).injective
      rw [map_sum, Std.Φ_incμ_smul]
      rw [show Std.Φ σC inc B μ (Std.mono σC inc B u.1) = targetBasis B μ (.inr ⟨u, none⟩) from
        Std.Φ_mono_join σC inc B μ (.inr ⟨u, none⟩)]
      simp only [map_smul, Std.Φ_mono_join, targetBasis_inr, Prod.smul_mk, smul_zero]
      rw [← DFinsupp.single_smul, hv]
      refine Prod.ext (by rw [Prod.fst_sum]; simp) ?_
      rw [Prod.snd_sum]
      simp only [← DFinsupp.single_smul]
      rw [congrArg (DFinsupp.single u) hsum]
      exact map_sum (DFinsupp.singleAddHom (fun u : NotSide B μ =>
        ↥(Submodule.span (Rμ k ι R μ) {eμ σ μ u.1.left})) u) _ _
    have hr : (v : Rμ k ι R μ) = ∑ o ∈ (b.repr v).support, b.repr v o • (b o : Rμ k ι R μ) := by
      conv_lhs => rw [hsum]
      simp
    rw [hx, map_sum]
    simp only [map_smul, liftLin_mono, liftMono_join_inr σC inc B hg, smul_assoc]
    calc ∑ o ∈ (b.repr v).support, b.repr v o • incμ σC inc μ (b o) • liftMono inc B P g u.1
        = incμ σC inc μ (v : Rμ k ι R μ) • liftMono inc B P g u.1 := by
          rw [hr, map_sum, Finset.sum_smul]
          simp [smul_assoc]
      _ = incμ σC inc μ r • liftMono inc B P g u.1 := by
          change incμ σC inc μ (r * eμ σ μ u.1.left) • _ = _
          rw [map_mul, mul_smul, incμ_eμ σC inc, liftMono_homog σC inc B hg]
  obtain ⟨x, rfl⟩ := monoJoin_surjective B μ w
  rcases x with ⟨j, s⟩ | ⟨u, _ | ⟨i, t⟩⟩
  · change liftLin σC inc B P g (incμ σC inc μ r • Std.mono σC inc B (Mono.ofBase ⟨μ, j, s⟩)) =
      incμ σC inc μ r • liftLin σC inc B P g (Std.mono σC inc B (Mono.ofBase ⟨μ, j, s⟩))
    rw [← Std.incl_basis, ← Std.incl_smul, liftLin_incl, liftLin_incl, hg]
  · exact (key r u).trans (by rw [liftLin_mono]; rfl)
  · cases μ with
    | none => exact (isEmpty_Tl_none σ i _).elim t
    | some l =>
      have hw : Std.mono σC inc B (monoJoin B (some l) (.inr ⟨u, some ⟨i, t⟩⟩)) =
          incμ σC inc (some l) (tval σ t) • Std.mono σC inc B u.1 :=
        Std.mono_cons σC inc B _ _ rfl (fun h => u.2 h.symm)
      rw [hw, smul_smul, ← map_mul, key, key, map_mul, mul_smul]

/-- **The universal property of standard modules.** -/
theorem Std.exists_unique_lift
    (hg : ∀ μ (r : Rμ k ι R μ) (n : N μ), g μ (r • n) = incμ σC inc μ r • g μ n) :
    ∃! f : Std σC inc B →ₗ[C] P, ∀ μ n, f (Std.incl σC inc B μ n) = g μ n := by
  -- `C`-linearity of the candidate
  have hC : ∀ c : C, ∀ x, liftLin σC inc B P g (c • x) = c • liftLin σC inc B P g x := by
    intro c
    let A : Subalgebra k C :=
      { carrier := {c | ∀ x, liftLin σC inc B P g (c • x) = c • liftLin σC inc B P g x}
        mul_mem' := fun ha hb x => by rw [mul_smul, ha, hb, mul_smul]
        add_mem' := fun ha hb x => by rw [add_smul, map_add, ha, hb, add_smul]
        algebraMap_mem' := fun a x => by
          simp only [algebraMap_smul, map_smul] }
    have hμ : ∀ μ r, incμ σC inc μ r ∈ A := fun μ r x => by
      have : (liftLin σC inc B P g).comp (smulLin (incμ σC inc μ r)) =
          (smulLin (incμ σC inc μ r)).comp (liftLin σC inc B P g) :=
        (Std.monoBasis σC inc B).ext fun w => by
          simp only [LinearMap.comp_apply, smulLin_apply, Std.monoBasis_apply]
          exact liftLin_smul_mono σC inc B hg μ r w
      exact LinearMap.congr_fun this x
    exact IsCoprod.mem_of_subalgebra σC inc (Fact.out : IsCoprod k σ C σC inc) A (hμ none) (fun l => hμ (some l)) c
  refine ⟨{ liftLin σC inc B P g with map_smul' := hC }, fun μ n => liftLin_incl σC inc B P g μ n,
    fun f hf => ?_⟩
  apply LinearMap.ext_on (Std.span_incl σC inc B)
  rintro _ hx
  obtain ⟨μ, n, rfl⟩ := Set.mem_iUnion.1 hx
  exact (hf μ n).trans (liftLin_incl σC inc B P g μ n).symm

end Bergman.Core
