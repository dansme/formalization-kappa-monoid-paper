/-
**Theorem 2.3 and Corollary 2.6** of Bergman, *Modules over coproducts of rings* (1974), in the
setting of its §9 (`R₀ = k^ι`), and their consequences for `V`.

* `StdPres.span_eq_top`, `StdPres.exists_equivStd`, `StdPres.j_injective`: a standard
  presentation identifies `M` with the explicit standard module (**Proposition 2.1(1)**).
* `exists_reach_of_equiv` — **Theorem 2.3** for isomorphisms: if `M ≅ M'` with standard
  presentations with finitely generated components, finitely many transfers and transvections
  turn the presentation of `M` into one whose components are those of `M'`.  Paper proof:
  Proposition 6.2 makes the images in `M'` well-positioned, and Proposition 8.4 identifies them
  with the components of `M'`.
* `exists_pres_range`: the image of a map out of a finitely generated standard module is
  standard, with finitely generated components (Propositions 6.2 and 8.2).
* `exists_pres_of_projective` — **Corollary 2.6**: a finitely generated projective module has a
  standard presentation with finitely generated projective components.  Bergman derives this
  from Corollary 2.4 (`hd_R M = sup hd_{R_μ} M_μ`); here, with `P ⊕ Q ≅ C^n`, both summands are
  standard with finitely generated components, and Theorem 2.3 applied to `C^n` shows that the
  components of `P ⊕ Q` are finitely generated projective, being those of the free module.
* `exists_pair_of_cls`, `rel_of_eq`: Corollaries 2.6 and 2.8 on `V`.
-/
import KappaMonoid.Bergman.Core.Prop62
import KappaMonoid.Bergman.Core.Prop8
import KappaMonoid.Bergman.Core.VBridge

universe u

set_option linter.unusedSectionVars false

namespace Bergman

open Matrix

namespace Core

open Module

section main

variable {k : Type u} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  {σ : ∀ l, (ι → k) →ₐ[k] R l} [Fact (∀ l, Function.Injective (σ l))]
  {C : Type u} [Ring C] [Algebra k C] {σC : (ι → k) →ₐ[k] C} {inc : ∀ l, R l →ₐ[k] C}
  [Fact (IsCoprod k σ C σC inc)]
  {N : Option Λ → Type u} [∀ μ, AddCommGroup (N μ)] [∀ μ, Module (Rμ k ι R μ) (N μ)]
  [∀ μ, Module k (N μ)] [∀ μ, IsScalarTower k (Rμ k ι R μ) (N μ)]
  {M : Type u} [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]
  {M' : Type u} [AddCommGroup M'] [Module C M'] [Module k M'] [IsScalarTower k C M']

/-! ## A standard presentation is the standard module -/

/-- The images of the components generate. -/
theorem StdPres.span_eq_top (p : StdPres σ σC inc M) :
    Submodule.span C (⋃ μ, Set.range (p.j μ)) = ⊤ := by
  set S := Submodule.span C (⋃ μ, Set.range (p.j μ))
  have hπ : ∀ μ a, S.mkQ (p.j μ a) = 0 := fun μ a =>
    (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span (Set.mem_iUnion.2 ⟨μ, a, rfl⟩))
  obtain ⟨_, _, huniq⟩ := p.lift (M ⧸ S) (fun μ => (S.mkQ.restrictScalars k).comp (p.j μ))
    (fun μ r a => by simp [p.j_smul])
  have h1 : S.mkQ = 0 :=
    (huniq S.mkQ fun μ a => rfl).trans (huniq 0 fun μ a => (hπ μ a).symm).symm
  exact eq_top_iff.2 fun m _ => (Submodule.Quotient.mk_eq_zero S).1 (LinearMap.congr_fun h1 m)

/-- A standard presentation identifies `M` with the explicit standard module. -/
theorem StdPres.exists_equivStd (p : StdPres σ σC inc M) (B : HomBases σ p.A) :
    ∃ Ψ : M ≃ₗ[C] Std σC inc B, ∀ μ a, Ψ (p.j μ a) = Std.incl σC inc B μ a := by
  obtain ⟨F, hF, -⟩ := p.lift (Std σC inc B) (Std.incl σC inc B) (Std.incl_smul σC inc B)
  obtain ⟨G, hG, -⟩ := Std.exists_unique_lift σC inc B M p.j p.j_smul
  obtain ⟨_, _, hu⟩ := p.lift M p.j p.j_smul
  obtain ⟨_, _, hu'⟩ := Std.exists_unique_lift σC inc B (Std σC inc B) (Std.incl σC inc B)
    (Std.incl_smul σC inc B)
  have h1 : G ∘ₗ F = LinearMap.id :=
    (hu _ fun μ a => by simp [hF, hG]).trans (hu _ fun μ a => rfl).symm
  have h2 : F ∘ₗ G = LinearMap.id :=
    (hu' _ fun μ a => by simp [hF, hG]).trans (hu' _ fun μ a => rfl).symm
  exact ⟨LinearEquiv.ofLinearMap F G h2 h1, hF⟩

/-- **Proposition 2.1(1)**: the components embed. -/
theorem StdPres.j_injective (p : StdPres σ σC inc M) (μ : Option Λ) :
    Function.Injective (p.j μ) := by
  let B := (nonempty_homBases σ p.A).some
  obtain ⟨Ψ, hΨ⟩ := p.exists_equivStd B
  intro a b h
  apply Std.incl_injective σC inc B μ
  rw [← hΨ, ← hΨ, h]

/-! ## The images of the components as a family of subspaces -/

variable {B : HomBases σ N}

/-- The images `g (A μ)` of the components, as a `SubFam`. -/
noncomputable def imgFam (g : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) : SubFam σC inc B where
  L μ := LinearMap.range ((g.restrictScalars k).comp (p.j μ))
  smul_mem μ r y := by
    rintro ⟨a, rfl⟩
    exact ⟨r • a, by simp [p.j_smul]⟩

theorem imgFam_coe (g : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) :
    (fun μ => ((imgFam g p).L μ : Set (Std σC inc B))) = img g p := by
  funext μ
  rw [imgFam, LinearMap.coe_range]
  rfl

theorem imgFam_wp {g : M →ₗ[C] Std σC inc B} {p : StdPres σ σC inc M} (h : WP (img g p)) :
    WP fun μ => ((imgFam g p).L μ : Set (Std σC inc B)) := by
  rwa [imgFam_coe]

theorem imgFam_span (g : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) :
    (imgFam g p).span = LinearMap.range g := by
  rw [SubFam.span, LinearMap.range_eq_map, ← p.span_eq_top, Submodule.map_span, Set.image_iUnion]
  congr 1
  refine Set.iUnion_congr fun μ => ?_
  rw [imgFam, LinearMap.coe_range, ← Set.range_comp]
  rfl

theorem imgFam_fg (g : M →ₗ[C] Std σC inc B) (p : StdPres σ σC inc M) (hp : p.FG)
    (μ : Option Λ) : Module.Finite (Rμ k ι R μ) ((imgFam g p).L μ) := by
  have := hp μ
  let s : p.A μ →ₗ[Rμ k ι R μ] (imgFam g p).L μ :=
    { toFun := fun a => ⟨g (p.j μ a), a, rfl⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun r a => Subtype.ext (by
        rw [RingHom.id_apply, SubFam.coe_smul]
        simp [p.j_smul]) }
  exact Module.Finite.of_surjective s fun ⟨_, a, rfl⟩ => ⟨a, rfl⟩

/-! ## Theorem 2.3 -/

/-- **Theorem 2.3**, for isomorphisms: if `M ≅ M'`, with standard presentations with finitely
generated components, then transfers and transvections turn the presentation of `M` into one
whose components are those of `M'`. -/
theorem exists_reach_of_equiv (p : StdPres σ σC inc M) (q : StdPres σ σC inc M') (hp : p.FG)
    (e : M ≃ₗ[C] M') : ∃ p', p.Reach p' ∧ p'.IsoExcept q ∅ := by
  set Bq := (nonempty_homBases σ q.A).some
  obtain ⟨Ψ, hΨ⟩ := q.exists_equivStd Bq
  let g : M →ₗ[C] Std σC inc Bq := Ψ.toLinearMap ∘ₗ e.toLinearMap
  obtain ⟨p', hreach, -, hW⟩ := exists_reach_wp g p hp
  have hF := imgFam_wp hW
  have htop : (imgFam g p').span = ⊤ := by
    rw [imgFam_span]
    exact LinearMap.range_eq_top.2 (Ψ.surjective.comp e.surjective)
  refine ⟨p', hreach, fun μ _ => ⟨?_⟩⟩
  have heq := (imgFam g p').eq_incl_of_wp hF htop μ
  have hinj : Function.Injective ((g.restrictScalars k).comp (p'.j μ)) :=
    (Ψ.injective.comp e.injective).comp (p'.j_injective μ)
  have hincl := Std.incl_injective σC inc Bq μ
  let T : p'.A μ ≃ₗ[k] q.A μ := (LinearEquiv.ofInjective _ hinj).trans
    ((LinearEquiv.ofEq _ _ heq).trans (LinearEquiv.ofInjective _ hincl).symm)
  have hT : ∀ a, Std.incl σC inc Bq μ (T a) = g (p'.j μ a) := fun a => by
    have h1 := LinearEquiv.ofInjective_apply (Std.incl σC inc Bq μ) (h := hincl)
      ((LinearEquiv.ofInjective _ hincl).symm
        (LinearEquiv.ofEq _ _ heq (LinearEquiv.ofInjective _ hinj a)))
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  exact
    { toFun := T
      invFun := T.symm
      map_add' := T.map_add
      left_inv := T.left_inv
      right_inv := T.right_inv
      map_smul' := fun r a => hincl (by
        rw [RingHom.id_apply, hT, Std.incl_smul, hT]
        simp [g, p'.j_smul]) }

/-! ## Images, products, Corollary 2.6 -/

/-- The image of a map out of a finitely generated standard module is standard, with finitely
generated components (Propositions 6.2 and 8.2). -/
theorem exists_pres_range (p : StdPres σ σC inc M) (hp : p.FG) (q : StdPres σ σC inc M')
    (f : M →ₗ[C] M') : ∃ r : StdPres σ σC inc (LinearMap.range f), r.FG := by
  obtain ⟨Ψ, -⟩ := q.exists_equivStd (nonempty_homBases σ q.A).some
  let g := Ψ.toLinearMap ∘ₗ f
  obtain ⟨p', -, hp', hW⟩ := exists_reach_wp g p hp
  let θ : (imgFam g p').span ≃ₗ[C] LinearMap.range f :=
    (LinearEquiv.ofEq _ _ ((imgFam_span g p').trans (LinearMap.range_comp f _))).trans
      (Ψ.submoduleMap (LinearMap.range f)).symm
  exact ⟨((imgFam g p').pres (imgFam_wp hW)).transport θ, imgFam_fg g p' hp'⟩

/-- The product of two standard presentations. -/
noncomputable def StdPres.prod (p : StdPres σ σC inc M) (q : StdPres σ σC inc M') :
    StdPres σ σC inc (M × M') where
  coprod := p.coprod
  A μ := p.A μ × q.A μ
  j μ := (p.j μ).prodMap (q.j μ)
  j_smul μ r a := Prod.ext (p.j_smul μ r a.1) (q.j_smul μ r a.2)
  lift P _ _ _ _ g hg := by
    obtain ⟨F₁, hF₁, hu₁⟩ := p.lift P (fun μ => g μ ∘ₗ LinearMap.inl k _ _)
      (fun μ r a => by simpa using hg μ r (a, 0))
    obtain ⟨F₂, hF₂, hu₂⟩ := q.lift P (fun μ => g μ ∘ₗ LinearMap.inr k _ _)
      (fun μ r b => by simpa using hg μ r (0, b))
    refine ⟨F₁.coprod F₂, fun μ ab => ?_, fun F hF => ?_⟩
    · have := hF₁ μ ab.1
      have := hF₂ μ ab.2
      simp_all [← map_add]
    · apply LinearMap.prod_ext
      · rw [LinearMap.coprod_inl]
        exact hu₁ (F ∘ₗ LinearMap.inl C M M') fun μ a => by simpa using hF μ (a, 0)
      · rw [LinearMap.coprod_inr]
        exact hu₂ (F ∘ₗ LinearMap.inr C M M') fun μ b => by simpa using hF μ (0, b)

theorem range_one_sub {E : Type u} [AddCommGroup E] [Module C E] {f : E →ₗ[C] E}
    (hf : IsIdempotentElem f) : LinearMap.range (1 - f) = LinearMap.ker f := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    have := LinearMap.congr_fun hf.eq w
    simp only [Module.End.mul_apply] at this
    simp [this]
  · intro hv
    exact ⟨v, by simp [LinearMap.mem_ker.1 hv]⟩

/-- **Corollary 2.6**: a finitely generated projective module over the coproduct has a standard
presentation with finitely generated projective components. -/
theorem exists_pres_of_projective (P : Type u) [AddCommGroup P] [Module C P] [Module k P]
    [IsScalarTower k C P] [Module.Projective C P] [Module.Finite C P] :
    ∃ p : StdPres σ σC inc P, p.FGP := by
  have hC : IsCoprod k σ C σC inc := Fact.out
  obtain ⟨n, F, hF, ⟨ψ⟩⟩ := exists_rowModEquiv (R := C) P
  -- the free module `C^n`, as the realisation of `(1_n, 0, …, 0)`
  let d : Option Λ → ℕ := fun μ => μ.elim n fun _ => 0
  let e : ∀ μ, Matrix (Fin (d μ)) (Fin (d μ)) (Rμ k ι R μ) := fun _ => 1
  have he : ∀ μ, e μ * e μ = e μ := fun _ => mul_one _
  have hE : realE σC inc e = 1 := by
    simp only [realE, e]
    rw [show (fun μ => (1 : Matrix (Fin (d μ)) (Fin (d μ)) (Rμ k ι R μ)).map (incμ σC inc μ)) =
      1 from funext fun μ => Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.blockDiagonal'_one
  have htop : rowMod (realE σC inc e) = ⊤ := by
    rw [hE]; exact LinearMap.range_eq_top.2 fun v => ⟨v, by simp⟩
  have hcard : Fintype.card (Σ μ, Fin (d μ)) = n := by
    simp [d, Fintype.card_sigma, Fintype.sum_option]
  let ζ : rowMod (realE σC inc e) ≃ₗ[C] (Fin n → C) :=
    ((LinearEquiv.ofTop _ htop)).trans
      (LinearEquiv.funCongrLeft C C (Fintype.equivFinOfCardEq hcard).symm)
  let p₀ := (realPres σC inc e hC he).transport ζ
  have hp₀ : p₀.FGP := realPres_FGP e hC he
  have hp₀' : p₀.FG := fun μ => (hp₀ μ).1
  -- `C^n = P ⊕ Q`
  let π : (Fin n → C) →ₗ[C] (Fin n → C) := vecMulLinear F
  have hπ : IsIdempotentElem π := LinearMap.ext fun v => by
    simp [π, Matrix.vecMul_vecMul, hF]
  obtain ⟨rP, hrP⟩ := exists_pres_range p₀ hp₀' p₀ π
  obtain ⟨rQ, hrQ⟩ := exists_pres_range p₀ hp₀' p₀ (1 - π)
  let rQ' := rQ.transport (LinearEquiv.ofEq _ _ (range_one_sub hπ))
  let pq := (rP.prod rQ').transport (Submodule.prodEquivOfIsCompl _ _ (LinearMap.IsIdempotentElem.isCompl hπ))
  obtain ⟨p', hreach, hiso⟩ := exists_reach_of_equiv p₀ pq hp₀' (LinearEquiv.refl _ _)
  have hp' := (StdPres.Reach.rel (fun _ _ => True) (fun _ _ => trivial) hreach hp₀).1
  have hpq : pq.FGP := hp'.of_iso hiso
  refine ⟨rP.transport ψ.symm, fun μ => ?_⟩
  have h1 : Module.Finite (Rμ k ι R μ) (rP.A μ × rQ'.A μ) := (hpq μ).1
  have h2 : Module.Projective (Rμ k ι R μ) (rP.A μ × rQ'.A μ) := (hpq μ).2
  exact fgp_of_equiv_prod (LinearEquiv.refl (Rμ k ι R μ) (rP.A μ × rQ'.A μ))

end main

/-! ## Bergman's theorem on `V` of a coproduct -/

section final

variable {k : Type u} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  {σ : ∀ l, (ι → k) →ₐ[k] R l}
  {C : Type u} [Ring C] [Algebra k C] {σC : (ι → k) →ₐ[k] C} {inc : ∀ l, R l →ₐ[k] C}

variable [Fact (∀ l, Function.Injective (σ l))] [Fact (IsCoprod k σ C σC inc)]

/-- The components of a pair, indexed by `Option Λ`. -/
def pairComp (x : V (ι → k) × ∀ l, V (R l)) : ∀ μ : Option Λ, V (Rμ k ι R μ)
  | none => x.1
  | some l => x.2 l

omit [Fact (∀ l, Function.Injective (σ l))] [Fact (IsCoprod k σ C σC inc)] in
theorem sum_pairComp (x : V (ι → k) × ∀ l, V (R l)) :
    ∑ μ, V.map (incμ σC inc μ).toRingHom (pairComp x μ) =
      V.map σC.toRingHom x.1 + ∑ l, V.map (inc l).toRingHom (x.2 l) :=
  Fintype.sum_option _

omit [Fact (∀ l, Function.Injective (σ l))] [Fact (IsCoprod k σ C σC inc)] in
theorem realPres_vpair (hC : IsCoprod k σ C σC inc) {m : Option Λ → Type}
    [∀ μ, Fintype (m μ)] [∀ μ, DecidableEq (m μ)] (e : ∀ μ, Matrix (m μ) (m μ) (Rμ k ι R μ))
    (he : ∀ μ, e μ * e μ = e μ) (x : V (ι → k) × ∀ l, V (R l))
    (hx : ∀ μ, cls (e μ) (he μ) = pairComp x μ) : (realPres σC inc e hC he).vpair = x :=
  Prod.ext ((vcls_eq (he none) (LinearEquiv.refl _ (rowMod (e none)))).trans (hx none))
    (funext fun l => (vcls_eq (he (some l)) (LinearEquiv.refl _ (rowMod (e (some l))))).trans
      (hx (some l)))

variable (σ) in
include σ in
/-- **Corollary 2.6** on `V`: every class in `V(C)` is induced from the factors. -/
theorem exists_pair_of_cls (y : V C) : ∃ x : V (ι → k) × ∀ l, V (R l),
    V.map σC.toRingHom x.1 + ∑ l, V.map (inc l).toRingHom (x.2 l) = y := by
  obtain ⟨n, F, hF, rfl⟩ := cls_surjective y
  have := rowMod.projective hF
  obtain ⟨p, hp⟩ := exists_pres_of_projective (σ := σ) (σC := σC) (inc := inc) (rowMod F)
  choose m e he hφ using fun μ => have := (hp μ).1; have := (hp μ).2
    exists_rowModEquiv (R := Rμ k ι R μ) (p.A μ)
  refine ⟨(cls (e none) (he none), fun l => cls (e (some l)) (he (some l))), ?_⟩
  rw [← sum_pairComp]
  have hc : ∀ μ, pairComp (R := R) (cls (e none) (he none), fun l => cls (e (some l)) (he (some l)))
      μ = cls (e μ) (he μ) := by rintro (_ | l) <;> rfl
  simp only [hc]
  rw [← cls_realE (σC := σC) (inc := inc) (m := fun μ => Fin (m μ)) e he]
  apply (rowModEquiv_iff_cls_eq _ _).1
  exact (realPres σC inc e Fact.out he).nonempty_equiv p (fun μ _ => ⟨(hφ μ).some.symm⟩)

variable (σ) in
/-- **Corollary 2.8** on `V`: pairs inducing the same class are related by basic transfers. -/
theorem rel_of_eq (r : (V (ι → k) × ∀ l, V (R l)) → (V (ι → k) × ∀ l, V (R l)) → Prop)
    (hr : ∀ (a : V (ι → k)) (l : Λ), r (a, 0) (0, Pi.single l (V.map (σ l).toRingHom a)))
    (x y : V (ι → k) × ∀ l, V (R l))
    (h : V.map σC.toRingHom x.1 + ∑ l, V.map (inc l).toRingHom (x.2 l) =
      V.map σC.toRingHom y.1 + ∑ l, V.map (inc l).toRingHom (y.2 l)) :
    addConGen r x y := by
  have hC : IsCoprod k σ C σC inc := Fact.out
  choose m e he hx using fun μ => cls_surjective (pairComp x μ)
  choose m' f hf hy using fun μ => cls_surjective (pairComp y μ)
  rw [← sum_pairComp, ← sum_pairComp] at h
  simp only [← hx, ← hy] at h
  rw [← cls_realE (σC := σC) (inc := inc) (m := fun μ => Fin (m μ)) e he,
    ← cls_realE (σC := σC) (inc := inc) (m := fun μ => Fin (m' μ)) f hf] at h
  obtain ⟨Φ⟩ := (rowModEquiv_iff_cls_eq _ _).2 h
  obtain ⟨p', hreach, hiso⟩ := exists_reach_of_equiv (realPres σC inc e hC he)
    (realPres σC inc f hC hf) (fun μ => (realPres_FGP e hC he μ).1) Φ
  obtain ⟨hp', hrel⟩ := StdPres.Reach.rel r hr hreach (realPres_FGP e hC he)
  rwa [realPres_vpair hC e he x hx, StdPres.vpair_eq hp' hiso,
    realPres_vpair hC f hf y hy] at hrel

end final

end Core

end Bergman
