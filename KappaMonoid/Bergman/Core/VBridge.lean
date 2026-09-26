/-
**From standard presentations to `V`** (Bergman 1974, Corollaries 2.6 and 2.8, the monoid side).

`vcls R Q ∈ V(R)` is the class of a finitely generated projective module `Q` (via
`exists_rowModEquiv`); it is invariant under isomorphism and additive on products.  A standard
presentation `p` with f.g. projective components has the tuple of component classes
`p.vpair ∈ V(k^ι) × ∏ V(R l)`.

* `realPres`: for idempotent matrices `e μ` over `R_μ`, the row module of the block-diagonal
  matrix `diag(e μ)` over `C` has a standard presentation with components `rowMod (e μ)`
  (`Hom_C(rowMod E, P) ≅ {x ∈ P^m | E x = x}`, and likewise over `R_μ`).
* `StdPres.nonempty_equiv`: presentations with isomorphic components present isomorphic modules.
* `StdPres.Reach.rel`: along transfers and transvections the tuple changes by basic transfers.

With Corollary 2.6 and Theorem 2.3 these give `exists_pair_of_cls` and `rel_of_eq`
(`Core/Main.lean`), hence `IsCoprod.coprodV_surjective` and `IsCoprod.coprodV_eq_iff`
(`Bergman/Coprod.lean`).
-/
import KappaMonoid.Bergman.Core.Pres
import KappaMonoid.Bergman.IdemModule
import Mathlib.RingTheory.Finiteness.Prod

universe u v

namespace Bergman

open Matrix

/-! ## The class of a finitely generated projective module -/

section vcls

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

open Classical in
/-- The class in `V(R)` of a module (meaningful for finitely generated projective modules). -/
noncomputable def vcls : V R :=
  if h : ∃ x : Idem R, Nonempty (Q ≃ₗ[R] rowMod x.e) then cls h.choose.e h.choose.idem else 0

variable {R Q}

theorem vcls_eq {m : Type} [Fintype m] [DecidableEq m] {e : Matrix m m R} (he : e * e = e)
    (φ : Q ≃ₗ[R] rowMod e) : vcls R Q = cls e he := by
  have h : ∃ x : Idem R, Nonempty (Q ≃ₗ[R] rowMod x.e) := by
    let x : Idem R := ⟨Fintype.card m,
      Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin m) e, reindex_idem he _⟩
    obtain ⟨ψ⟩ := (rowModEquiv_iff_cls_eq he x.idem).2 (cls_reindex he _).symm
    exact ⟨x, ⟨φ.trans ψ⟩⟩
  rw [vcls, dif_pos h]
  obtain ⟨ψ⟩ := h.choose_spec
  exact (rowModEquiv_iff_cls_eq _ he).1 ⟨ψ.symm.trans φ⟩

variable {Q Q' : Type u} [AddCommGroup Q] [Module R Q] [AddCommGroup Q'] [Module R Q']

theorem vcls_eq_iff [Module.Finite R Q] [Module.Projective R Q] {m : Type} [Fintype m]
    [DecidableEq m] {e : Matrix m m R} (he : e * e = e) :
    vcls R Q = cls e he ↔ Nonempty (Q ≃ₗ[R] rowMod e) := by
  obtain ⟨n, f, hf, ⟨ψ⟩⟩ := exists_rowModEquiv (R := R) Q
  rw [vcls_eq hf ψ]
  constructor
  · intro h
    obtain ⟨χ⟩ := (rowModEquiv_iff_cls_eq hf he).2 h
    exact ⟨ψ.trans χ⟩
  · rintro ⟨χ⟩
    exact (rowModEquiv_iff_cls_eq hf he).1 ⟨ψ.symm.trans χ⟩

theorem vcls_congr [Module.Finite R Q] [Module.Projective R Q] (φ : Q ≃ₗ[R] Q') :
    vcls R Q = vcls R Q' := by
  obtain ⟨n, f, hf, ⟨ψ⟩⟩ := exists_rowModEquiv (R := R) Q
  rw [vcls_eq hf ψ, vcls_eq hf (φ.symm.trans ψ)]

theorem vcls_prod [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R Q']
    [Module.Projective R Q'] : vcls R (Q × Q') = vcls R Q + vcls R Q' := by
  obtain ⟨n, e, he, ⟨ψ⟩⟩ := exists_rowModEquiv (R := R) Q
  obtain ⟨n', f, hf, ⟨ψ'⟩⟩ := exists_rowModEquiv (R := R) Q'
  obtain ⟨χ⟩ := rowMod_fromBlocks he hf
  rw [vcls_eq he ψ, vcls_eq hf ψ', vcls_eq (fromBlocks_idem he hf)
    ((ψ.prodCongr ψ').trans χ.symm), cls_fromBlocks]

/-- A direct summand of a finitely generated projective module is finitely generated
projective. -/
theorem fgp_of_equiv_prod {L : Type u} [AddCommGroup L] [Module R L] [Module.Finite R Q]
    [Module.Projective R Q] (φ : Q ≃ₗ[R] Q' × L) :
    Module.Finite R Q' ∧ Module.Projective R Q' := by
  refine ⟨Module.Finite.of_surjective (LinearMap.fst R Q' L ∘ₗ φ.toLinearMap) fun x =>
    ⟨φ.symm (x, 0), by simp⟩, ?_⟩
  exact Module.Projective.of_split (φ.symm.toLinearMap ∘ₗ LinearMap.inl R Q' L)
    (LinearMap.fst R Q' L ∘ₗ φ.toLinearMap) (LinearMap.ext fun x => by simp)

theorem fgp_of_equiv [Module.Finite R Q] [Module.Projective R Q] (φ : Q ≃ₗ[R] Q') :
    Module.Finite R Q' ∧ Module.Projective R Q' :=
  ⟨Module.Finite.equiv φ, Module.Projective.of_equiv φ⟩

/-- The `1 × 1` matrix `(ε)`. -/
def mat1 (ε : R) : Matrix (Fin 1) (Fin 1) R := Matrix.of fun _ _ => ε

theorem mat1_idem {ε : R} (hε : ε * ε = ε) : mat1 ε * mat1 ε = mat1 ε := by
  ext i j; simp [mat1, Matrix.mul_apply, hε]

/-- The left ideal `R ε` of an idempotent is `rowMod (ε)`. -/
noncomputable def spanIdemEquiv {ε : R} (hε : ε * ε = ε) :
    Submodule.span R {ε} ≃ₗ[R] rowMod (mat1 ε) := by
  have hv : ∀ v : Fin 1 → R, v ᵥ* mat1 ε = fun _ => v 0 * ε := fun v => by
    ext i; simp [mat1, Matrix.vecMul, dotProduct]
  have hs : ∀ x ∈ Submodule.span R {ε}, x * ε = x := fun x hx => by
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [smul_eq_mul, mul_assoc, hε]
  exact
  { toFun := fun x => ⟨fun _ => (x : R), (mem_rowMod (mat1_idem hε) _).2 (by
      rw [hv, hs x x.2])⟩
    invFun := fun v => ⟨(v : Fin 1 → R) 0, by
      rw [← congrFun ((mem_rowMod (mat1_idem hε) _).1 v.2) 0, hv]
      exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun v => by
      apply Subtype.ext
      funext i
      rw [Subsingleton.elim i 0] }

theorem fgp_span_idem {ε : R} (hε : ε * ε = ε) :
    Module.Finite R (Submodule.span R {ε}) ∧ Module.Projective R (Submodule.span R {ε}) := by
  have := rowMod.projective (mat1_idem hε)
  exact fgp_of_equiv (spanIdemEquiv hε).symm

theorem vcls_span_idem {ε : R} (hε : ε * ε = ε) :
    vcls R (Submodule.span R {ε}) = cls (mat1 ε) (mat1_idem hε) :=
  vcls_eq _ (spanIdemEquiv hε)

end vcls

namespace Core

open Module

variable {k : Type u} [Field k] {ι : Type} [DecidableEq ι]
  {Λ : Type}
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  {σ : ∀ l, (ι → k) →ₐ[k] R l}
  {C : Type u} [Ring C] [Algebra k C] {σC : (ι → k) →ₐ[k] C} {inc : ∀ l, R l →ₐ[k] C}
set_option hygiene false in
local notation "R_[" μ "]" => Rμ k ι R μ
set_option hygiene false in
local notation "inc_[" μ "]" => incμ σC inc μ

/-! ## The left ideals `R_μ e_j` -/

theorem eμ_idem (μ : Option Λ) (j : ι) : eμ σ μ j * eμ σ μ j = eμ σ μ j := by
  rw [eμ_mul_eμ, if_pos rfl]

theorem ee_idem (j : ι) : (ee j : ι → k) * ee j = ee j := by
  rw [ee_mul_ee, if_pos rfl]

/-- The class of `k^ι e_j` in `V(k^ι)`. -/
noncomputable def eecls (j : ι) : V (ι → k) := cls (mat1 (ee j : ι → k)) (mat1_idem (ee_idem j))

theorem fgp_lid (μ : Option Λ) (j : ι) :
    Module.Finite (R_[μ]) (lid σ μ j) ∧ Module.Projective (R_[μ]) (lid σ μ j) :=
  fgp_span_idem (eμ_idem μ j)

theorem vcls_lid (μ : Option Λ) (j : ι) :
    vcls (R_[μ]) (lid σ μ j) = V.map (σμ σ μ).toRingHom (eecls j) := by
  rw [vcls_span_idem (eμ_idem μ j), eecls, V.map_cls]
  exact cls_congr (by ext; rfl) _ _

theorem vcls_lid_none (j : ι) : (vcls (R_[none]) (lid σ none j) : V (ι → k)) = eecls j := by
  rw [vcls_lid]
  exact V.map_id _

theorem vcls_lid_some (l : Λ) (j : ι) :
    (vcls (R_[some l]) (lid σ (some l) j) : V (R l)) = V.map (σ l).toRingHom (eecls j) :=
  vcls_lid _ j

/-! ## Additive maps out of row modules -/

/-- An additive map out of `rowMod e`, semilinear along `φ`, is determined by the rows of `e`. -/
theorem rowMod_map_eq_sum {S : Type u} [Ring S] {m : Type} [Fintype m] [DecidableEq m]
    {e : Matrix m m S}
    (he : e * e = e) {P : Type u} [AddCommGroup P] [Module C P] (φ : S →+* C)
    {G : Type*} [FunLike G (rowMod e) P] [AddMonoidHomClass G (rowMod e) P] (g : G)
    (hg : ∀ (r : S) a, g (r • a) = φ r • g a) (a : rowMod e) :
    g a = ∑ i, φ ((a : m → S) i) • g ⟨e i, row_mem_range_vecMulLinear e i⟩ := by
  have ha : a = ∑ i, (a : m → S) i • (⟨e i, row_mem_range_vecMulLinear e i⟩ : rowMod e) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rw [← vecMul_eq_sum_smul, (mem_rowMod he _).1 a.2]
  conv_lhs => rw [ha]
  rw [map_sum]
  simp only [hg]

/-! ## Realising a family of idempotents -/

section real

variable {m : Option Λ → Type} [∀ μ, Fintype (m μ)] [∀ μ, DecidableEq (m μ)]
  (e : ∀ μ, Matrix (m μ) (m μ) (R_[μ]))

variable (σC inc) in
/-- The block-diagonal matrix `diag(e μ)` over `C`. -/
noncomputable def realE [DecidableEq Λ] : Matrix (Σ μ, m μ) (Σ μ, m μ) C :=
  Matrix.blockDiagonal' fun μ => (e μ).map (inc_[μ])

omit [DecidableEq ι] [(μ : Option Λ) → DecidableEq (m μ)] in
theorem realE_idem [Fintype Λ] [DecidableEq Λ] (he : ∀ μ, e μ * e μ = e μ) :
    realE σC inc e * realE σC inc e = realE σC inc e :=
  blockDiagonal'_idem _ fun μ => by rw [← Matrix.map_mul, he]

omit [DecidableEq ι] in
theorem cls_realE [Fintype Λ] [DecidableEq Λ] (he : ∀ μ, e μ * e μ = e μ) :
    cls (realE σC inc e) (realE_idem e he) =
      ∑ μ, V.map (inc_[μ]).toRingHom (cls (e μ) (he μ)) := by
  simp only [V.map_cls]
  exact cls_blockDiagonal' _ _

variable (σC inc) in
/-- Put a vector over `R_μ` into block `μ`, mapped to `C`. -/
noncomputable def jvec [DecidableEq Λ] (μ : Option Λ) : (m μ → R_[μ]) →ₗ[k] ((Σ μ, m μ) → C) where
  toFun v x := (Pi.single (M := fun ν => m ν → C) μ (fun a => inc_[μ] (v a))) x.1 x.2
  map_add' v w := by
    ext ⟨ν, b⟩
    by_cases h : ν = μ
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  map_smul' c v := by
    ext ⟨ν, b⟩
    by_cases h : ν = μ
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]

omit [DecidableEq ι] [(μ : Option Λ) → Fintype (m μ)] [(μ : Option Λ) → DecidableEq (m μ)] in
theorem jvec_same [DecidableEq Λ] (μ : Option Λ) (v : m μ → R_[μ]) (a : m μ) :
    jvec σC inc μ v ⟨μ, a⟩ = inc_[μ] (v a) := by
  simp [jvec]

omit [DecidableEq ι] [(μ : Option Λ) → Fintype (m μ)] [(μ : Option Λ) → DecidableEq (m μ)] in
theorem jvec_ne [DecidableEq Λ] {μ ν : Option Λ} (h : ν ≠ μ) (v : m μ → R_[μ]) (b : m ν) :
    jvec σC inc μ v ⟨ν, b⟩ = 0 := by
  simp [jvec, Pi.single_eq_of_ne h]

omit [DecidableEq ι] [(μ : Option Λ) → Fintype (m μ)] [(μ : Option Λ) → DecidableEq (m μ)] in
theorem jvec_smul [DecidableEq Λ] (μ : Option Λ) (r : R_[μ]) (v : m μ → R_[μ]) :
    jvec σC inc μ (r • v) = inc_[μ] r • jvec σC inc μ v := by
  ext ⟨ν, b⟩
  by_cases h : ν = μ
  · subst h; simp [jvec_same]
  · simp [jvec_ne h]

omit [DecidableEq ι] [(μ : Option Λ) → Fintype (m μ)] [(μ : Option Λ) → DecidableEq (m μ)] in
theorem jvec_row [DecidableEq Λ] (μ : Option Λ) (i : m μ) :
    jvec σC inc μ (e μ i) = realE σC inc e ⟨μ, i⟩ := by
  ext ⟨ν, b⟩
  by_cases h : ν = μ
  · subst h; simp [jvec_same, realE, Matrix.blockDiagonal'_apply_eq]
  · rw [jvec_ne h, realE, Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm h)]

omit [DecidableEq ι] in
theorem jvec_mem [Fintype Λ] [DecidableEq Λ] (he : ∀ μ, e μ * e μ = e μ) (μ : Option Λ)
    {v : m μ → R_[μ]}
    (hv : v ∈ rowMod (e μ)) : jvec σC inc μ v ∈ rowMod (realE σC inc e) := by
  rw [← (mem_rowMod (he μ) v).1 hv, vecMul_eq_sum_smul, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [jvec_smul, jvec_row]
  exact Submodule.smul_mem _ _ (row_mem_range_vecMulLinear _ _)

variable (σC inc) in
/-- The inclusion of `rowMod (e μ)` into `rowMod (diag e)`. -/
noncomputable def jmap [Fintype Λ] [DecidableEq Λ] (he : ∀ μ, e μ * e μ = e μ) (μ : Option Λ) :
    rowMod (e μ) →ₗ[k] rowMod (realE σC inc e) where
  toFun v := ⟨jvec σC inc μ v, jvec_mem e he μ v.2⟩
  map_add' v w := Subtype.ext ((jvec σC inc μ).map_add (v : m μ → R_[μ]) w)
  map_smul' c v := Subtype.ext ((jvec σC inc μ).map_smul c (v : m μ → R_[μ]))

omit [DecidableEq ι] in
theorem jmap_coe [Fintype Λ] [DecidableEq Λ] (he : ∀ μ, e μ * e μ = e μ) (μ : Option Λ)
    (a : rowMod (e μ)) :
    (jmap σC inc e he μ a : (Σ μ, m μ) → C) = jvec σC inc μ (a : m μ → R_[μ]) := rfl

variable (C) in
/-- `w ↦ ∑ w_x y_x`. -/
noncomputable def sumMap {α : Type} [Fintype α] {P : Type u} [AddCommGroup P] [Module C P]
    (y : α → P) : (α → C) →ₗ[C] P where
  toFun w := ∑ x, w x • y x
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum, mul_smul]

theorem sumMap_apply {α : Type} [Fintype α] {P : Type u} [AddCommGroup P] [Module C P]
    (y : α → P) (w : α → C) : sumMap C y w = ∑ x, w x • y x := rfl

variable (σC inc) in
/-- **The realisation**: `rowMod (diag e)` has the standard presentation with components
`rowMod (e μ)`. -/
noncomputable def realPres [Fintype Λ] [DecidableEq Λ] (hC : IsCoprod k σ C σC inc)
    (he : ∀ μ, e μ * e μ = e μ) :
    StdPres σ σC inc (rowMod (realE σC inc e)) where
  coprod := hC
  A μ := rowMod (e μ)
  j := jmap σC inc e he
  j_smul μ r a := Subtype.ext (jvec_smul μ r (a : m μ → R_[μ]))
  lift P _ _ _ _ g hg := by
    refine ⟨sumMap C (fun x => g x.1 ⟨e x.1 x.2, row_mem_range_vecMulLinear _ _⟩) ∘ₗ
      (rowMod (realE σC inc e)).subtype, fun μ a => ?_, fun f hf => ?_⟩
    · rw [LinearMap.comp_apply, Submodule.subtype_apply, sumMap_apply, jmap_coe,
        Fintype.sum_sigma, Finset.sum_eq_single μ (fun ν _ h => by simp [jvec_ne h])
        (by simp)]
      simp only [jvec_same]
      exact (rowMod_map_eq_sum (he μ) (inc_[μ]).toRingHom (g μ)
        (hg μ) a).symm
    · refine LinearMap.ext fun w => ?_
      rw [rowMod_map_eq_sum (realE_idem e he) (RingHom.id C) f
        (fun r a => f.map_smul r a) w, LinearMap.comp_apply, Submodule.subtype_apply,
        sumMap_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      have : (⟨realE σC inc e x, row_mem_range_vecMulLinear _ x⟩ : rowMod (realE σC inc e)) =
          jmap σC inc e he x.1 ⟨e x.1 x.2, row_mem_range_vecMulLinear _ _⟩ :=
        Subtype.ext (jvec_row e x.1 x.2).symm
      exact (congrArg f this).trans (hf x.1 _)

omit [DecidableEq ι] in
theorem realPres_FGP [Fintype Λ] [DecidableEq Λ] (hC : IsCoprod k σ C σC inc)
    (he : ∀ μ, e μ * e μ = e μ) :
    (realPres σC inc e hC he).FGP := fun μ => show Module.Finite _ (rowMod (e μ)) ∧ _ from
  ⟨rowMod.finite (e μ), rowMod.projective (he μ)⟩

end real

/-! ## Presentations and classes -/

section pres

variable {M M' : Type u} [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]
  [AddCommGroup M'] [Module C M'] [Module k M'] [IsScalarTower k C M']

omit [DecidableEq ι] in
/-- Standard presentations with isomorphic components present isomorphic modules. -/
theorem StdPres.nonempty_equiv (p : StdPres σ σC inc M) (q : StdPres σ σC inc M')
    (h : p.IsoExcept q ∅) : Nonempty (M ≃ₗ[C] M') := by
  have φ : ∀ μ, p.A μ ≃ₗ[R_[μ]] q.A μ := fun μ => (h μ (Set.notMem_empty μ)).some
  obtain ⟨F, hF, -⟩ := p.lift M' (fun μ => q.j μ ∘ₗ ((φ μ).toLinearMap.restrictScalars k))
    (fun μ r a => by simp [q.j_smul])
  obtain ⟨G, hG, -⟩ := q.lift M (fun μ => p.j μ ∘ₗ ((φ μ).symm.toLinearMap.restrictScalars k))
    (fun μ r a => by simp [p.j_smul])
  obtain ⟨_, _, hu⟩ := p.lift M p.j p.j_smul
  obtain ⟨_, _, hu'⟩ := q.lift M' q.j q.j_smul
  have h1 : G ∘ₗ F = LinearMap.id :=
    (hu _ fun μ a => by simp [hF, hG]).trans (hu _ fun μ a => rfl).symm
  have h2 : F ∘ₗ G = LinearMap.id :=
    (hu' _ fun μ a => by simp [hF, hG]).trans (hu' _ fun μ a => rfl).symm
  exact ⟨LinearEquiv.ofLinearMap F G h2 h1⟩

/-- The classes of the components, as an element of `V(k^ι) × ∏ V(R l)`. -/
noncomputable def StdPres.vpair (p : StdPres σ σC inc M) : V (ι → k) × ∀ l, V (R l) :=
  (vcls (R_[none]) (p.A none), fun l => vcls (R_[some l]) (p.A (some l)))

omit [DecidableEq ι] [IsScalarTower k C M] in
theorem StdPres.FGP.of_iso {p : StdPres σ σC inc M} {q : StdPres σ σC inc M'} (hp : p.FGP)
    (h : p.IsoExcept q ∅) : q.FGP := fun μ => by
  have := (hp μ).1; have := (hp μ).2
  exact fgp_of_equiv (h μ (Set.notMem_empty μ)).some

omit [DecidableEq ι] [IsScalarTower k C M] in
theorem StdPres.vpair_eq [DecidableEq Λ] {p : StdPres σ σC inc M} {q : StdPres σ σC inc M'}
    (hp : p.FGP)
    (h : p.IsoExcept q ∅) : p.vpair = q.vpair := by
  have hv : ∀ μ, vcls _ (p.A μ) = vcls _ (q.A μ) := fun μ => by
    have := (hp μ).1; have := (hp μ).2
    exact vcls_congr (h μ (Set.notMem_empty μ)).some
  exact Prod.ext (hv none) (funext fun l => hv (some l))

variable [DecidableEq Λ] (r : (V (ι → k) × ∀ l, V (R l)) → (V (ι → k) × ∀ l, V (R l)) → Prop)
  (hr : ∀ (a : V (ι → k)) (l : Λ), r (a, 0) (0, Pi.single l (V.map (σ l).toRingHom a)))
include hr

/-- A basic transfer moves `k^ι e_j` to `R_l e_j`. -/
theorem StdPres.rel_of_transfer {p p' : StdPres σ σC inc M} (hp : p.FGP) (hp' : p'.FGP)
    (l : Λ) (j : ι) (hiso : p.IsoExcept p' {none, some l})
    (φ1 : p.A (some l) ≃ₗ[R_[some l]] p'.A (some l) × lid σ (some l) j)
    (φ2 : p'.A none ≃ₗ[R_[none]] p.A none × lid σ none j) :
    addConGen r p.vpair p'.vpair := by
  have hl1 := fgp_lid (σ := σ) (some l) j
  have hl0 := fgp_lid (σ := σ) none j
  let base : V (ι → k) × ∀ l, V (R l) := (p.vpair.1, p'.vpair.2)
  have e1 : p.vpair = base + (0, Pi.single l (V.map (σ l).toRingHom (eecls j))) := by
    refine Prod.ext (add_zero _).symm (funext fun l' => ?_)
    by_cases hl : l' = l
    · subst hl
      have := (hp (some l')).1; have := (hp (some l')).2
      have := (hp' (some l')).1; have := (hp' (some l')).2
      have := hl1.1; have := hl1.2
      have key : vcls (R_[some l']) (p.A (some l')) =
          vcls (R_[some l']) (p'.A (some l')) +
            vcls (R_[some l']) (lid σ (some l') j) := by
        rw [vcls_congr φ1, vcls_prod]
      simp only [base, Prod.snd_add, Pi.add_apply, Pi.single_eq_same]
      rw [← vcls_lid_some]
      exact key
    · have := (hp (some l')).1; have := (hp (some l')).2
      simp only [base, Prod.snd_add, Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
      exact vcls_congr (hiso (some l') (by simp [hl])).some
  have e2 : p'.vpair = base + (eecls j, 0) := by
    refine Prod.ext ?_ (add_zero _).symm
    have := (hp none).1; have := (hp none).2
    have := (hp' none).1; have := (hp' none).2
    have := hl0.1; have := hl0.2
    have key : vcls (R_[none]) (p'.A none) =
        vcls (R_[none]) (p.A none) + vcls (R_[none]) (lid σ none j) := by
      rw [vcls_congr φ2, vcls_prod]
    simp only [base, Prod.fst_add]
    rw [← vcls_lid_none (σ := σ)]
    exact key
  rw [e1, e2]
  exact (addConGen r).add ((addConGen r).refl base)
    ((addConGen r).symm (AddConGen.Rel.of _ _ (hr _ l)))

theorem StdPres.Step.rel {p p' : StdPres σ σC inc M} (h : p.Step p') (hp : p.FGP) :
    p'.FGP ∧ addConGen r p.vpair p'.vpair := by
  rcases h with h | ⟨l, j, hiso, ⟨φ1⟩, ⟨φ2⟩⟩ | ⟨l, j, hiso, ⟨ψ1⟩, ⟨ψ2⟩⟩
  · refine ⟨hp.of_iso h, ?_⟩
    rw [StdPres.vpair_eq hp h]
    exact (addConGen r).refl _
  · have hp' : p'.FGP := by
      intro μ
      by_cases hμ : μ ∈ ({none, some l} : Set (Option Λ))
      · rcases hμ with rfl | hμ
        · have := (hp none).1; have := (hp none).2
          have hl0 := fgp_lid (σ := σ) none j
          have := hl0.1; have := hl0.2
          exact fgp_of_equiv φ2.symm
        · rw [Set.mem_singleton_iff] at hμ
          subst hμ
          have := (hp (some l)).1; have := (hp (some l)).2
          exact fgp_of_equiv_prod φ1
      · have := (hp μ).1; have := (hp μ).2
        exact fgp_of_equiv (hiso μ hμ).some
    exact ⟨hp', StdPres.rel_of_transfer r hr hp hp' l j hiso φ1 φ2⟩
  · have hp' : p'.FGP := by
      intro μ
      by_cases hμ : μ ∈ ({none, some l} : Set (Option Λ))
      · rcases hμ with rfl | hμ
        · have := (hp none).1; have := (hp none).2
          exact fgp_of_equiv_prod ψ1
        · rw [Set.mem_singleton_iff] at hμ
          subst hμ
          have := (hp (some l)).1; have := (hp (some l)).2
          have hl1 := fgp_lid (σ := σ) (some l) j
          have := hl1.1; have := hl1.2
          exact fgp_of_equiv ψ2.symm
      · have := (hp μ).1; have := (hp μ).2
        exact fgp_of_equiv (hiso μ hμ).some
    exact ⟨hp', (addConGen r).symm (StdPres.rel_of_transfer r hr hp' hp l j
      (fun μ hμ => ⟨(hiso μ hμ).some.symm⟩) ψ2 ψ1)⟩

theorem StdPres.Reach.rel {p p' : StdPres σ σC inc M} (h : p.Reach p') (hp : p.FGP) :
    p'.FGP ∧ addConGen r p.vpair p'.vpair := by
  induction h with
  | refl => exact ⟨hp, (addConGen r).refl _⟩
  | tail _ hs ih =>
    obtain ⟨hb, hrel⟩ := ih
    obtain ⟨hc, hrel'⟩ := StdPres.Step.rel r hr hs hb
    exact ⟨hc, (addConGen r).trans hrel hrel'⟩

end pres


end Core

end Bergman
