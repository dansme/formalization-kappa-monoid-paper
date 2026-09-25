/-
**Basic transfers and transvections, as changes of standard presentation** (Bergman §1, §6).

The `C`-module `M` stays fixed; each move replaces its standard presentation by another one,
related by one `StdPres.Step`, and records how the images of the components change.

* `StdPres.transfer_some`: `A l = ker φ ⊕ R_l a` with `φ : A l → R_l e_j`, `φ a = e_j`; the summand
  `R_l a` is moved to `A none` as `k^ι a` (Bergman's case `(a_λ)` of §6).
* `StdPres.transfer_none`: the same from `A none` to `A l` (case `(a_0)`).
* `StdPres.transvection`: `θ = id - (m ↦ ε(m) x)` for a functional `ε` supported on `A μ₁` with
  `ε x = 0` (case `(b)`); the new presentation is `θ ∘ j` on `μ₁`.
-/
import KappaMonoid.Bergman.Core.Pres

universe u

set_option linter.unusedSectionVars false

namespace Bergman.Core

open Module

variable {k : Type u} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  {σ : ∀ l, (ι → k) →ₐ[k] R l} [Fact (∀ l, Function.Injective (σ l))]
  {C : Type u} [Ring C] [Algebra k C] {σC : (ι → k) →ₐ[k] C} {inc : ∀ l, R l →ₐ[k] C}
  [Fact (IsCoprod k σ C σC inc)]
  {M : Type u} [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]

/-- The functional `ε : M → C` extending `incμ ∘ e` on `A μ₁` and `0` on the other components. -/
theorem StdPres.exists_functional (p : StdPres σ σC inc M) (μ₁ : Option Λ)
    (e : p.A μ₁ →ₗ[Rμ k ι R μ₁] Rμ k ι R μ₁) :
    ∃ ε : M →ₗ[C] C, (∀ b, ε (p.j μ₁ b) = incμ σC inc μ₁ (e b)) ∧
      ∀ μ ≠ μ₁, ∀ b, ε (p.j μ b) = 0 := by
  classical
  let G : p.A μ₁ →ₗ[k] C := (incμ σC inc μ₁).toLinearMap.comp (e.restrictScalars k)
  let g : ∀ μ, p.A μ →ₗ[k] C := Function.update (fun μ => 0) μ₁ G
  have hg : ∀ μ (r : Rμ k ι R μ) b, g μ (r • b) = incμ σC inc μ r • g μ b := by
    intro μ r b
    by_cases h : μ = μ₁
    · subst h
      simp only [g, Function.update_self, G, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        LinearMap.restrictScalars_apply, map_smul, smul_eq_mul, map_mul]
    · simp only [g, Function.update_of_ne h, LinearMap.zero_apply, smul_zero]
  obtain ⟨ε, hε, -⟩ := p.lift C g hg
  refine ⟨ε, fun b => ?_, fun μ h b => ?_⟩
  · rw [hε]; simp [g, G]
  · rw [hε]; simp [g, Function.update_of_ne h]

theorem lid_mul_eμ {μ : Option Λ} {j : ι} (c : lid σ μ j) :
    (c : Rμ k ι R μ) * eμ σ μ j = c := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 c.2
  rw [← hr, smul_eq_mul, mul_assoc, eμ_mul_eμ, if_pos rfl]

/-! ## A general basic transfer

The summand `R_{μ₀} a` of `A μ₀` (split off by `φ : A μ₀ → R_{μ₀} e_j` with `φ a = e_j`) is moved to
`A μ₁` as `R_{μ₁} e_j`.  Uniformly in `μ`, the new component is the submodule
`{(x, c) | ψ x = 0, c = 0 unless μ = μ₁}` of `A μ × R_μ e_j`, where `ψ` is `φ` on `μ₀` and `0`
elsewhere, and `(x, c) ↦ j x + c · j(a)`. -/

namespace TransferAux

variable (p : StdPres σ σC inc M) (μ₀ μ₁ : Option Λ) (j : ι)
  (φ : p.A μ₀ →ₗ[Rμ k ι R μ₀] lid σ μ₀ j) (a : p.A μ₀)

/-- `φ` on `A μ₀`, `0` on the other components. -/
noncomputable def ψ : ∀ μ, p.A μ →ₗ[Rμ k ι R μ] lid σ μ j :=
  Function.update (fun _ => 0) μ₀ φ

/-- `a` in `A μ₀`, `0` in the other components. -/
noncomputable def aμ : ∀ μ, p.A μ := Function.update (fun _ => 0) μ₀ a

theorem ψ_self : ψ p μ₀ j φ μ₀ = φ := Function.update_self _ _ _

theorem ψ_of_ne {μ : Option Λ} (h : μ ≠ μ₀) : ψ p μ₀ j φ μ = 0 := Function.update_of_ne h _ _

theorem aμ_self : aμ p μ₀ a μ₀ = a := Function.update_self _ _ _

theorem aμ_of_ne {μ : Option Λ} (h : μ ≠ μ₀) : aμ p μ₀ a μ = 0 := Function.update_of_ne h _ _

variable {φ a} in
theorem ψ_smul_aμ (ha : (φ a : Rμ k ι R μ₀) = eμ σ μ₀ j) (μ : Option Λ) (x : p.A μ) :
    ψ p μ₀ j φ μ ((ψ p μ₀ j φ μ x : Rμ k ι R μ) • aμ p μ₀ a μ) = ψ p μ₀ j φ μ x := by
  by_cases h : μ = μ₀
  · subst h
    rw [ψ_self, aμ_self]
    apply Subtype.ext
    rw [map_smul, Submodule.coe_smul, smul_eq_mul, ha, lid_mul_eμ]
  · rw [ψ_of_ne p μ₀ j φ h]; simp

/-- The new components. -/
def S (μ : Option Λ) : Submodule (Rμ k ι R μ) (p.A μ × lid σ μ j) where
  carrier := {y | ψ p μ₀ j φ μ y.1 = 0 ∧ (μ ≠ μ₁ → y.2 = 0)}
  add_mem' := fun ha hb => ⟨by rw [Prod.fst_add, map_add, ha.1, hb.1, add_zero],
    fun h => by rw [Prod.snd_add, ha.2 h, hb.2 h, add_zero]⟩
  zero_mem' := ⟨map_zero _, fun _ => rfl⟩
  smul_mem' := fun c y hy => ⟨by rw [Prod.smul_fst, map_smul, hy.1, smul_zero],
    fun h => by rw [Prod.smul_snd, hy.2 h, smul_zero]⟩

theorem mem_S {μ : Option Λ} {y : p.A μ × lid σ μ j} :
    y ∈ S p μ₀ μ₁ j φ μ ↔ ψ p μ₀ j φ μ y.1 = 0 ∧ (μ ≠ μ₁ → y.2 = 0) := Iff.rfl

variable {φ a} in
/-- The projection `x ↦ (x - ψ(x) a, 0)` onto the new component. -/
noncomputable def π (ha : (φ a : Rμ k ι R μ₀) = eμ σ μ₀ j) (μ : Option Λ) :
    p.A μ →ₗ[Rμ k ι R μ] S p μ₀ μ₁ j φ μ where
  toFun x := ⟨(x - (ψ p μ₀ j φ μ x : Rμ k ι R μ) • aμ p μ₀ a μ, 0),
    ⟨by rw [map_sub, ψ_smul_aμ p μ₀ j ha, sub_self], fun _ => rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext; apply Prod.ext
    · simp only [map_add, Submodule.coe_add, add_smul, Submodule.coe_add, Prod.fst_add]; abel
    · simp
  map_smul' r x := by
    apply Subtype.ext; apply Prod.ext
    · simp only [map_smul, Submodule.coe_smul, smul_eq_mul, mul_smul, smul_sub, RingHom.id_apply,
        Submodule.coe_smul, Prod.smul_fst]
    · simp

theorem π_coe (ha : (φ a : Rμ k ι R μ₀) = eμ σ μ₀ j) (μ : Option Λ) (x : p.A μ) :
    (π p μ₀ μ₁ j ha μ x : p.A μ × lid σ μ j) =
      (x - (ψ p μ₀ j φ μ x : Rμ k ι R μ) • aμ p μ₀ a μ, 0) := rfl

/-- The new maps into `M`: `(x, c) ↦ j x + c · j(a)`. -/
noncomputable def jj (μ : Option Λ) : S p μ₀ μ₁ j φ μ →ₗ[k] M where
  toFun y := p.j μ (y : p.A μ × lid σ μ j).1 +
    incμ σC inc μ ((y : p.A μ × lid σ μ j).2 : Rμ k ι R μ) • p.j μ₀ a
  map_add' y z := by
    simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, map_add, add_smul]; abel
  map_smul' c y := by
    simp only [Submodule.coe_smul_of_tower, Prod.smul_fst, Prod.smul_snd, map_smul,
      RingHom.id_apply, smul_add, smul_assoc]

theorem jj_apply (μ : Option Λ) (y : S p μ₀ μ₁ j φ μ) :
    jj p μ₀ μ₁ j φ a μ y = p.j μ (y : p.A μ × lid σ μ j).1 +
      incμ σC inc μ ((y : p.A μ × lid σ μ j).2 : Rμ k ι R μ) • p.j μ₀ a := rfl

theorem jj_smul (μ : Option Λ) (r : Rμ k ι R μ) (y : S p μ₀ μ₁ j φ μ) :
    jj p μ₀ μ₁ j φ a μ (r • y) = incμ σC inc μ r • jj p μ₀ μ₁ j φ a μ y := by
  simp only [jj_apply, Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, p.j_smul, smul_eq_mul,
    map_mul, mul_smul, smul_add]

/-- `(0, e_j)` in the new component `μ₁`. -/
def y₁ : S p μ₀ μ₁ j φ μ₁ :=
  ⟨(0, ⟨eμ σ μ₁ j, Submodule.mem_span_singleton_self _⟩), ⟨map_zero _, fun h => (h rfl).elim⟩⟩

variable {a} in
theorem jj_y₁ (hja : eμ σ μ₀ j • a = a) : jj p μ₀ μ₁ j φ a μ₁ (y₁ p μ₀ μ₁ j φ) = p.j μ₀ a := by
  rw [jj_apply]
  change p.j μ₁ 0 + incμ σC inc μ₁ (eμ σ μ₁ j) • p.j μ₀ a = _
  rw [map_zero, zero_add, incμ_eμ (σ := σ) σC inc, ← incμ_eμ (σ := σ) σC inc μ₀, ← p.j_smul, hja]

variable {φ a} in
theorem j_eq (ha : (φ a : Rμ k ι R μ₀) = eμ σ μ₀ j) (hja : eμ σ μ₀ j • a = a) (μ : Option Λ)
    (x : p.A μ) :
    p.j μ x = jj p μ₀ μ₁ j φ a μ (π p μ₀ μ₁ j ha μ x) +
      incμ σC inc μ (ψ p μ₀ j φ μ x : Rμ k ι R μ) • jj p μ₀ μ₁ j φ a μ₁ (y₁ p μ₀ μ₁ j φ) := by
  rw [jj_y₁ p μ₀ μ₁ j φ hja, jj_apply, π_coe]
  simp only [map_sub, p.j_smul, ZeroMemClass.coe_zero, map_zero, zero_smul, add_zero]
  have : incμ σC inc μ (ψ p μ₀ j φ μ x : Rμ k ι R μ) • p.j μ (aμ p μ₀ a μ) =
      incμ σC inc μ (ψ p μ₀ j φ μ x : Rμ k ι R μ) • p.j μ₀ a := by
    by_cases h : μ = μ₀
    · subst h; rw [aμ_self]
    · rw [ψ_of_ne p μ₀ j φ h]; simp
  rw [this, sub_add_cancel]

variable {φ a} in
theorem exists_unique_lift (ha : (φ a : Rμ k ι R μ₀) = eμ σ μ₀ j) (hja : eμ σ μ₀ j • a = a)
    (P : Type u) [AddCommGroup P] [Module C P] [Module k P] [IsScalarTower k C P]
    (g' : ∀ μ, S p μ₀ μ₁ j φ μ →ₗ[k] P)
    (hg' : ∀ μ (r : Rμ k ι R μ) y, g' μ (r • y) = incμ σC inc μ r • g' μ y) :
    ∃! f : M →ₗ[C] P, ∀ μ y, f (jj p μ₀ μ₁ j φ a μ y) = g' μ y := by
  set q := g' μ₁ (y₁ p μ₀ μ₁ j φ) with hq_def
  have hq : ∀ c : lid σ μ₁ j, incμ σC inc μ₁ (c : Rμ k ι R μ₁) • q =
      g' μ₁ ⟨(0, c), ⟨map_zero _, fun h => (h rfl).elim⟩⟩ := by
    intro c
    rw [hq_def, ← hg']
    congr 1
    apply Subtype.ext; apply Prod.ext
    · change (c : Rμ k ι R μ₁) • (0 : p.A μ₁) = 0
      exact smul_zero _
    · apply Subtype.ext
      change (c : Rμ k ι R μ₁) * eμ σ μ₁ j = c
      exact lid_mul_eμ c
  let g : ∀ μ, p.A μ →ₗ[k] P := fun μ =>
    { toFun := fun x => g' μ (π p μ₀ μ₁ j ha μ x) +
        incμ σC inc μ (ψ p μ₀ j φ μ x : Rμ k ι R μ) • q
      map_add' := fun x y => by
        simp only [map_add, Submodule.coe_add, add_smul]; abel
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, LinearMap.map_smul_of_tower, map_smul,
          Submodule.coe_smul_of_tower, smul_add, smul_assoc] }
  have hg_apply : ∀ μ x, g μ x = g' μ (π p μ₀ μ₁ j ha μ x) +
      incμ σC inc μ (ψ p μ₀ j φ μ x : Rμ k ι R μ) • q := fun _ _ => rfl
  have hg : ∀ μ (r : Rμ k ι R μ) x, g μ (r • x) = incμ σC inc μ r • g μ x := by
    intro μ r x
    simp only [hg_apply, map_smul, hg', Submodule.coe_smul, smul_eq_mul, map_mul, mul_smul,
      smul_add]
  obtain ⟨f, hf, huniq⟩ := p.lift P g hg
  have hga : g μ₀ a = q := by
    have hπ : π p μ₀ μ₁ j ha μ₀ a = 0 := by
      apply Subtype.ext
      rw [π_coe, ψ_self, aμ_self, ha, hja, sub_self]; rfl
    rw [hg_apply, hπ, map_zero, zero_add, ψ_self, ha, incμ_eμ (σ := σ) σC inc,
      ← incμ_eμ (σ := σ) σC inc μ₁, hq_def, ← hg']
    congr 1
    apply Subtype.ext; apply Prod.ext
    · change eμ σ μ₁ j • (0 : p.A μ₁) = 0
      exact smul_zero _
    · apply Subtype.ext
      change eμ σ μ₁ j * eμ σ μ₁ j = eμ σ μ₁ j
      rw [eμ_mul_eμ, if_pos rfl]
  refine ⟨f, fun μ y => ?_, fun f₁ hf₁ => huniq f₁ fun μ x => ?_⟩
  · rw [jj_apply, map_add, map_smul, hf, hf, hga, hg_apply]
    obtain ⟨⟨x, c⟩, hx, hc⟩ := y
    have hπ : π p μ₀ μ₁ j ha μ x = ⟨(x, 0), ⟨hx, fun _ => rfl⟩⟩ := by
      apply Subtype.ext
      rw [π_coe]
      change (x - (ψ p μ₀ j φ μ x : Rμ k ι R μ) • aμ p μ₀ a μ, 0) = (x, 0)
      rw [hx]; simp
    change g' μ _ + incμ σC inc μ (ψ p μ₀ j φ μ x : Rμ k ι R μ) • q +
      incμ σC inc μ (c : Rμ k ι R μ) • q = _
    have hx' : ψ p μ₀ j φ μ x = 0 := hx
    rw [hπ]; simp only [hx', ZeroMemClass.coe_zero, map_zero, zero_smul, add_zero]
    by_cases h : μ = μ₁
    · subst h
      rw [hq c, ← map_add]
      congr 1
      apply Subtype.ext; apply Prod.ext
      · exact add_zero x
      · exact zero_add c
    · have hc0 : c = 0 := hc h
      subst hc0
      rw [ZeroMemClass.coe_zero, map_zero, zero_smul, add_zero]
  · rw [j_eq p μ₀ μ₁ j ha hja μ x, map_add, map_smul, hf₁, hf₁, hg_apply]

/-- The new presentation. -/
noncomputable def pres (ha : (φ a : Rμ k ι R μ₀) = eμ σ μ₀ j) (hja : eμ σ μ₀ j • a = a) :
    StdPres σ σC inc M where
  coprod := p.coprod
  A μ := S p μ₀ μ₁ j φ μ
  j μ := jj p μ₀ μ₁ j φ a μ
  j_smul := jj_smul p μ₀ μ₁ j φ a
  lift P _ _ _ _ g' hg' := exists_unique_lift p μ₀ μ₁ j ha hja P g' hg'

end TransferAux

open TransferAux in
/-- **A general basic transfer**: the summand `R_{μ₀} a` of `A μ₀`, split off by `φ`, moves to
`A μ₁` as a summand `R_{μ₁} e_j`. -/
theorem StdPres.exists_transfer (p : StdPres σ σC inc M) (μ₀ μ₁ : Option Λ) (h01 : μ₀ ≠ μ₁)
    (j : ι) (φ : p.A μ₀ →ₗ[Rμ k ι R μ₀] lid σ μ₀ j) (a : p.A μ₀)
    (ha : (φ a : Rμ k ι R μ₀) = eμ σ μ₀ j) (hja : eμ σ μ₀ j • a = a) :
    ∃ p' : StdPres σ σC inc M,
      Nonempty (p.A μ₀ ≃ₗ[Rμ k ι R μ₀] p'.A μ₀ × lid σ μ₀ j) ∧
      Nonempty (p'.A μ₁ ≃ₗ[Rμ k ι R μ₁] p.A μ₁ × lid σ μ₁ j) ∧
      p.IsoExcept p' {μ₀, μ₁} ∧ (p.FG → p'.FG) ∧
      (∀ μ, μ ≠ μ₀ → μ ≠ μ₁ → Set.range (p'.j μ) = Set.range (p.j μ)) ∧
      Set.range (p'.j μ₀) = p.j μ₀ '' {x | φ x = 0} ∧
      Set.range (p'.j μ₁) =
        {m | ∃ (x : p.A μ₁) (c : Rμ k ι R μ₁), m = p.j μ₁ x + incμ σC inc μ₁ c • p.j μ₀ a} := by
  let p' := pres p μ₀ μ₁ j φ a ha hja
  -- the source component
  let e₀ : p.A μ₀ ≃ₗ[Rμ k ι R μ₀] S p μ₀ μ₁ j φ μ₀ × lid σ μ₀ j :=
    { (π p μ₀ μ₁ j ha μ₀).prod (ψ p μ₀ j φ μ₀) with
      invFun := fun z => (z.1 : p.A μ₀ × lid σ μ₀ j).1 + (z.2 : Rμ k ι R μ₀) • a
      left_inv := fun x => by
        change (x - (ψ p μ₀ j φ μ₀ x : Rμ k ι R μ₀) • aμ p μ₀ a μ₀) +
          (ψ p μ₀ j φ μ₀ x : Rμ k ι R μ₀) • a = x
        rw [aμ_self, sub_add_cancel]
      right_inv := fun z => by
        obtain ⟨⟨⟨x, c⟩, hx, hc⟩, d⟩ := z
        have hx' : φ x = 0 := by rw [← ψ_self p μ₀ j φ]; exact hx
        have hc' : c = 0 := hc h01
        subst hc'
        have hψ : ψ p μ₀ j φ μ₀ (x + (d : Rμ k ι R μ₀) • a) = d := by
          rw [ψ_self]; apply Subtype.ext
          rw [map_add, hx', zero_add, map_smul, Submodule.coe_smul, smul_eq_mul, ha, lid_mul_eμ]
        refine Prod.ext (Subtype.ext ?_) hψ
        change (x + (d : Rμ k ι R μ₀) • a -
          (ψ p μ₀ j φ μ₀ (x + (d : Rμ k ι R μ₀) • a) : Rμ k ι R μ₀) • aμ p μ₀ a μ₀, 0) = (x, 0)
        rw [hψ, aμ_self, add_sub_cancel_right] }
  -- the target component
  let e₁ : S p μ₀ μ₁ j φ μ₁ ≃ₗ[Rμ k ι R μ₁] p.A μ₁ × lid σ μ₁ j :=
    { (S p μ₀ μ₁ j φ μ₁).subtype with
      invFun := fun z => ⟨z, ⟨by rw [ψ_of_ne p μ₀ j φ h01.symm]; rfl, fun h => (h rfl).elim⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  -- the other components
  let eo : ∀ μ, μ ≠ μ₀ → μ ≠ μ₁ → (p.A μ ≃ₗ[Rμ k ι R μ] S p μ₀ μ₁ j φ μ) := fun μ h0 h1 =>
    { toFun := fun x => ⟨(x, 0), ⟨by rw [ψ_of_ne p μ₀ j φ h0]; rfl, fun _ => rfl⟩⟩
      map_add' := fun x y => Subtype.ext (Prod.ext rfl (add_zero 0).symm)
      map_smul' := fun r x => Subtype.ext (Prod.ext rfl (smul_zero r).symm)
      invFun := fun y => (y : p.A μ × lid σ μ j).1
      left_inv := fun _ => rfl
      right_inv := fun y => Subtype.ext (Prod.ext rfl (y.2.2 h1).symm) }
  have hjo : ∀ μ (h1 : μ ≠ μ₁) (y : S p μ₀ μ₁ j φ μ),
      jj p μ₀ μ₁ j φ a μ y = p.j μ (y : p.A μ × lid σ μ j).1 := fun μ h1 y => by
    rw [jj_apply, y.2.2 h1, ZeroMemClass.coe_zero, map_zero, zero_smul, add_zero]
  refine ⟨p', ⟨e₀⟩, ⟨e₁⟩, fun μ hμ => ?_, fun hfg μ => ?_, fun μ h0 h1 => ?_, ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hμ
    exact ⟨eo μ hμ.1 hμ.2⟩
  · have := hfg μ
    by_cases h0 : μ = μ₀
    · subst h0
      exact Module.Finite.of_surjective ((LinearMap.fst _ _ _).comp e₀.toLinearMap)
        (Prod.fst_surjective.comp e₀.surjective)
    by_cases h1 : μ = μ₁
    · subst h1
      exact Module.Finite.equiv e₁.symm
    · exact Module.Finite.equiv (eo μ h0 h1)
  · ext m
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (hjo μ h1 y).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨eo μ h0 h1 x, hjo μ h1 _⟩
  · ext m
    constructor
    · rintro ⟨(y : S p μ₀ μ₁ j φ μ₀), rfl⟩
      refine ⟨(y : p.A μ₀ × lid σ μ₀ j).1, ?_, (hjo μ₀ h01 y).symm⟩
      have h := y.2.1
      rwa [ψ_self] at h
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨(x, 0), ⟨?_, fun _ => rfl⟩⟩, hjo μ₀ h01 _⟩
      rw [ψ_self]; exact hx
  · ext m
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, _, rfl⟩
    · rintro ⟨x, c, rfl⟩
      refine ⟨⟨(x, ⟨c * eμ σ μ₁ j, Submodule.mem_span_singleton.2 ⟨c, rfl⟩⟩),
        ⟨by rw [ψ_of_ne p μ₀ j φ h01.symm]; rfl, fun h => (h rfl).elim⟩⟩, ?_⟩
      change p.j μ₁ x + incμ σC inc μ₁ (c * eμ σ μ₁ j) • p.j μ₀ a = _
      rw [map_mul, mul_smul, incμ_eμ (σ := σ) σC inc, ← incμ_eμ (σ := σ) σC inc μ₀, ← p.j_smul,
        hja]

/-- **Basic transfer from `A l` to `A none`.** -/
theorem StdPres.transfer_some (p : StdPres σ σC inc M) (l : Λ) (j : ι)
    (φ : p.A (some l) →ₗ[Rμ k ι R (some l)] lid σ (some l) j) (a : p.A (some l))
    (ha : (φ a : Rμ k ι R (some l)) = eμ σ (some l) j) (hja : eμ σ (some l) j • a = a) :
    ∃ p' : StdPres σ σC inc M, p.Step p' ∧ (p.FG → p'.FG) ∧
      (∀ μ, μ ≠ none → μ ≠ some l → Set.range (p'.j μ) = Set.range (p.j μ)) ∧
      Set.range (p'.j (some l)) = p.j (some l) '' {x | φ x = 0} ∧
      Set.range (p'.j none) =
        {m | ∃ (x : p.A none) (c : ι → k), m = p.j none x + σC c • p.j (some l) a} := by
  obtain ⟨p', h0, h1, hiso, hfg, hoth, hr0, hr1⟩ :=
    p.exists_transfer (some l) none (Option.some_ne_none l) j φ a ha hja
  refine ⟨p', Or.inr (Or.inl ⟨l, j, ?_, h0, h1⟩), hfg, fun μ hn hs => hoth μ hs hn, hr0, hr1⟩
  rwa [Set.pair_comm] at hiso

/-- **Basic transfer from `A none` to `A l`.** -/
theorem StdPres.transfer_none (p : StdPres σ σC inc M) (l : Λ) (j : ι)
    (ψ : p.A none →ₗ[Rμ k ι R none] lid σ none j) (a : p.A none)
    (ha : (ψ a : Rμ k ι R none) = eμ σ none j) (hja : eμ σ none j • a = a) :
    ∃ p' : StdPres σ σC inc M, p.Step p' ∧ (p.FG → p'.FG) ∧
      (∀ μ, μ ≠ none → μ ≠ some l → Set.range (p'.j μ) = Set.range (p.j μ)) ∧
      Set.range (p'.j none) = p.j none '' {x | ψ x = 0} ∧
      Set.range (p'.j (some l)) =
        {m | ∃ (x : p.A (some l)) (r : R l), m = p.j (some l) x + inc l r • p.j none a} := by
  obtain ⟨p', h0, h1, hiso, hfg, hoth, hr0, hr1⟩ :=
    p.exists_transfer none (some l) (Option.some_ne_none l).symm j ψ a ha hja
  exact ⟨p', Or.inr (Or.inr ⟨l, j, hiso, h0, h1⟩), hfg, hoth, hr0, hr1⟩

/-- A standard presentation transported along a `C`-linear isomorphism: same components, maps
composed with the isomorphism. -/
noncomputable def StdPres.transport (p : StdPres σ σC inc M) {M' : Type u} [AddCommGroup M']
    [Module C M'] [Module k M'] [IsScalarTower k C M'] (θ : M ≃ₗ[C] M') :
    StdPres σ σC inc M' where
  coprod := p.coprod
  A := p.A
  j μ := (θ.toLinearMap.restrictScalars k).comp (p.j μ)
  j_smul μ r b := by
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      p.j_smul, map_smul]
  lift P _ _ _ _ g hg := by
    obtain ⟨f, hf, huniq⟩ := p.lift P g hg
    refine ⟨f ∘ₗ θ.symm.toLinearMap, fun μ b => ?_, fun f' hf' => ?_⟩
    · simp [hf]
    · have : f' ∘ₗ θ.toLinearMap = f := huniq _ fun μ b => hf' μ b
      ext m
      rw [← this]
      simp

theorem StdPres.transport_j (p : StdPres σ σC inc M) {M' : Type u} [AddCommGroup M']
    [Module C M'] [Module k M'] [IsScalarTower k C M'] (θ : M ≃ₗ[C] M') (μ : Option Λ)
    (b : p.A μ) : (p.transport θ).j μ b = θ (p.j μ b) := rfl

/-- **Transvection.** -/
theorem StdPres.transvection (p : StdPres σ σC inc M) (μ₁ : Option Λ) (ε : M →ₗ[C] C)
    (hε : ∀ μ ≠ μ₁, ∀ b, ε (p.j μ b) = 0) (x : M) (hx : ε x = 0) :
    ∃ p' : StdPres σ σC inc M, p.Step p' ∧ (p.FG → p'.FG) ∧
      (∀ μ ≠ μ₁, Set.range (p'.j μ) = Set.range (p.j μ)) ∧
      Set.range (p'.j μ₁) = {m | ∃ b, m = p.j μ₁ b - ε (p.j μ₁ b) • x} := by
  let θ₀ : M →ₗ[C] M := LinearMap.id - ε.smulRight x
  let θ₁ : M →ₗ[C] M := LinearMap.id + ε.smulRight x
  have hεx : ∀ c : C, ε (c • x) = 0 := fun c => by rw [map_smul, hx, smul_zero]
  let θ : M ≃ₗ[C] M := LinearEquiv.ofLinearMap θ₀ θ₁
    (LinearMap.ext fun m => by
      simp [θ₀, θ₁, hεx])
    (LinearMap.ext fun m => by
      simp [θ₀, θ₁, hεx])
  have hθ : ∀ m, θ m = m - ε m • x := fun m => rfl
  refine ⟨p.transport θ, Or.inl fun μ _ => ⟨LinearEquiv.refl _ _⟩, fun h => h, fun μ hμ => ?_, ?_⟩
  · have e : ∀ b : p.A μ, (p.transport θ).j μ b = p.j μ b := fun b => by
      rw [StdPres.transport_j, hθ, hε μ hμ b, zero_smul, sub_zero]
    ext m
    exact ⟨fun ⟨b, hb⟩ => ⟨b, (e b).symm.trans hb⟩, fun ⟨b, hb⟩ => ⟨b, (e b).trans hb⟩⟩
  · ext m
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

end Bergman.Core
