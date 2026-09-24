/-
**Idempotent matrices and finitely generated projective modules.**

For an idempotent `e ∈ M_m(R)`, `rowMod e = R^{1×m} e` is a finitely generated projective left
`R`-module, every such module arises this way, and `rowMod e ≅ rowMod f` iff `e` and `f` are
Murray–von Neumann equivalent.  This is the dictionary between `V R` (`Bergman/Idem.lean`) and
modules.
-/
import KappaMonoid.Bergman.Idem

universe u

namespace Bergman

open Matrix

variable {R : Type u} [Ring R]

section

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- `R^{1×m} e`: the row vectors `v` with `v e = v`, as a left submodule of `m → R`. -/
def rowMod (e : Matrix m m R) : Submodule R (m → R) := LinearMap.range (Matrix.vecMulLinear e)

omit [DecidableEq m] in
theorem mem_rowMod {e : Matrix m m R} (he : e * e = e) (v : m → R) :
    v ∈ rowMod e ↔ v ᵥ* e = v :=
  ⟨vecMul_idem_of_mem_range he, fun h => ⟨v, h⟩⟩

omit [DecidableEq m] in
/-- `rowMod e` is a direct summand of `m → R`, split by `v ↦ v e`. -/
theorem rowMod.projective {e : Matrix m m R} (he : e * e = e) :
    Module.Projective R (rowMod e) :=
  Module.Projective.of_split (rowMod e).subtype (vecMulLinear e).rangeRestrict
    (LinearMap.ext fun v => Subtype.ext (vecMul_idem_of_mem_range he v.2))

omit [DecidableEq m] in
instance rowMod.finite (e : Matrix m m R) : Module.Finite R (rowMod e) :=
  Module.Finite.range _

omit [DecidableEq m] [DecidableEq n] in
/-- Equivalent idempotents give isomorphic modules: `v ↦ v a`, with inverse `w ↦ w b`. -/
theorem MvN.rowModEquiv {e : Matrix m m R} {f : Matrix n n R} (he : e * e = e)
    (hf : f * f = f) (h : MvN e f) : Nonempty (rowMod e ≃ₗ[R] rowMod f) := by
  obtain ⟨a, b, hab, hba⟩ := h
  have ha : ∀ v ∈ rowMod e, v ᵥ* a ∈ rowMod f := fun v hv => by
    rw [mem_rowMod hf, vecMul_vecMul, ← hba, ← Matrix.mul_assoc, hab, ← vecMul_vecMul,
      (mem_rowMod he v).1 hv]
  have hb : ∀ w ∈ rowMod f, w ᵥ* b ∈ rowMod e := fun w hw => by
    rw [mem_rowMod he, vecMul_vecMul, ← hab, ← Matrix.mul_assoc, hba, ← vecMul_vecMul,
      (mem_rowMod hf w).1 hw]
  refine ⟨LinearEquiv.ofLinearMap
    (((vecMulLinear a).comp (rowMod e).subtype).codRestrict (rowMod f) fun v => ha v v.2)
    (((vecMulLinear b).comp (rowMod f).subtype).codRestrict (rowMod e) fun w => hb w w.2) ?_ ?_⟩
  · refine LinearMap.ext fun w => Subtype.ext ?_
    change (w : n → R) ᵥ* b ᵥ* a = w
    rw [vecMul_vecMul, hba, (mem_rowMod hf _).1 w.2]
  · refine LinearMap.ext fun v => Subtype.ext ?_
    change (v : m → R) ᵥ* a ᵥ* b = v
    rw [vecMul_vecMul, hab, (mem_rowMod he _).1 v.2]

/-- Isomorphic modules come from equivalent idempotents. -/
theorem mvN_of_rowModEquiv {e : Matrix m m R} {f : Matrix n n R} (he : e * e = e)
    (hf : f * f = f) (h : Nonempty (rowMod e ≃ₗ[R] rowMod f)) : MvN e f := by
  obtain ⟨φ⟩ := h
  exact mvN_of_rangeEquiv he hf φ

theorem rowModEquiv_iff_cls_eq {e : Matrix m m R} {f : Matrix n n R} (he : e * e = e)
    (hf : f * f = f) : Nonempty (rowMod e ≃ₗ[R] rowMod f) ↔ cls e he = cls f hf :=
  ⟨fun h => (cls_eq_cls he hf).2 (mvN_of_rowModEquiv he hf h),
    fun h => MvN.rowModEquiv he hf ((cls_eq_cls he hf).1 h)⟩

omit [DecidableEq m] [DecidableEq n] in
theorem vecMul_fromBlocks_zero (e : Matrix m m R) (f : Matrix n n R) (v : m ⊕ n → R) :
    v ᵥ* Matrix.fromBlocks e 0 0 f = Sum.elim ((v ∘ Sum.inl) ᵥ* e) ((v ∘ Sum.inr) ᵥ* f) := by
  ext (j | j) <;> simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type]

/-- Block sums give direct sums. -/
theorem rowMod_fromBlocks {e : Matrix m m R} {f : Matrix n n R} (he : e * e = e)
    (hf : f * f = f) : Nonempty (rowMod (Matrix.fromBlocks e 0 0 f) ≃ₗ[R] rowMod e × rowMod f) := by
  have hE := fromBlocks_idem he hf
  have h1 : ∀ v ∈ rowMod (Matrix.fromBlocks e 0 0 f), v ∘ Sum.inl ∈ rowMod e := fun v hv => by
    have := (mem_rowMod hE v).1 hv
    rw [vecMul_fromBlocks_zero] at this
    rw [mem_rowMod he]
    simpa using congrArg (· ∘ Sum.inl) this
  have h2 : ∀ v ∈ rowMod (Matrix.fromBlocks e 0 0 f), v ∘ Sum.inr ∈ rowMod f := fun v hv => by
    have := (mem_rowMod hE v).1 hv
    rw [vecMul_fromBlocks_zero] at this
    rw [mem_rowMod hf]
    simpa using congrArg (· ∘ Sum.inr) this
  have h3 : ∀ x ∈ rowMod e, ∀ y ∈ rowMod f,
      Sum.elim x y ∈ rowMod (Matrix.fromBlocks e 0 0 f) := fun x hx y hy => by
    rw [mem_rowMod hE, vecMul_fromBlocks_zero, Sum.elim_comp_inl, Sum.elim_comp_inr,
      (mem_rowMod he x).1 hx, (mem_rowMod hf y).1 hy]
  exact ⟨{
    toFun := fun v => (⟨_, h1 v v.2⟩, ⟨_, h2 v v.2⟩)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    invFun := fun p => ⟨Sum.elim p.1 p.2, h3 _ p.1.2 _ p.2.2⟩
    left_inv := fun v => Subtype.ext (Sum.elim_comp_inl_inr (v : m ⊕ n → R))
    right_inv := fun _ => rfl }⟩

theorem rowMod_one : Nonempty (rowMod (1 : Matrix (Fin 1) (Fin 1) R) ≃ₗ[R] R) := by
  have h : rowMod (1 : Matrix (Fin 1) (Fin 1) R) = ⊤ :=
    LinearMap.range_eq_top.2 fun v => ⟨v, by simp⟩
  exact ⟨(LinearEquiv.ofTop _ h).trans (LinearEquiv.funUnique (Fin 1) R R)⟩

theorem rowMod_subsingleton_iff {e : Matrix m m R} (he : e * e = e) :
    Subsingleton (rowMod e) ↔ e = 0 := by
  constructor
  · intro hs
    ext i j
    have : (⟨e i, row_mem_range_vecMulLinear e i⟩ : rowMod e) = 0 := Subsingleton.elim _ _
    exact congrFun (congrArg Subtype.val this) j
  · rintro rfl
    refine ⟨fun x y => Subtype.ext ?_⟩
    have h0 : ∀ z : rowMod (0 : Matrix m m R), (z : m → R) = 0 := fun z => by
      rw [← (mem_rowMod he _).1 z.2, Matrix.vecMul_zero]
    rw [h0 x, h0 y]

end

/-- Every finitely generated projective module is some `rowMod e`.

Proof: a surjection `π : R^n → Q` has a section `s`; the idempotent endomorphism `s ∘ π` of
`R^n` is right multiplication by a matrix `e`, and `Q ≅ range s = range (s ∘ π) = rowMod e`. -/
theorem exists_rowModEquiv (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    [Module.Finite R Q] : ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) R) (_ : e * e = e),
      Nonempty (Q ≃ₗ[R] rowMod e) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R Q
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let p : (Fin n → R) →ₗ[R] (Fin n → R) := s ∘ₗ π
  let e : Matrix (Fin n) (Fin n) R := Matrix.of fun i => p (Pi.single i 1)
  have hp : vecMulLinear e = p := by
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simp [e]
  have hpp : ∀ v, p (p v) = p v := fun v => by
    change s (π (s (π v))) = s (π v)
    rw [← LinearMap.comp_apply π s, hs, LinearMap.id_apply]
  have he : e * e = e := by
    ext i j
    have : e i ᵥ* e = e i := by
      rw [← vecMulLinear_apply, hp]
      exact hpp _
    exact congrFun this j
  have hinj : Function.Injective s := fun x y hxy => by
    have := congrArg π hxy
    rwa [← LinearMap.comp_apply π s, ← LinearMap.comp_apply π s, hs] at this
  have hrange : LinearMap.range s = rowMod e := by
    rw [rowMod, hp]
    exact (LinearMap.range_comp_of_range_eq_top s (LinearMap.range_eq_top.2 hπ)).symm
  exact ⟨n, e, he, ⟨(LinearEquiv.ofInjective s hinj).trans (LinearEquiv.ofEq _ _ hrange)⟩⟩

end Bergman
