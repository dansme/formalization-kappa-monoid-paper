/-
**The monoid `V(R)` via idempotent matrices.**

`V(R)` is the monoid of isomorphism classes of finitely generated projective modules.  Here it is
set up as the monoid of Murray–von Neumann classes of idempotent matrices, which has three
advantages over the module-theoretic definition for the realisation proof:

* it is side-free (left and right modules give the same monoid);
* it is functorial along ring homomorphisms by applying the map entrywise, which makes it
  compatible with matrix rings (`V (Matrix n n R) ≅ V R`) and with directed colimits;
* it needs no tensor products over non-commutative rings.

The translation to modules (`R^{1×n} e`) is in `Bergman/IdemModule.lean`.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.RingTheory.HopkinsLevitzki

universe u v w

namespace Bergman

open Matrix

section MvN

variable {R : Type u} [Ring R]

/-- **Murray–von Neumann equivalence** of square matrices, possibly of different sizes and
index types: `e = a * b` and `f = b * a`.  For idempotents this says that the modules
`R^{1×m} e` and `R^{1×n} f` are isomorphic. -/
def MvN {m n : Type*} [Fintype m] [Fintype n] (e : Matrix m m R) (f : Matrix n n R) : Prop :=
  ∃ (a : Matrix m n R) (b : Matrix n m R), a * b = e ∧ b * a = f

variable {l m n o : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype o]

theorem MvN.refl {e : Matrix m m R} (he : e * e = e) : MvN e e := ⟨e, e, he, he⟩

theorem MvN.symm {e : Matrix m m R} {f : Matrix n n R} (h : MvN e f) : MvN f e := by
  obtain ⟨a, b, hab, hba⟩ := h
  exact ⟨b, a, hba, hab⟩

/-- Transitivity needs the outer matrices to be idempotent: `(a a')(b' b) = a f b = e e`. -/
theorem MvN.trans {e : Matrix m m R} {f : Matrix n n R} {g : Matrix o o R} (he : e * e = e)
    (hg : g * g = g) (h₁ : MvN e f) (h₂ : MvN f g) : MvN e g := by
  obtain ⟨a, b, hab, hba⟩ := h₁
  obtain ⟨a', b', hab', hba'⟩ := h₂
  refine ⟨a * a', b' * b, ?_, ?_⟩
  · calc a * a' * (b' * b) = a * (a' * b') * b := by simp only [Matrix.mul_assoc]
      _ = a * (b * a) * b := by rw [hab', hba]
      _ = (a * b) * (a * b) := by simp only [Matrix.mul_assoc]
      _ = e := by rw [hab, he]
  · calc b' * b * (a * a') = b' * (b * a) * a' := by simp only [Matrix.mul_assoc]
      _ = b' * (a' * b') * a' := by rw [hba, hab']
      _ = (b' * a') * (b' * a') := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hba', hg]

theorem reindex_idem {e : Matrix m m R} (he : e * e = e) (σ : m ≃ n) :
    Matrix.reindex σ σ e * Matrix.reindex σ σ e = Matrix.reindex σ σ e := by
  rw [Matrix.reindex_apply, ← Matrix.submatrix_mul e e σ.symm σ.symm σ.symm σ.symm.bijective, he]

/-- A reindexed matrix is equivalent to the original. -/
theorem MvN.reindex {e : Matrix m m R} (he : e * e = e) (σ : m ≃ n) :
    MvN e (Matrix.reindex σ σ e) := by
  refine ⟨e.submatrix id σ.symm, e.submatrix σ.symm id, ?_, ?_⟩
  · rw [← Matrix.submatrix_mul e e id σ.symm id σ.symm.bijective, he, Matrix.submatrix_id_id]
  · rw [← Matrix.submatrix_mul e e σ.symm id σ.symm Function.bijective_id, he,
      Matrix.reindex_apply]

/-- Block sums respect equivalence. -/
theorem MvN.fromBlocks {e : Matrix m m R} {f : Matrix n n R} {e' : Matrix l l R}
    {f' : Matrix o o R} (h : MvN e e') (h' : MvN f f') :
    MvN (Matrix.fromBlocks e 0 0 f) (Matrix.fromBlocks e' 0 0 f') := by
  obtain ⟨a, b, hab, hba⟩ := h
  obtain ⟨a', b', hab', hba'⟩ := h'
  exact ⟨Matrix.fromBlocks a 0 0 a', Matrix.fromBlocks b 0 0 b',
    by simp [Matrix.fromBlocks_multiply, hab, hab'],
    by simp [Matrix.fromBlocks_multiply, hba, hba']⟩

theorem fromBlocks_idem {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {e : Matrix m m R} {f : Matrix n n R} (he : e * e = e) (hf : f * f = f) :
    Matrix.fromBlocks e 0 0 f * Matrix.fromBlocks e 0 0 f = Matrix.fromBlocks e 0 0 f := by
  rw [Matrix.fromBlocks_multiply]; simp [he, hf]

/-- Block sums commute up to equivalence. -/
theorem MvN.fromBlocks_comm [DecidableEq m] [DecidableEq n] {e : Matrix m m R} {f : Matrix n n R} (he : e * e = e)
    (hf : f * f = f) : MvN (Matrix.fromBlocks e 0 0 f) (Matrix.fromBlocks f 0 0 e) := by
  have := MvN.reindex (fromBlocks_idem he hf) (Equiv.sumComm m n)
  convert this using 1
  ext (i | i) (j | j) <;> simp [Matrix.reindex_apply]

/-- Block sums are associative up to equivalence. -/
theorem MvN.fromBlocks_assoc [DecidableEq m] [DecidableEq n] [DecidableEq o]
    {e : Matrix m m R} {f : Matrix n n R} {g : Matrix o o R}
    (he : e * e = e) (hf : f * f = f) (hg : g * g = g) :
    MvN (Matrix.fromBlocks (Matrix.fromBlocks e 0 0 f) 0 0 g)
      (Matrix.fromBlocks e 0 0 (Matrix.fromBlocks f 0 0 g)) := by
  have := MvN.reindex (fromBlocks_idem (fromBlocks_idem he hf) hg) (Equiv.sumAssoc m n o)
  convert this using 1
  ext (i | i | i) (j | j | j) <;> simp [Matrix.reindex_apply]

/-- Adding a zero block does not change the class. -/
theorem MvN.fromBlocks_zero {e : Matrix m m R} (he : e * e = e) :
    MvN (Matrix.fromBlocks e 0 0 (0 : Matrix n n R)) e := by
  refine ⟨Matrix.fromRows e 0, Matrix.fromCols e 0, ?_, ?_⟩
  · rw [Matrix.fromRows_mul_fromCols]; simp [he]
  · rw [Matrix.fromCols_mul_fromRows]; simp [he]

theorem MvN.map {T : Type v} [Ring T] (φ : R →+* T) {e : Matrix m m R} {f : Matrix n n R}
    (h : MvN e f) : MvN (e.map φ) (f.map φ) := by
  obtain ⟨a, b, hab, hba⟩ := h
  exact ⟨a.map φ, b.map φ, by rw [← Matrix.map_mul, hab], by rw [← Matrix.map_mul, hba]⟩

/-- A matrix equivalent to a matrix of size zero is zero. -/
theorem MvN.eq_zero_of_isEmpty [IsEmpty n] {e : Matrix m m R} {f : Matrix n n R}
    (h : MvN e f) : e = 0 := by
  obtain ⟨a, b, hab, -⟩ := h
  rw [← hab]
  ext i j
  simp [Matrix.mul_apply]

end MvN

/-! ## Row modules

`R^{1×m} e` for an idempotent `e`, as the range of `v ↦ v e`.  The module-theoretic dictionary
is in `Bergman/IdemModule.lean` (where this range is called `rowMod e`); the one fact needed
here, that isomorphic row modules come from equivalent idempotents, is proved in this file
because `V` of a division ring uses it. -/

section rangeEquiv

variable {R : Type u} [Ring R] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n]

omit [DecidableEq m] [Fintype n] [DecidableEq n] in
theorem vecMul_eq_sum_smul (v : m → R) (M : Matrix m n R) : v ᵥ* M = ∑ i, v i • M i := by
  ext j
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

theorem row_mem_range_vecMulLinear (e : Matrix m m R) (i : m) :
    e i ∈ LinearMap.range (vecMulLinear e) :=
  ⟨Pi.single i 1, by simp; rfl⟩

omit [DecidableEq m] in
theorem vecMul_idem_of_mem_range {e : Matrix m m R} (he : e * e = e) {v : m → R}
    (hv : v ∈ LinearMap.range (vecMulLinear e)) : v ᵥ* e = v := by
  obtain ⟨w, rfl⟩ := hv
  simp only [vecMulLinear_apply, vecMul_vecMul, he]

/-- The matrix of a linear map between row modules: its `i`-th row is the image of the `i`-th
row of `e`. -/
noncomputable def rangeMat {e : Matrix m m R} {f : Matrix n n R}
    (φ : LinearMap.range (vecMulLinear e) →ₗ[R] LinearMap.range (vecMulLinear f)) :
    Matrix m n R :=
  Matrix.of fun i => (φ ⟨e i, row_mem_range_vecMulLinear e i⟩ : n → R)

omit [DecidableEq n] in
/-- A linear map between row modules is right multiplication by `rangeMat`. -/
theorem vecMul_rangeMat {e : Matrix m m R} {f : Matrix n n R} (he : e * e = e)
    (φ : LinearMap.range (vecMulLinear e) →ₗ[R] LinearMap.range (vecMulLinear f))
    (v : LinearMap.range (vecMulLinear e)) : (v : m → R) ᵥ* rangeMat φ = φ v := by
  have hv : v = ∑ i, (v : m → R) i • ⟨e i, row_mem_range_vecMulLinear e i⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [← vecMul_eq_sum_smul, vecMul_idem_of_mem_range he v.2]
  conv_rhs => rw [hv]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
  rw [vecMul_eq_sum_smul]
  rfl

/-- Isomorphic row modules come from equivalent idempotents. -/
theorem mvN_of_rangeEquiv {e : Matrix m m R} {f : Matrix n n R} (he : e * e = e)
    (hf : f * f = f)
    (φ : LinearMap.range (vecMulLinear e) ≃ₗ[R] LinearMap.range (vecMulLinear f)) : MvN e f := by
  refine ⟨rangeMat φ.toLinearMap, rangeMat φ.symm.toLinearMap, ?_, ?_⟩
  · ext i j
    have := vecMul_rangeMat hf φ.symm.toLinearMap (φ ⟨e i, row_mem_range_vecMulLinear e i⟩)
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
    exact congrFun this j
  · ext i j
    have := vecMul_rangeMat he φ.toLinearMap (φ.symm ⟨f i, row_mem_range_vecMulLinear f i⟩)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    exact congrFun this j

end rangeEquiv

/-! ## Idempotent matrices and `V(R)` -/

variable (R : Type u) [Ring R]

/-- An idempotent square matrix over `R`, of any finite size. -/
structure Idem where
  /-- The size. -/
  n : ℕ
  /-- The matrix. -/
  e : Matrix (Fin n) (Fin n) R
  idem : e * e = e

instance Idem.setoid : Setoid (Idem R) where
  r e f := MvN e.e f.e
  iseqv := ⟨fun e => MvN.refl e.idem, MvN.symm, fun {e _ g} => MvN.trans e.idem g.idem⟩

/-- **`V(R)`**: Murray–von Neumann classes of idempotent matrices over `R`, i.e. isomorphism
classes of finitely generated projective modules. -/
def V : Type u := Quotient (Idem.setoid R)

variable {R}

section cls

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The class in `V(R)` of an idempotent matrix indexed by any finite type. -/
noncomputable def cls (e : Matrix m m R) (he : e * e = e) : V R :=
  Quotient.mk _ ⟨Fintype.card m, Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin m) e,
    by rw [← Matrix.coe_reindexLinearEquiv ℕ R, Matrix.reindexLinearEquiv_mul, he]⟩

omit [DecidableEq m] in
theorem cls_congr {e e' : Matrix m m R} (h : e = e') (he : e * e = e) (he' : e' * e' = e') :
    cls e he = cls e' he' := by
  subst h; rfl

omit [DecidableEq m] [DecidableEq n] in
theorem cls_eq_cls {e : Matrix m m R} (he : e * e = e) {f : Matrix n n R} (hf : f * f = f) :
    cls e he = cls f hf ↔ MvN e f := by
  have he' := reindex_idem he (Fintype.equivFin m)
  have hf' := reindex_idem hf (Fintype.equivFin n)
  constructor
  · intro h
    have h' : MvN (Matrix.reindex _ _ e) (Matrix.reindex _ _ f) := Quotient.exact h
    exact ((MvN.reindex he _).trans he hf' h').trans he hf (MvN.reindex hf _).symm
  · intro h
    exact Quotient.sound
      (((MvN.reindex he _).symm.trans he' hf h).trans he' hf' (MvN.reindex hf _))

theorem cls_mk (e : Idem R) : cls e.e e.idem = Quotient.mk _ e :=
  Quotient.sound (MvN.reindex e.idem _).symm

theorem cls_surjective (x : V R) : ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) R) (he : e * e = e),
    cls e he = x := by
  obtain ⟨e⟩ := x
  exact ⟨e.n, e.e, e.idem, cls_mk e⟩

omit [DecidableEq m] [DecidableEq n] in
theorem cls_reindex {e : Matrix m m R} (he : e * e = e) (σ : m ≃ n) :
    cls (Matrix.reindex σ σ e) (reindex_idem he σ) = cls e he :=
  (cls_eq_cls _ _).2 (MvN.reindex he σ).symm

omit [DecidableEq m] [DecidableEq n] in
theorem submatrix_idem {e : Matrix m m R} (he : e * e = e) (σ : n ≃ m) :
    e.submatrix σ σ * e.submatrix σ σ = e.submatrix σ σ :=
  reindex_idem he σ.symm

omit [DecidableEq m] [DecidableEq n] in
theorem cls_submatrix {e : Matrix m m R} (he : e * e = e) (σ : n ≃ m) :
    cls (e.submatrix σ σ) (submatrix_idem he σ) = cls e he :=
  cls_reindex he σ.symm

end cls

noncomputable instance : Zero (V R) := ⟨cls (0 : Matrix (Fin 0) (Fin 0) R) (by simp)⟩

noncomputable instance : Add (V R) :=
  ⟨Quotient.lift₂
    (fun e f : Idem R => cls (Matrix.fromBlocks e.e 0 0 f.e) (fromBlocks_idem e.idem f.idem))
    (fun _ _ _ _ h h' => (cls_eq_cls _ _).2 (MvN.fromBlocks h h'))⟩

theorem zero_def : (0 : V R) = cls (0 : Matrix (Fin 0) (Fin 0) R) (by simp) := rfl

theorem cls_fromBlocks_aux {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {e : Matrix m m R} (he : e * e = e) {f : Matrix n n R} (hf : f * f = f) :
    cls (Matrix.fromBlocks e 0 0 f) (fromBlocks_idem he hf) = cls e he + cls f hf := by
  change _ = cls (Matrix.fromBlocks (Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin m) e)
    0 0 (Matrix.reindex (Fintype.equivFin n) (Fintype.equivFin n) f))
    (fromBlocks_idem (reindex_idem he _) (reindex_idem hf _))
  exact (cls_eq_cls _ _).2 (MvN.fromBlocks (MvN.reindex he _) (MvN.reindex hf _))

noncomputable instance : AddCommMonoid (V R) where
  add_assoc x y z := by
    induction x using Quotient.inductionOn with | h x => ?_
    induction y using Quotient.inductionOn with | h y => ?_
    induction z using Quotient.inductionOn with | h z => ?_
    rw [← cls_mk x, ← cls_mk y, ← cls_mk z, ← cls_fromBlocks_aux x.idem y.idem,
      ← cls_fromBlocks_aux (fromBlocks_idem x.idem y.idem) z.idem,
      ← cls_fromBlocks_aux y.idem z.idem,
      ← cls_fromBlocks_aux x.idem (fromBlocks_idem y.idem z.idem), cls_eq_cls]
    exact MvN.fromBlocks_assoc x.idem y.idem z.idem
  zero_add x := by
    induction x using Quotient.inductionOn with | h x => ?_
    rw [← cls_mk x, zero_def, ← cls_fromBlocks_aux, cls_eq_cls]
    exact (MvN.fromBlocks_comm (by simp) x.idem).trans (fromBlocks_idem (by simp) x.idem) x.idem
      (MvN.fromBlocks_zero x.idem)
  add_zero x := by
    induction x using Quotient.inductionOn with | h x => ?_
    rw [← cls_mk x, zero_def, ← cls_fromBlocks_aux, cls_eq_cls]
    exact MvN.fromBlocks_zero x.idem
  add_comm x y := by
    induction x using Quotient.inductionOn with | h x => ?_
    induction y using Quotient.inductionOn with | h y => ?_
    rw [← cls_mk x, ← cls_mk y, ← cls_fromBlocks_aux, ← cls_fromBlocks_aux, cls_eq_cls]
    exact MvN.fromBlocks_comm x.idem y.idem
  nsmul := nsmulRec

section clsLemmas

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem cls_fromBlocks {e : Matrix m m R} (he : e * e = e) {f : Matrix n n R} (hf : f * f = f) :
    cls (Matrix.fromBlocks e 0 0 f) (fromBlocks_idem he hf) = cls e he + cls f hf :=
  cls_fromBlocks_aux he hf

theorem cls_zero_matrix : cls (0 : Matrix m m R) (by simp) = 0 := by
  rw [zero_def, cls_eq_cls]
  exact ⟨0, 0, by simp, by simp⟩

theorem cls_eq_zero_iff {e : Matrix m m R} (he : e * e = e) : cls e he = 0 ↔ e = 0 := by
  constructor
  · intro h
    rw [zero_def, cls_eq_cls] at h
    exact h.eq_zero_of_isEmpty
  · rintro rfl
    exact cls_zero_matrix

/-- Splitting off the `none` block of a sigma type over `Option α`. -/
def sigmaOptionEquiv {α : Type*} (m' : Option α → Type*) :
    (Σ i, m' i) ≃ m' none ⊕ Σ a, m' (some a) where
  toFun
    | ⟨none, x⟩ => Sum.inl x
    | ⟨some a, x⟩ => Sum.inr ⟨a, x⟩
  invFun
    | Sum.inl x => ⟨none, x⟩
    | Sum.inr ⟨a, x⟩ => ⟨some a, x⟩
  left_inv := by rintro ⟨_ | a, x⟩ <;> rfl
  right_inv := by rintro (x | ⟨a, x⟩) <;> rfl

theorem blockDiagonal'_idem {o : Type*} [Fintype o] [DecidableEq o] {m' : o → Type*}
    [∀ i, Fintype (m' i)] (e : ∀ i, Matrix (m' i) (m' i) R) (he : ∀ i, e i * e i = e i) :
    Matrix.blockDiagonal' e * Matrix.blockDiagonal' e = Matrix.blockDiagonal' e := by
  rw [← Matrix.blockDiagonal'_mul]; simp [he]

private theorem cls_blockDiagonal'_aux (o : Type w) [Fintype o] : ∀ [DecidableEq o]
    (m' : o → Type v) [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)]
    (e : ∀ i, Matrix (m' i) (m' i) R) (he : ∀ i, e i * e i = e i),
    cls (Matrix.blockDiagonal' e) (blockDiagonal'_idem e he) = ∑ i, cls (e i) (he i) := by
  refine Fintype.induction_empty_option (P := fun o _ => ∀ [DecidableEq o]
    (m' : o → Type v) [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)]
    (e : ∀ i, Matrix (m' i) (m' i) R) (he : ∀ i, e i * e i = e i),
    cls (Matrix.blockDiagonal' e) (blockDiagonal'_idem e he) = ∑ i, cls (e i) (he i))
    ?_ ?_ ?_ o
  · intro α β _ σ ih _ m' _ _ e he
    let _inst : Fintype α := Fintype.ofEquiv β σ.symm
    classical
    have key := ih (fun a => m' (σ a)) (fun a => e (σ a)) (fun a => he (σ a))
    rw [Fintype.sum_equiv σ (fun a => cls (e (σ a)) (he (σ a))) (fun b => cls (e b) (he b))
      (fun _ => rfl)] at key
    rw [← key, ← cls_submatrix (blockDiagonal'_idem e he) (Equiv.sigmaCongrLeft σ)]
    apply cls_congr
    ext ⟨a, x⟩ ⟨b, y⟩
    by_cases h : a = b
    · subst h; simp [Matrix.blockDiagonal'_apply_eq]
    · simp [Matrix.blockDiagonal'_apply_ne _ _ _ h,
        Matrix.blockDiagonal'_apply_ne _ _ _ (σ.injective.ne h)]
  · intro _ m' _ _ e he
    rw [Finset.univ_eq_empty, Finset.sum_empty, ← cls_zero_matrix (m := Σ i, m' i)]
    apply cls_congr
    ext ⟨i, _⟩
    exact i.elim
  · intro α _ ih _ m' _ _ e he
    classical
    rw [Fintype.sum_option, ← ih (fun a => m' (some a)) (fun a => e (some a))
      (fun a => he (some a)), ← cls_fromBlocks (he none),
      ← cls_submatrix (blockDiagonal'_idem e he) (sigmaOptionEquiv m').symm]
    apply cls_congr
    ext (x | ⟨a, x⟩) (y | ⟨b, y⟩)
    · simp [sigmaOptionEquiv, Matrix.blockDiagonal'_apply_eq]
    · simp [sigmaOptionEquiv, Matrix.blockDiagonal'_apply_ne]
    · simp [sigmaOptionEquiv, Matrix.blockDiagonal'_apply_ne]
    · by_cases h : a = b
      · subst h; simp [sigmaOptionEquiv, Matrix.blockDiagonal'_apply_eq]
      · simp [sigmaOptionEquiv, Matrix.blockDiagonal'_apply_ne _ _ _ h,
          Matrix.blockDiagonal'_apply_ne e x y (Option.some_injective _ |>.ne h)]

theorem cls_blockDiagonal' {o : Type*} [Fintype o] [DecidableEq o] {m' : o → Type*}
    [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] (e : ∀ i, Matrix (m' i) (m' i) R)
    (he : ∀ i, e i * e i = e i) :
    cls (Matrix.blockDiagonal' e) (by rw [← Matrix.blockDiagonal'_mul]; simp [he]) =
      ∑ i, cls (e i) (he i) :=
  cls_blockDiagonal'_aux o m' e he

/-- `cls` of a block diagonal matrix with equal blocks. -/
theorem cls_blockDiagonal_const {o : Type*} [Fintype o] [DecidableEq o] {e : Matrix m m R}
    (he : e * e = e) :
    cls (Matrix.blockDiagonal fun _ : o => e)
      (by rw [← Matrix.blockDiagonal_mul]; simp [he]) = Fintype.card o • cls e he := by
  have h := cls_blockDiagonal' (fun _ : o => e) (fun _ => he)
  rw [Finset.sum_const, Finset.card_univ] at h
  rw [← h, ← cls_submatrix (blockDiagonal'_idem (fun _ : o => e) (fun _ => he))
    ((Equiv.prodComm m o).trans (Equiv.sigmaEquivProd o m).symm)]
  apply cls_congr
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases h : k = l
  · subst h; simp [Matrix.blockDiagonal_apply, Matrix.blockDiagonal'_apply_eq]
  · simp [Matrix.blockDiagonal_apply, Matrix.blockDiagonal'_apply_ne _ _ _ h, h]

end clsLemmas

/-- The class of `R` itself. -/
noncomputable def V.one (R : Type u) [Ring R] : V R := cls (1 : Matrix (Fin 1) (Fin 1) R) (by simp)

theorem cls_one {n : Type*} [Fintype n] [DecidableEq n] :
    cls (1 : Matrix n n R) (by simp) = Fintype.card n • V.one R := by
  have h := cls_blockDiagonal_const (o := n) (m := Fin 1) (R := R) (e := 1) (by simp)
  rw [← V.one] at h
  rw [← h, ← cls_submatrix (e := (1 : Matrix n n R)) (by simp)
    (Equiv.uniqueProd n (Fin 1))]
  apply cls_congr
  rw [Matrix.submatrix_one_equiv, ← Matrix.blockDiagonal_one]
  rfl

/-! ## Functoriality -/

section map

variable {T : Type v} [Ring T]

private theorem map_lift_cls (φ : R →+* T) {h : ∀ a b : Idem R, a ≈ b → _}
    {m : Type*} [Fintype m] [DecidableEq m] (e : Matrix m m R) (he : e * e = e) :
    Quotient.lift (fun e : Idem R => cls (e.e.map φ) (by rw [← Matrix.map_mul, e.idem])) h
      (cls e he) = cls (e.map φ) (by rw [← Matrix.map_mul, he]) := by
  change cls ((Matrix.reindex _ _ e).map φ) _ = _
  rw [← cls_reindex (e := e.map φ) (by rw [← Matrix.map_mul, he]) (Fintype.equivFin m)]
  exact cls_congr (by simp [Matrix.reindex_apply, Matrix.submatrix_map]) _ _

/-- `V` of a ring homomorphism: apply it entrywise. -/
noncomputable def V.map (φ : R →+* T) : V R →+ V T where
  toFun := Quotient.lift (fun e : Idem R => cls (e.e.map φ) (by rw [← Matrix.map_mul, e.idem]))
    (fun _ _ h => (cls_eq_cls _ _).2 (MvN.map φ h))
  map_zero' := by
    rw [zero_def, map_lift_cls, zero_def]
    exact cls_congr (Subsingleton.elim _ _) _ _
  map_add' x y := by
    induction x using Quotient.inductionOn with | h x => ?_
    induction y using Quotient.inductionOn with | h y => ?_
    rw [← cls_mk x, ← cls_mk y, ← cls_fromBlocks, map_lift_cls, map_lift_cls, map_lift_cls,
      ← cls_fromBlocks]
    exact cls_congr (by simp [Matrix.fromBlocks_map]) _ _

theorem V.map_cls (φ : R →+* T) {m : Type*} [Fintype m] [DecidableEq m] {e : Matrix m m R}
    (he : e * e = e) : V.map φ (cls e he) = cls (e.map φ) (by rw [← Matrix.map_mul, he]) :=
  map_lift_cls (h := fun _ _ h => (cls_eq_cls _ _).2 (MvN.map φ h)) φ e he

theorem V.map_one (φ : R →+* T) : V.map φ (V.one R) = V.one T := by
  rw [V.one, V.map_cls, V.one]
  exact cls_congr (Matrix.map_one φ φ.map_zero φ.map_one) _ _

theorem V.map_comp {W : Type w} [Ring W] (φ : R →+* T) (ψ : T →+* W) (x : V R) :
    V.map (ψ.comp φ) x = V.map ψ (V.map φ x) := by
  induction x using Quotient.inductionOn with | h x => ?_
  rw [← cls_mk x, V.map_cls, V.map_cls, V.map_cls]
  rfl

theorem V.map_id (x : V R) : V.map (RingHom.id R) x = x := by
  induction x using Quotient.inductionOn with | h x => ?_
  rw [← cls_mk x, V.map_cls]
  rfl

end map

/-! ## Matrix rings, products, fields -/

section matrix

theorem comp_mul' {I J K M : Type*} [Fintype J] [Fintype K]
    (a : Matrix I J (Matrix K K R)) (b : Matrix J M (Matrix K K R)) :
    Matrix.comp I M K K R (a * b) = Matrix.comp I J K K R a * Matrix.comp J M K K R b := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.comp_apply, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]

theorem comp_idem {I K : Type*} [Fintype I] [Fintype K] {e : Matrix I I (Matrix K K R)}
    (he : e * e = e) :
    Matrix.comp I I K K R e * Matrix.comp I I K K R e = Matrix.comp I I K K R e := by
  rw [← comp_mul', he]

omit [Ring R] in
theorem comp_injective {I J K L : Type*} : Function.Injective (Matrix.comp I J K L R) :=
  (Matrix.comp I J K L R).injective

variable (n : Type) [Fintype n] [DecidableEq n]

private theorem flat_lift_cls {h : ∀ a b : Idem (Matrix n n R), a ≈ b → _}
    {m : Type*} [Fintype m] [DecidableEq m] (e : Matrix m m (Matrix n n R)) (he : e * e = e) :
    Quotient.lift (fun e : Idem (Matrix n n R) => cls (Matrix.comp _ _ _ _ R e.e)
      (comp_idem e.idem)) h (cls e he) = cls (Matrix.comp _ _ _ _ R e) (comp_idem he) := by
  change cls (Matrix.comp _ _ _ _ R (Matrix.reindex _ _ e)) _ = _
  rw [← cls_reindex (comp_idem he) ((Fintype.equivFin m).prodCongr (Equiv.refl n))]
  exact cls_congr (by ext ⟨i, k⟩ ⟨j, l⟩; simp [Matrix.reindex_apply]) _ _

/-- Flattening a matrix of matrices, on `V`. -/
noncomputable def V.flat : V (Matrix n n R) →+ V R where
  toFun := Quotient.lift (fun e : Idem (Matrix n n R) => cls (Matrix.comp _ _ _ _ R e.e)
      (comp_idem e.idem))
    (fun _ _ ⟨a, b, hab, hba⟩ => (cls_eq_cls _ _).2 ⟨Matrix.comp _ _ _ _ R a,
      Matrix.comp _ _ _ _ R b, by rw [← comp_mul', hab], by rw [← comp_mul', hba]⟩)
  map_zero' := by
    rw [zero_def, flat_lift_cls, cls_eq_zero_iff]
    ext ⟨i, _⟩
    exact i.elim0
  map_add' x y := by
    induction x using Quotient.inductionOn with | h x => ?_
    induction y using Quotient.inductionOn with | h y => ?_
    rw [← cls_mk x, ← cls_mk y, ← cls_fromBlocks, flat_lift_cls, flat_lift_cls, flat_lift_cls,
      ← cls_fromBlocks, ← cls_submatrix (fromBlocks_idem (comp_idem x.idem) (comp_idem y.idem))
        (Equiv.sumProdDistrib (Fin x.n) (Fin y.n) n)]
    apply cls_congr
    ext ⟨i | i, k⟩ ⟨j | j, l⟩ <;> simp

theorem V.flat_cls {m : Type*} [Fintype m] [DecidableEq m] (e : Matrix m m (Matrix n n R))
    (he : e * e = e) : V.flat n (cls e he) = cls (Matrix.comp _ _ _ _ R e) (comp_idem he) :=
  flat_lift_cls (h := fun _ _ ⟨a, b, hab, hba⟩ => (cls_eq_cls _ _).2 ⟨Matrix.comp _ _ _ _ R a,
    Matrix.comp _ _ _ _ R b, by rw [← comp_mul', hab], by rw [← comp_mul', hba]⟩) n e he

theorem V.flat_injective : Function.Injective (V.flat (R := R) n) := by
  intro x y hxy
  induction x using Quotient.inductionOn with | h x => ?_
  induction y using Quotient.inductionOn with | h y => ?_
  rw [← cls_mk x, ← cls_mk y, V.flat_cls, V.flat_cls, cls_eq_cls] at hxy
  rw [← cls_mk x, ← cls_mk y, cls_eq_cls]
  obtain ⟨a, b, hab, hba⟩ := hxy
  refine ⟨(Matrix.comp _ _ _ _ R).symm a, (Matrix.comp _ _ _ _ R).symm b, ?_, ?_⟩
  · apply comp_injective; rw [comp_mul']; simpa using hab
  · apply comp_injective; rw [comp_mul']; simpa using hba

/-- `r ↦ r` placed at the corner `(i₀, i₀)`, as a non-unital ring homomorphism. -/
noncomputable def cornerHom (i₀ : n) : R →ₙ+* Matrix n n R where
  toFun r := Matrix.single i₀ i₀ r
  map_mul' r s := (Matrix.single_mul_single_same r i₀ i₀ i₀ s).symm
  map_zero' := Matrix.single_zero i₀ i₀
  map_add' r s := Matrix.single_add i₀ i₀ r s

theorem cornerHom_apply (i₀ : n) (r : R) : cornerHom n i₀ r = Matrix.single i₀ i₀ r := rfl

theorem map_mul_nonUnital {S : Type*} [Ring S] (f : R →ₙ+* S) {l m o : Type*} [Fintype m]
    (M : Matrix l m R) (N : Matrix m o R) : (M * N).map f = M.map f * N.map f := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

theorem V.flat_surjective [Nonempty n] : Function.Surjective (V.flat (R := R) n) := by
  intro x
  obtain ⟨p, e, he, rfl⟩ := cls_surjective x
  let i₀ : n := Classical.arbitrary n
  have hE : e.map (cornerHom n i₀) * e.map (cornerHom n i₀) = e.map (cornerHom n i₀) := by
    rw [← map_mul_nonUnital, he]
  refine ⟨cls _ hE, ?_⟩
  rw [V.flat_cls, cls_eq_cls]
  refine ⟨Matrix.of fun (i : Fin p × n) (j : Fin p) => if i.2 = i₀ then e i.1 j else 0,
    Matrix.of fun (i : Fin p) (j : Fin p × n) => if j.2 = i₀ then e i j.1 else 0, ?_, ?_⟩
  · ext ⟨i, k⟩ ⟨j, l⟩
    simp only [Matrix.mul_apply, Matrix.of_apply, ite_mul, zero_mul,
      mul_ite, mul_zero, Matrix.comp_apply, Matrix.map_apply, cornerHom_apply,
      Matrix.single_apply]
    by_cases hk : k = i₀ <;> by_cases hl : l = i₀ <;>
      simp [hk, hl, eq_comm (a := i₀), ← Matrix.mul_apply, he]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, ite_mul, zero_mul,
      mul_ite, mul_zero]
    simp [← Matrix.mul_apply, he]

/-- **`V(M_n(R)) ≅ V(R)`**, flattening a matrix of matrices; the class of `M_n(R)` goes to
`n • [R]`. -/
noncomputable def V.matrixEquiv [Nonempty n] : V (Matrix n n R) ≃+ V R :=
  AddEquiv.ofBijective (V.flat n) ⟨V.flat_injective n, V.flat_surjective n⟩

theorem V.matrixEquiv_apply [Nonempty n] (x : V (Matrix n n R)) :
    V.matrixEquiv n x = V.flat n x := rfl

theorem V.matrixEquiv_one [Nonempty n] :
    V.matrixEquiv (R := R) n (V.one _) = Fintype.card n • V.one R := by
  rw [V.matrixEquiv_apply, V.one, V.flat_cls]
  rw [cls_congr Matrix.comp_one _ (by simp), cls_one, Fintype.card_prod, Fintype.card_fin,
    one_mul]

/-- The class of a matrix whose entries are scalar matrices, under `V.matrixEquiv`. -/
theorem V.matrixEquiv_cls_scalar [Nonempty n]
    {m : Type} [Fintype m] [DecidableEq m] (e : Matrix m m R) (he : e * e = e) :
    V.matrixEquiv n (cls (e.map (Matrix.scalar n)) (by rw [← Matrix.map_mul, he])) =
      Fintype.card n • cls e he := by
  rw [V.matrixEquiv_apply, V.flat_cls, ← cls_blockDiagonal_const he]
  apply cls_congr
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [Matrix.blockDiagonal_apply, Matrix.diagonal_apply]

end matrix

/-- `V.matrixEquiv` is natural. -/
theorem V.matrixEquiv_map {T : Type v} [Ring T] (φ : R →+* T) (n : Type) [Fintype n]
    [DecidableEq n] [Nonempty n] (x : V (Matrix n n R)) :
    V.matrixEquiv n (V.map (RingHom.mapMatrix φ) x) = V.map φ (V.matrixEquiv n x) := by
  induction x using Quotient.inductionOn with | h x => ?_
  rw [← cls_mk x, V.matrixEquiv_apply, V.matrixEquiv_apply, V.map_cls, V.flat_cls, V.flat_cls,
    V.map_cls]
  rfl

/-- `V` of a ring isomorphism is an isomorphism. -/
noncomputable def V.congr {T : Type v} [Ring T] (φ : R ≃+* T) : V R ≃+ V T where
  toFun := V.map φ.toRingHom
  invFun := V.map φ.symm.toRingHom
  left_inv x := by rw [← V.map_comp]; simp [V.map_id]
  right_inv x := by rw [← V.map_comp]; simp [V.map_id]
  map_add' := map_add _

/-- **`V(k) = ℕ`** for a field (more generally a division ring), generated by `[k]`. -/
theorem V.field_nsmul_one (k : Type u) [DivisionRing k] (x : V k) : ∃ n : ℕ, x = n • V.one k := by
  obtain ⟨p, e, he, rfl⟩ := cls_surjective x
  let W := LinearMap.range (vecMulLinear e)
  let r := Module.finrank k W
  have htop : LinearMap.range (vecMulLinear (1 : Matrix (Fin r) (Fin r) k)) = ⊤ :=
    LinearMap.range_eq_top.2 fun v => ⟨v, by simp⟩
  let φ : W ≃ₗ[k] LinearMap.range (vecMulLinear (1 : Matrix (Fin r) (Fin r) k)) :=
    (Module.finBasis k W).equivFun.trans (LinearEquiv.ofTop _ htop).symm
  refine ⟨r, ?_⟩
  rw [← Fintype.card_fin r, ← cls_one, cls_eq_cls]
  exact mvN_of_rangeEquiv he (by simp) φ

theorem V.field_nsmul_one_injective (k : Type u) [DivisionRing k] :
    Function.Injective (fun n : ℕ => n • V.one k) := by
  intro p q hpq
  simp only at hpq
  rw [← Fintype.card_fin p, ← Fintype.card_fin q, ← cls_one, ← cls_one, cls_eq_cls] at hpq
  obtain ⟨a, b, hab, hba⟩ := hpq
  let φ : (Fin p → k) ≃ₗ[k] (Fin q → k) :=
    LinearEquiv.ofLinearMap (vecMulLinear a) (vecMulLinear b)
      (LinearMap.ext fun v => by simp [vecMul_vecMul, hba])
      (LinearMap.ext fun v => by simp [vecMul_vecMul, hab])
  simpa using φ.finrank_eq

section pi

variable {ι : Type} (A : ι → Type u) [∀ i, Ring (A i)]

/-- A family of matrices as a matrix over the product ring. -/
def piMat {m n : Type*} (E : ∀ i, Matrix m n (A i)) : Matrix m n (∀ i, A i) :=
  Matrix.of fun s t i => E i s t

theorem piMat_mul [Fintype ι] {l m n : Type*} [Fintype m] (E : ∀ i, Matrix l m (A i))
    (F : ∀ i, Matrix m n (A i)) : piMat A E * piMat A F = piMat A fun i => E i * F i := by
  ext s t i
  simp [piMat, Matrix.mul_apply, Finset.sum_apply]

theorem piMat_map {m n : Type*} (E : ∀ i, Matrix m n (A i)) (i : ι) :
    (piMat A E).map (Pi.evalRingHom A i) = E i := rfl

theorem piMat_eta {m n : Type*} (M : Matrix m n (∀ i, A i)) :
    piMat A (fun i => M.map (Pi.evalRingHom A i)) = M := rfl

variable [Fintype ι]

theorem V.pi_injective :
    Function.Injective (AddMonoidHom.pi fun i => V.map (Pi.evalRingHom A i)) := by
  intro x y hxy
  induction x using Quotient.inductionOn with | h x => ?_
  induction y using Quotient.inductionOn with | h y => ?_
  rw [← cls_mk x, ← cls_mk y] at hxy
  have h : ∀ i, MvN (x.e.map (Pi.evalRingHom A i)) (y.e.map (Pi.evalRingHom A i)) := by
    intro i
    have := congrFun hxy i
    change V.map (Pi.evalRingHom A i) (cls x.e x.idem) =
      V.map (Pi.evalRingHom A i) (cls y.e y.idem) at this
    rwa [V.map_cls, V.map_cls, cls_eq_cls] at this
  choose a b hab hba using h
  rw [← cls_mk x, ← cls_mk y, cls_eq_cls]
  refine ⟨piMat A a, piMat A b, ?_, ?_⟩
  · rw [piMat_mul]; simp_rw [hab]; rfl
  · rw [piMat_mul]; simp_rw [hba]; rfl

theorem V.pi_surjective :
    Function.Surjective (AddMonoidHom.pi fun i => V.map (Pi.evalRingHom A i)) := by
  intro x
  choose p e he hx using fun i => cls_surjective (x i)
  let N := ∑ i, p i
  have hp : ∀ i, p i + (N - p i) = N := fun i =>
    Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  let σ : ∀ i, Fin (p i) ⊕ Fin (N - p i) ≃ Fin N := fun i =>
    finSumFinEquiv.trans (finCongr (hp i))
  let E : ∀ i, Matrix (Fin N) (Fin N) (A i) := fun i =>
    Matrix.reindex (σ i) (σ i) (Matrix.fromBlocks (e i) 0 0 0)
  have hE : ∀ i, E i * E i = E i := fun i => reindex_idem (fromBlocks_idem (he i) (by simp)) _
  have hEE : piMat A E * piMat A E = piMat A E := by rw [piMat_mul]; simp_rw [hE]
  refine ⟨cls (piMat A E) hEE, funext fun i => ?_⟩
  change V.map (Pi.evalRingHom A i) (cls (piMat A E) hEE) = x i
  rw [V.map_cls, ← hx i]
  rw [cls_congr (piMat_map A E i) _ (hE i), cls_reindex (fromBlocks_idem (he i) (by simp)),
    cls_eq_cls]
  exact MvN.fromBlocks_zero (he i)

end pi

/-- `V` of a finite product is the product. -/
noncomputable def V.piEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → Type u)
    [∀ i, Ring (A i)] : V (∀ i, A i) ≃+ ∀ i, V (A i) :=
  AddEquiv.ofBijective (AddMonoidHom.pi fun i => V.map (Pi.evalRingHom A i))
    ⟨V.pi_injective A, V.pi_surjective A⟩

theorem V.piEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → Type u)
    [∀ i, Ring (A i)] (x : V (∀ i, A i)) (i : ι) :
    V.piEquiv A x i = V.map (Pi.evalRingHom A i) x := rfl

end Bergman

namespace Bergman

theorem one_sub_idem {R : Type u} [Ring R] {m : Type*} [Fintype m] [DecidableEq m]
    {e : Matrix m m R} (he : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]

end Bergman
