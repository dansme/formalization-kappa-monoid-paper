/-
**Corner rings and matrix units: the tools for `Bergman/Morita.lean`.**

* The corner ring `e T e` of an idempotent `e` (Mathlib's `IsIdempotentElem.Corner`) is a
  `k`-algebra when `T` is (`Corner.instAlgebra`).
* `idemFamilyHom`: `k^ι → A` from a complete family of orthogonal idempotents;
  `matUnitsProdHom`: `M_ι(k) × k → A` from a (not necessarily full) system of matrix units.
* **Matrix units (the matrix-units form of Morita equivalence).**  A `k`-algebra map
  `F : M_N(R) → T` gives matrix units `u_{ij} = F(e_{ij})` in `T`; with `e = u_{cc}`, every
  `ψ : S → e T e` extends to `moritaHom F c ψ : M_N(S) → T`, `X ↦ ∑ u_{ic} ψ(X_{ij}) u_{cj}`, and an
  algebra map out of `M_N(S)` is determined by its values on the matrix units and on `S e_{cc}`
  (`ext_of_single`).
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RingTheory.Idempotents

namespace Bergman

open Matrix

/-! ## The corner ring `e T e` as a `k`-algebra -/

section Corner

variable {k : Type*} [CommSemiring k] {T : Type*} [Ring T] [Algebra k T] {e : T}

/-- An element of the corner ring `e T e`, from `x` with `e x = x = x e`. -/
def cornerMk (he : IsIdempotentElem e) (x : T) (h₁ : e * x = x) (h₂ : x * e = x) : he.Corner :=
  ⟨x, (Subsemigroup.mem_corner_iff he).2 ⟨h₁, h₂⟩⟩

variable (he : IsIdempotentElem e)

@[simp] theorem cornerMk_val (x : T) (h₁ : e * x = x) (h₂ : x * e = x) :
    (cornerMk he x h₁ h₂).1 = x := rfl

theorem corner_mul_left (x : he.Corner) : e * x.1 = x.1 :=
  ((Subsemigroup.mem_corner_iff he).1 x.2).1

theorem corner_mul_right (x : he.Corner) : x.1 * e = x.1 :=
  ((Subsemigroup.mem_corner_iff he).1 x.2).2

theorem corner_ext {x y : he.Corner} (h : x.1 = y.1) : x = y := Subtype.ext h

@[simp] theorem corner_val_one : (1 : he.Corner).1 = e := rfl
@[simp] theorem corner_val_zero : (0 : he.Corner).1 = 0 := rfl
@[simp] theorem corner_val_mul (x y : he.Corner) : (x * y).1 = x.1 * y.1 := rfl
@[simp] theorem corner_val_add (x y : he.Corner) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem corner_val_neg (x : he.Corner) : (-x).1 = -x.1 := rfl
@[simp] theorem corner_val_sub (x y : he.Corner) : (x - y).1 = x.1 - y.1 := rfl

@[simp] theorem corner_val_ite (p : Prop) [Decidable p] (x : he.Corner) :
    (if p then x else 0).1 = if p then x.1 else 0 := by
  split_ifs <;> rfl

/-- The inclusion `e T e → T`, as an additive map. -/
def cornerVal : he.Corner →+ T where
  toFun x := x.1
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem corner_val_sum {ι : Type*} (s : Finset ι) (f : ι → he.Corner) :
    (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 :=
  map_sum (cornerVal he) f s

/-- `k → e T e`, `c ↦ c e`. -/
def cornerAlgebraMap : k →+* he.Corner where
  toFun c := cornerMk he (algebraMap k T c * e)
    (by rw [← mul_assoc, ← Algebra.commutes, mul_assoc, he.eq]) (by rw [mul_assoc, he.eq])
  map_one' := corner_ext he (by simp)
  map_mul' c d := corner_ext he (by
    simp only [cornerMk_val, corner_val_mul, map_mul]
    rw [mul_assoc (algebraMap k T c) e, ← mul_assoc e, ← Algebra.commutes d e, mul_assoc,
      mul_assoc (algebraMap k T d) e e, he.eq])
  map_zero' := corner_ext he (by simp)
  map_add' c d := corner_ext he (by simp [add_mul])

/-- The corner ring `e T e` is a `k`-algebra, with `algebraMap c = c e`. -/
instance Corner.instAlgebra : Algebra k he.Corner :=
  (cornerAlgebraMap he).toAlgebra' fun c x => corner_ext he (by
    change algebraMap k T c * e * x.1 = x.1 * (algebraMap k T c * e)
    rw [mul_assoc, corner_mul_left, ← mul_assoc, ← Algebra.commutes, mul_assoc,
      corner_mul_right])

@[simp] theorem corner_val_algebraMap (c : k) :
    (algebraMap k he.Corner c).1 = algebraMap k T c * e := rfl

end Corner

/-! ## Algebra maps out of `k^ι` and out of `M_ι(k) × k` -/

section Families

variable {k : Type*} [CommSemiring k] {A : Type*} [Ring A] [Algebra k A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `k^ι → A`, `v ↦ ∑ v_i p_i`, for a complete family `p` of orthogonal idempotents. -/
def idemFamilyHom (p : ι → A) (hp : ∀ i j, p i * p j = if i = j then p i else 0)
    (hsum : ∑ i, p i = 1) : (ι → k) →ₐ[k] A where
  toFun v := ∑ i, v i • p i
  map_one' := by simp [hsum]
  map_mul' v w := by
    simp only [Pi.mul_apply, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, hp, smul_ite,
      smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  map_zero' := by simp
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  commutes' c := by
    simp [Algebra.algebraMap_eq_smul_one, ← Finset.smul_sum, hsum]

theorem idemFamilyHom_apply (p : ι → A) (hp : ∀ i j, p i * p j = if i = j then p i else 0)
    (hsum : ∑ i, p i = 1) (v : ι → k) :
    idemFamilyHom (k := k) p hp hsum v = ∑ i, v i • p i := rfl

@[simp] theorem idemFamilyHom_single (p : ι → A)
    (hp : ∀ i j, p i * p j = if i = j then p i else 0) (hsum : ∑ i, p i = 1) (i : ι) :
    idemFamilyHom (k := k) p hp hsum (Pi.single i 1) = p i := by
  simp [idemFamilyHom_apply, Pi.single_apply]

/-- Algebra maps out of `k^ι` agree once they agree on the idempotents `Pi.single i 1`. -/
theorem algHom_pi_ext {f g : (ι → k) →ₐ[k] A}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  ext v
  have hv : v = ∑ i, v i • (Pi.single i 1 : ι → k) := by
    ext j; simp [Pi.single_apply]
  rw [hv]; simp [map_sum, map_smul, h]

/-- There is only one algebra map out of `k^Unit = k`. -/
theorem algHom_unit_ext (f g : (Unit → k) →ₐ[k] A) : f = g := by
  ext v
  have hv : v = algebraMap k (Unit → k) (v ()) := funext fun _ => rfl
  rw [hv, f.commutes, g.commutes]

/-- `M_ι(k) × k → A`, `(x, c) ↦ ∑ x_{ab} v_{ab} + c (1 - ∑ v_{aa})`, for a system `v` of matrix
units (not necessarily summing to `1`). -/
def matUnitsProdHom (v : ι → ι → A)
    (hv : ∀ a b c d, v a b * v c d = if b = c then v a d else 0) :
    Matrix ι ι k × k →ₐ[k] A :=
  have hPv : ∀ a b, (∑ i, v i i) * v a b = v a b := fun a b => by
    simp [Finset.sum_mul, hv]
  have hvP : ∀ a b, v a b * (∑ i, v i i) = v a b := fun a b => by
    simp [Finset.mul_sum, hv]
  have hQv : ∀ a b, (1 - ∑ i, v i i) * v a b = 0 := fun a b => by
    rw [sub_mul, hPv, one_mul, sub_self]
  have hvQ : ∀ a b, v a b * (1 - ∑ i, v i i) = 0 := fun a b => by
    rw [mul_sub, hvP, mul_one, sub_self]
  have hQQ : (1 - ∑ i, v i i) * (1 - ∑ i, v i i) = 1 - ∑ i, v i i := by
    rw [mul_sub, mul_one, Finset.mul_sum]; simp [hQv]
  { toFun := fun x => ∑ a, ∑ b, x.1 a b • v a b + x.2 • (1 - ∑ i, v i i)
    map_one' := by
      simp [Prod.fst_one, Prod.snd_one, one_apply, ite_smul, Finset.sum_ite_eq]
    map_mul' := fun x y => by
      have hXY : (∑ a, ∑ b, x.1 a b • v a b) * (∑ a, ∑ b, y.1 a b • v a b) =
          ∑ a, ∑ b, (x.1 * y.1) a b • v a b := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum, smul_mul_smul_comm, hv, smul_ite, smul_zero,
          mul_apply, Finset.sum_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact Finset.sum_comm
      have hXQ : (∑ a, ∑ b, x.1 a b • v a b) * (y.2 • (1 - ∑ i, v i i)) = 0 := by
        simp [Finset.sum_mul, hvQ]
      have hQY : (x.2 • (1 - ∑ i, v i i)) * (∑ a, ∑ b, y.1 a b • v a b) = 0 := by
        simp [Finset.mul_sum, hQv]
      rw [add_mul, mul_add, mul_add, hXY, hXQ, hQY, smul_mul_smul_comm, hQQ, Prod.fst_mul,
        Prod.snd_mul]
      abel
    map_zero' := by simp
    map_add' := fun x y => by
      simp only [Prod.fst_add, Prod.snd_add, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
      abel
    commutes' := fun c => by
      simp only [Prod.algebraMap_apply, algebraMap_matrix_apply, Algebra.algebraMap_self,
        RingHom.id_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Algebra.algebraMap_eq_smul_one, ← Finset.smul_sum, ← smul_add]
      rw [add_sub_cancel] }

theorem matUnitsProdHom_apply (v : ι → ι → A)
    (hv : ∀ a b c d, v a b * v c d = if b = c then v a d else 0) (x : Matrix ι ι k × k) :
    matUnitsProdHom v hv x = ∑ a, ∑ b, x.1 a b • v a b + x.2 • (1 - ∑ i, v i i) := rfl

@[simp] theorem matUnitsProdHom_single (v : ι → ι → A)
    (hv : ∀ a b c d, v a b * v c d = if b = c then v a d else 0) (a b : ι) :
    matUnitsProdHom v hv (single a b (1 : k), 0) = v a b := by
  simp [matUnitsProdHom_apply, single_apply, ite_smul, ite_and, Finset.sum_ite_eq]

@[simp] theorem matUnitsProdHom_snd (v : ι → ι → A)
    (hv : ∀ a b c d, v a b * v c d = if b = c then v a d else 0) :
    matUnitsProdHom v hv ((0 : Matrix ι ι k), (1 : k)) = 1 - ∑ i, v i i := by
  simp [matUnitsProdHom_apply]

/-- Algebra maps out of `M_ι(k) × k` agree once they agree on the `(e_{ab}, 0)` and on `(0, 1)`. -/
theorem algHom_matrixProd_ext {f g : Matrix ι ι k × k →ₐ[k] A}
    (h : ∀ a b, f (single a b 1, 0) = g (single a b 1, 0)) (h' : f (0, 1) = g (0, 1)) :
    f = g := by
  ext x
  have hx : x = ∑ a, ∑ b, x.1 a b • ((single a b 1 : Matrix ι ι k), (0 : k)) +
      x.2 • ((0 : Matrix ι ι k), (1 : k)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_single, smul_eq_mul, mul_one,
        smul_zero, add_zero]
      exact matrix_eq_sum_single x.1
    · simp [Prod.snd_sum]
  rw [hx]; simp only [map_add, map_sum, map_smul, h, h']

end Families

/-! ## Matrix units and the corner at `e_{cc}` -/

section MatrixUnits

variable {k : Type*} [CommSemiring k] {N : Type*} [Fintype N] [DecidableEq N]
  {R S T : Type*} [Ring R] [Ring S] [Ring T] [Algebra k R] [Algebra k S] [Algebra k T]

/-- Algebra maps out of `M_N(R)` agree once they agree on all `r e_{ab}`. -/
theorem algHom_matrix_ext {f g : Matrix N N R →ₐ[k] T}
    (h : ∀ a b r, f (single a b r) = g (single a b r)) : f = g := by
  ext X
  rw [matrix_eq_sum_single X]; simp [map_sum, h]

variable (F : Matrix N N R →ₐ[k] T)

theorem map_single_mul_single (a b c d : N) :
    F (single a b 1) * F (single c d 1) = if b = c then F (single a d 1) else 0 := by
  rw [← map_mul]
  split_ifs with h
  · subst h; rw [single_mul_single_same, one_mul]
  · rw [single_mul_single_of_ne (h := h), map_zero]

theorem map_single_mul_single_same (a b d : N) (r s : R) :
    F (single a b r) * F (single b d s) = F (single a d (r * s)) := by
  rw [← map_mul, single_mul_single_same]

theorem map_single_mul_single_one (a b d : N) :
    F (single a b 1) * F (single b d 1) = F (single a d 1) := by
  rw [map_single_mul_single_same, one_mul]

theorem isIdempotentElem_single (c : N) : IsIdempotentElem (F (single c c 1)) := by
  rw [IsIdempotentElem, map_single_mul_single_same, mul_one]

variable (c : N) {e : T} (he : IsIdempotentElem e) (hFe : F (single c c 1) = e)

/-- `R → e T e`, `r ↦ F(r e_{cc})`, for `e = F(e_{cc})`. -/
def cornerMap : R →ₐ[k] he.Corner where
  toFun r := cornerMk he (F (single c c r))
    (by rw [← hFe, map_single_mul_single_same, one_mul])
    (by rw [← hFe, map_single_mul_single_same, mul_one])
  map_one' := corner_ext he hFe
  map_mul' r s := corner_ext he (by
    simp only [cornerMk_val, corner_val_mul]; rw [map_single_mul_single_same])
  map_zero' := corner_ext he (by simp)
  map_add' r s := corner_ext he (by simp [single_add])
  commutes' a := corner_ext he (by
    simp only [cornerMk_val, corner_val_algebraMap]
    rw [← hFe, Algebra.algebraMap_eq_smul_one a, ← smul_single, map_smul, Algebra.smul_def])

@[simp] theorem cornerMap_val (r : R) : (cornerMap F c he hFe r).1 = F (single c c r) := rfl

/-- The element `u_{ca} t u_{bc}` of the corner `e T e`, `u_{ij} = F(e_{ij})`. -/
def cornerEnt (t : T) (a b : N) : he.Corner :=
  cornerMk he (F (single c a 1) * t * F (single b c 1))
    (by rw [← hFe, ← mul_assoc, ← mul_assoc, map_single_mul_single_same, one_mul])
    (by rw [← hFe, mul_assoc, map_single_mul_single_same, mul_one])

@[simp] theorem cornerEnt_val (t : T) (a b : N) :
    (cornerEnt F c he hFe t a b).1 = F (single c a 1) * t * F (single b c 1) := rfl

theorem cornerMap_apply_eq (Y : Matrix N N R) (a b : N) :
    cornerMap F c he hFe (Y a b) = cornerEnt F c he hFe (F Y) a b :=
  corner_ext he (by
    rw [cornerMap_val, cornerEnt_val, ← map_mul, ← map_mul, single_mul_mul_single, one_mul,
      mul_one])

theorem cornerEnt_mul (s t : T) (a l l' b : N) :
    cornerEnt F c he hFe s a l * cornerEnt F c he hFe t l' b =
      cornerEnt F c he hFe (s * F (single l l' 1) * t) a b :=
  corner_ext he (by
    have h := map_single_mul_single_same F l c l' (1 : R) 1
    rw [one_mul] at h
    simp only [corner_val_mul, cornerEnt_val]
    rw [← h]; simp only [mul_assoc])

theorem sum_cornerEnt_mul {p : Type*} [Fintype p] (f : p → N) (s t : T) (a b : N) :
    ∑ x, cornerEnt F c he hFe s a (f x) * cornerEnt F c he hFe t (f x) b =
      cornerEnt F c he hFe (s * F (∑ x, single (f x) (f x) (1 : R)) * t) a b :=
  corner_ext he (by
    simp only [cornerEnt_mul, corner_val_sum, cornerEnt_val, map_sum, Finset.mul_sum,
      Finset.sum_mul])

theorem sum_units_cornerEnt {p q : Type*} [Fintype p] [Fintype q] (f : p → N) (g : q → N)
    (t : T) :
    ∑ x, ∑ y, F (single (f x) c 1) * (cornerEnt F c he hFe t (f x) (g y)).1 *
        F (single c (g y) 1) =
      F (∑ x, single (f x) (f x) (1 : R)) * t * F (∑ y, single (g y) (g y) (1 : R)) := by
  simp only [cornerEnt_val, map_sum, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← map_single_mul_single_one F (f x) c (f x), ← map_single_mul_single_one F (g y) c (g y)]
  simp only [mul_assoc]

/-- `M_N(e T e) → T`, `Z ↦ ∑ u_{ic} Z_{ij} u_{cj}` with `u_{ij} = F(e_{ij})`, `e = u_{cc}`. -/
def unitsHom : Matrix N N he.Corner →ₐ[k] T :=
  have hue : ∀ i j, F (single i c 1) * e * F (single c j 1) = F (single i j 1) := fun i j => by
    rw [← hFe, map_single_mul_single_same, map_single_mul_single_same, one_mul, one_mul]
  have hkey : ∀ (x y : he.Corner) (i l l' j : N),
      F (single i c 1) * x.1 * F (single c l 1) * (F (single l' c 1) * y.1 * F (single c j 1)) =
        if l = l' then F (single i c 1) * (x * y).1 * F (single c j 1) else 0 := by
    intro x y i l l' j
    have h : F (single c l 1) * F (single l' c 1) = if l = l' then e else 0 := by
      rw [map_single_mul_single, hFe]
    calc _ = F (single i c 1) * x.1 * (F (single c l 1) * F (single l' c 1)) * y.1 *
          F (single c j 1) := by simp only [mul_assoc]
      _ = _ := by
        rw [h]; split_ifs
        · rw [mul_assoc _ x.1 e, corner_mul_right, corner_val_mul, mul_assoc _ x.1]
        · simp
  have hcomm : ∀ a : k, (∑ i, ∑ j, F (single i c 1) *
      (algebraMap k (Matrix N N he.Corner) a i j).1 * F (single c j 1)) = algebraMap k T a := by
    intro a
    simp only [algebraMap_matrix_apply, corner_val_ite, corner_val_algebraMap, mul_ite,
      ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h : ∀ i, F (single i c 1) * (algebraMap k T a * e) * F (single c i 1) =
        algebraMap k T a * F (single i i 1) := fun i => by
      rw [← mul_assoc, ← Algebra.commutes, mul_assoc, mul_assoc, ← mul_assoc _ e, hue]
    rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.mul_sum, ← map_sum, sum_single_one, map_one,
      mul_one]
  { toFun := fun Z => ∑ i, ∑ j, F (single i c 1) * (Z i j).1 * F (single c j 1)
    map_one' := by simpa using hcomm 1
    map_mul' := fun X Y => by
      show ∑ i, ∑ j, F (single i c 1) * ((X * Y) i j).1 * F (single c j 1) =
        (∑ i, ∑ l, F (single i c 1) * (X i l).1 * F (single c l 1)) *
          (∑ l', ∑ j, F (single l' c 1) * (Y l' j).1 * F (single c j 1))
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum, hkey, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp only [mul_apply, corner_val_sum, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm
    map_zero' := by simp
    map_add' := fun X Y => by
      simp [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    commutes' := hcomm }

theorem unitsHom_apply (Z : Matrix N N he.Corner) :
    unitsHom F c he hFe Z = ∑ i, ∑ j, F (single i c 1) * (Z i j).1 * F (single c j 1) := rfl

@[simp] theorem unitsHom_single (a b : N) (x : he.Corner) :
    unitsHom F c he hFe (single a b x) = F (single a c 1) * x.1 * F (single c b 1) := by
  simp [unitsHom_apply, single_apply, ite_and, Finset.sum_ite_eq]

variable (ψ : S →ₐ[k] he.Corner)

/-- `M_N(S) → T`, `X ↦ ∑ u_{ic} ψ(X_{ij}) u_{cj}`: the extension of `ψ : S → e T e` along the
matrix units `u_{ij} = F(e_{ij})`. -/
noncomputable def moritaHom : Matrix N N S →ₐ[k] T :=
  (unitsHom F c he hFe).comp ψ.mapMatrix

theorem moritaHom_apply (X : Matrix N N S) :
    moritaHom F c he hFe ψ X = ∑ i, ∑ j, F (single i c 1) * (ψ (X i j)).1 * F (single c j 1) :=
  rfl

@[simp] theorem moritaHom_single (a b : N) (s : S) :
    moritaHom F c he hFe ψ (single a b s) = F (single a c 1) * (ψ s).1 * F (single c b 1) := by
  simp [moritaHom, AlgHom.mapMatrix_apply, Matrix.map_single]

/-- If `ψ` restricts to `cornerMap F` on `R`, then `moritaHom F c ψ` restricts to `F` on
`M_N(R)`. -/
theorem moritaHom_comp_mapMatrix (j : R →ₐ[k] S) (hψ : ψ.comp j = cornerMap F c he hFe) :
    (moritaHom F c he hFe ψ).comp j.mapMatrix = F := by
  refine algHom_matrix_ext fun a b r => ?_
  rw [AlgHom.comp_apply, AlgHom.mapMatrix_apply, Matrix.map_single,
    moritaHom_single, ← AlgHom.comp_apply ψ j, hψ, cornerMap_val,
    map_single_mul_single_same, map_single_mul_single_same, one_mul, mul_one]

/-- `moritaHom` sends the matrix `(of fun a b => u_{ca} t u_{bc})`-image of `t` back to
`F(1) t F(1) = t`. -/
theorem moritaHom_of_cornerEnt (X : Matrix N N S) (t : T)
    (hX : X.map ψ = Matrix.of fun a b => cornerEnt F c he hFe t a b) :
    moritaHom F c he hFe ψ X = t := by
  have h := sum_units_cornerEnt F c he hFe id id t
  simp only [id, sum_single_one, map_one, one_mul, mul_one] at h
  rw [← h, moritaHom_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show ψ (X a b) = X.map ψ a b from rfl, hX, of_apply]

end MatrixUnits

section Ext

variable {k : Type*} [CommSemiring k] {N : Type*} [Fintype N] [DecidableEq N]
  {S T : Type*} [Ring S] [Ring T] [Algebra k S] [Algebra k T]

/-- Algebra maps out of `M_N(S)` agree once they agree on the matrix units and on `S e_{cc}`. -/
theorem ext_of_single {g g' : Matrix N N S →ₐ[k] T} (c : N)
    (h1 : ∀ a b, g (single a b 1) = g' (single a b 1))
    (h2 : ∀ s, g (single c c s) = g' (single c c s)) : g = g' := by
  refine algHom_matrix_ext fun a b s => ?_
  have hs : single a b s = single a c (1 : S) * single c c s * single c b 1 := by
    rw [single_mul_single_same, single_mul_single_same, one_mul, mul_one]
  rw [hs, map_mul, map_mul, map_mul, map_mul, h1, h1, h2]

/-- The corner maps of two algebra maps out of `M_N(S)` that agree on the matrix units. -/
theorem ext_of_cornerMap {g g' : Matrix N N S →ₐ[k] T} (c : N)
    (h1 : ∀ a b, g (single a b 1) = g' (single a b 1))
    (h2 : cornerMap g c (isIdempotentElem_single g c) rfl =
      cornerMap g' c (isIdempotentElem_single g c) (h1 c c).symm) : g = g' :=
  ext_of_single c h1 fun s => congrArg (fun φ : S →ₐ[k] _ => (φ s).1) h2

end Ext

end Bergman
