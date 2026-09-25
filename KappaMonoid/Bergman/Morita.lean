/-
**Universal idempotents and universal isomorphisms, and their matrix rings as coproducts.**

`IsIdemExt j n E` says `S` is `R` with a universal idempotent `n × n` matrix `E` adjoined;
`IsIsoExt j D D' A B` says `S` is `R` with a universal isomorphism `R^{1×m} D ≅ R^{1×m'} D'`
adjoined (`A`, `B` mutually inverse, in the corners).  Both are universal-property predicates.

**Bergman, *Coproducts and some universal ring constructions* (1974), §§3–5**: after passing to
a matrix ring in which the modules concerned become cyclic, these constructions are coproducts
over a product of copies of `k`:

* `M_n(R⟨E⟩)  ≅ M_n(R) ⊔_k (k × k)`;
* `M_N(R⟨D ≅ D'⟩) ≅ M_N(R) ⊔_{k³} (M₂(k) × k)`, with `N = m + m' + 1` and `k³` the idempotents
  `diag(D,0,0)`, `diag(0,D',0)`, `diag(1-D,1-D',1)`.

Here the matrix rings are shown to have the universal property `IsCoprod` directly, via the
matrix units of `M_N(k)` and the corner ring at `e₁₁`.
-/
import KappaMonoid.Bergman.IsCoprod
import KappaMonoid.Bergman.Corner

universe u

namespace Bergman

open Matrix

variable {k : Type u} [Field k] {R S : Type u} [Ring R] [Ring S] [Algebra k R] [Algebra k S]

/-- `S` is `R` with a universal idempotent `n × n` matrix `E`. -/
structure IsIdemExt (j : R →ₐ[k] S) (n : ℕ) (E : Matrix (Fin n) (Fin n) S) : Prop where
  idem : E * E = E
  lift : ∀ (T : Type u) [Ring T] [Algebra k T] (φ : R →ₐ[k] T) (E' : Matrix (Fin n) (Fin n) T),
    E' * E' = E' → ∃ ψ : S →ₐ[k] T, ψ.comp j = φ ∧ E.map ψ = E'
  ext : ∀ (T : Type u) [Ring T] [Algebra k T] (ψ ψ' : S →ₐ[k] T), ψ.comp j = ψ'.comp j →
    E.map ψ = E.map ψ' → ψ = ψ'

/-- `S` is `R` with a universal isomorphism `R^{1×m} D ≅ R^{1×m'} D'`, given by `A` and its
inverse `B`. -/
structure IsIsoExt {m m' : Type} [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m']
    (j : R →ₐ[k] S) (D : Matrix m m R) (D' : Matrix m' m' R)
    (A : Matrix m m' S) (B : Matrix m' m S) : Prop where
  cornerA : D.map j * A * D'.map j = A
  cornerB : D'.map j * B * D.map j = B
  mulAB : A * B = D.map j
  mulBA : B * A = D'.map j
  lift : ∀ (T : Type u) [Ring T] [Algebra k T] (φ : R →ₐ[k] T) (A' : Matrix m m' T)
    (B' : Matrix m' m T), D.map φ * A' * D'.map φ = A' → D'.map φ * B' * D.map φ = B' →
    A' * B' = D.map φ → B' * A' = D'.map φ →
    ∃ ψ : S →ₐ[k] T, ψ.comp j = φ ∧ A.map ψ = A' ∧ B.map ψ = B'
  ext : ∀ (T : Type u) [Ring T] [Algebra k T] (ψ ψ' : S →ₐ[k] T), ψ.comp j = ψ'.comp j →
    A.map ψ = A.map ψ' → B.map ψ = B.map ψ' → ψ = ψ'

/-! ## Two-member families -/

/-- The family `true ↦ A`, `false ↦ B`. -/
def pair (A B : Type u) : Bool → Type u
  | true => A
  | false => B

instance pair.instRing (A B : Type u) [Ring A] [Ring B] : ∀ b, Ring (pair A B b)
  | true => ‹Ring A›
  | false => ‹Ring B›

instance pair.instAlgebra (A B : Type u) [Ring A] [Ring B] [Algebra k A] [Algebra k B] :
    ∀ b, Algebra k (pair A B b)
  | true => ‹Algebra k A›
  | false => ‹Algebra k B›

/-- A family of algebra maps out of `pair A B`. -/
def pairHom {A B T : Type u} [Ring A] [Ring B] [Ring T] [Algebra k A] [Algebra k B]
    [Algebra k T] (f : A →ₐ[k] T) (g : B →ₐ[k] T) : ∀ b, pair A B b →ₐ[k] T
  | true => f
  | false => g

/-- A family of algebra maps into `pair A B`. -/
def pairSigma {ι : Type} {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (f : (ι → k) →ₐ[k] A) (g : (ι → k) →ₐ[k] B) : ∀ b, (ι → k) →ₐ[k] pair A B b
  | true => f
  | false => g

/-! ## Helpers: two and three orthogonal idempotents, blocks of the corner entries -/

section Helpers

variable {k : Type*} [CommSemiring k] {A : Type*} [Ring A] [Algebra k A]

/-- `k² → A`, `v ↦ v₀ p + v₁ (1 - p)`, for an idempotent `p`. -/
def idem2Hom (p : A) (hp : p * p = p) : (Fin 2 → k) →ₐ[k] A :=
  idemFamilyHom (k := k) ![p, 1 - p]
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [mul_sub, sub_mul, hp])
    (by simp [Fin.sum_univ_two])

theorem idem2Hom_apply (p : A) (hp : p * p = p) (v : Fin 2 → k) :
    idem2Hom p hp v = v 0 • p + v 1 • (1 - p) := by
  simp [idem2Hom, idemFamilyHom_apply, Fin.sum_univ_two]

/-- `k³ → A`, from orthogonal idempotents `p`, `q` and the complement `1 - p - q`. -/
def idem3Hom (p q : A) (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0) :
    (Fin 3 → k) →ₐ[k] A :=
  idemFamilyHom (k := k) ![p, q, 1 - p - q]
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [mul_sub, sub_mul, hp, hq, hpq, hqp])
    (by simp [Fin.sum_univ_three])

theorem idem3Hom_single (p q : A) (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0)
    (hqp : q * p = 0) (i : Fin 3) :
    idem3Hom (k := k) p q hp hq hpq hqp (Pi.single i 1) = ![p, q, 1 - p - q] i :=
  idemFamilyHom_single _ _ _ i

end Helpers

section CornerBlk

variable {k : Type*} [CommSemiring k] {N : Type*} [Fintype N] [DecidableEq N]
  {R T : Type*} [Ring R] [Ring T] [Algebra k R] [Algebra k T]
  (F : Matrix N N R →ₐ[k] T) (c : N) {e : T} (he : IsIdempotentElem e)
  (hFe : F (single c c 1) = e)

/-- The block `(u_{c f(a)} t u_{g(b) c})_{a b}` of corner entries of `t`. -/
def cornerBlk {p q : Type*} (t : T) (f : p → N) (g : q → N) : Matrix p q he.Corner :=
  of fun a b => cornerEnt F c he hFe t (f a) (g b)

@[simp] theorem cornerBlk_apply {p q : Type*} (t : T) (f : p → N) (g : q → N) (a : p) (b : q) :
    cornerBlk F c he hFe t f g a b = cornerEnt F c he hFe t (f a) (g b) := rfl

theorem cornerBlk_mul {p q r : Type*} [Fintype q] (s t : T) (f : p → N) (g : q → N)
    (h : r → N) :
    cornerBlk F c he hFe s f g * cornerBlk F c he hFe t g h =
      cornerBlk F c he hFe (s * F (∑ x, single (g x) (g x) (1 : R)) * t) f h := by
  ext a b
  simp only [mul_apply, cornerBlk_apply]
  exact sum_cornerEnt_mul F c he hFe g s t (f a) (h b)

theorem cornerBlk_mul_id (s t : T) :
    cornerBlk F c he hFe s id id * cornerBlk F c he hFe t id id =
      cornerBlk F c he hFe (s * t) id id := by
  rw [cornerBlk_mul]; simp [sum_single_one]

theorem cornerBlk_map {p q : Type*} (Y : Matrix N N R) (f : p → N) (g : q → N) :
    cornerBlk F c he hFe (F Y) f g = (Y.submatrix f g).map (cornerMap F c he hFe) := by
  ext a b
  simp [cornerMap_apply_eq]

end CornerBlk

/-! ## The universal idempotent -/

section Idem

variable (k) in
/-- `k → k × k`, the diagonal, as an algebra map from `k^Unit`. -/
noncomputable def diagTwo : (Unit → k) →ₐ[k] (Fin 2 → k) :=
  Pi.algHom k _ fun _ => Pi.evalAlgHom k (fun _ => k) ()

variable (n : ℕ)

/-- The scalars `k → M_n(R)`, as an algebra map from `k^Unit`. -/
noncomputable def unitScalar (T : Type u) [Ring T] [Algebra k T] :
    (Unit → k) →ₐ[k] Matrix (Fin n) (Fin n) T :=
  (Algebra.ofId k _).comp (Pi.evalAlgHom k (fun _ => k) ())

/-- `k × k → M_n(S)`, `(a, b) ↦ a E + b (1 - E)` for an idempotent `E`. -/
noncomputable def idemHom {E : Matrix (Fin n) (Fin n) S} (hE : E * E = E) :
    (Fin 2 → k) →ₐ[k] Matrix (Fin n) (Fin n) S := idem2Hom E hE

theorem idemHom_apply {E : Matrix (Fin n) (Fin n) S} (hE : E * E = E) (v : Fin 2 → k) :
    idemHom n hE v = v 0 • E + v 1 • (1 - E) := idem2Hom_apply E hE v

/-- **`M_n(R⟨E⟩) = M_n(R) ⊔_k (k × k)`.** -/
theorem IsIdemExt.isCoprod {j : R →ₐ[k] S} {E : Matrix (Fin n) (Fin n) S}
    (hS : IsIdemExt j n E) (hn : 1 ≤ n) :
    IsCoprod k (pairSigma (unitScalar n R) (diagTwo k)) (Matrix (Fin n) (Fin n) S)
      (unitScalar n S) (pairHom (AlgHom.mapMatrix j) (idemHom n hS.idem)) := by
  let c : Fin n := ⟨0, hn⟩
  refine ⟨fun l => ?_, ?_, ?_⟩
  · cases l <;> exact algHom_unit_ext _ _
  · intro T _ _ f₀ f _
    let F : Matrix (Fin n) (Fin n) R →ₐ[k] T := f true
    let G : (Fin 2 → k) →ₐ[k] T := f false
    have he : IsIdempotentElem (F (single c c 1)) := isIdempotentElem_single F c
    let p : T := G (Pi.single 0 1)
    have hp : p * p = p := by
      simp only [p, ← map_mul]; congr 1; ext i; fin_cases i <;> simp
    let E' := cornerBlk F c he rfl p id id
    have hE' : E' * E' = E' := by simp only [E', cornerBlk_mul_id, hp]
    obtain ⟨ψ, hψj, hψE⟩ := hS.lift he.Corner (cornerMap F c he rfl) E' hE'
    refine ⟨moritaHom F c he rfl ψ, algHom_unit_ext _ _, fun l => ?_⟩
    cases l
    · show (moritaHom F c he rfl ψ).comp (idemHom n hS.idem) = G
      have hE : moritaHom F c he rfl ψ E = p := moritaHom_of_cornerEnt F c he rfl ψ E p hψE
      have h1 : (Pi.single 1 1 : Fin 2 → k) = 1 - Pi.single 0 1 := by
        ext i; fin_cases i <;> simp
      refine algHom_pi_ext fun i => ?_
      rw [AlgHom.comp_apply, idemHom_apply]
      fin_cases i
      · simp [hE, p]
      · simp [map_sub, hE, p, h1]
    · exact moritaHom_comp_mapMatrix F c he rfl ψ j hψj
  · intro T _ _ g g' _ hl
    have hlt : g.comp (AlgHom.mapMatrix j) = g'.comp (AlgHom.mapMatrix j) := hl true
    have hlf : g.comp (idemHom n hS.idem) = g'.comp (idemHom n hS.idem) := hl false
    have hr : ∀ a b (r : R), g (single a b (j r)) = g' (single a b (j r)) := fun a b r => by
      have := congrArg (fun φ : Matrix (Fin n) (Fin n) R →ₐ[k] T => φ (single a b r)) hlt
      simpa [AlgHom.mapMatrix_apply, Matrix.map_single] using this
    have h1 : ∀ a b, g (single a b 1) = g' (single a b 1) := fun a b => by
      simpa using hr a b 1
    have hE : g E = g' E := by
      have := congrArg (fun φ : (Fin 2 → k) →ₐ[k] T => φ (Pi.single 0 1)) hlf
      simpa [idemHom_apply] using this
    refine ext_of_cornerMap c h1 (hS.ext _ _ _ ?_ ?_)
    · ext r
      exact corner_ext _ (hr c c r)
    · ext a b
      refine corner_ext _ ?_
      have hs : single c a (1 : S) * E * single b c 1 = single c c (E a b) := by
        simp [single_mul_mul_single]
      simp only [Matrix.map_apply, cornerMap_val]
      rw [← hs, map_mul, map_mul, map_mul, map_mul, h1, h1, hE]

end Idem

/-! ## The universal isomorphism -/

section Iso

variable {m m' : Type} [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m']

/-- The index type `m ⊕ m' ⊕ Unit` of the matrix ring in which `R^{1×m} D`, `R^{1×m'} D'` and a
nonzero complement become cyclic. -/
abbrev isoIdx (m m' : Type) : Type := m ⊕ m' ⊕ Unit

section Blocks

variable {T : Type*} [Ring T]

/-- `diag(X, 0, 0)`. -/
def blk₁ (m' : Type) (X : Matrix m m T) : Matrix (isoIdx m m') (isoIdx m m') T :=
  fromBlocks X 0 0 0

/-- `diag(0, X, 0)`. -/
def blk₂ (m : Type) (X : Matrix m' m' T) : Matrix (isoIdx m m') (isoIdx m m') T :=
  fromBlocks 0 0 0 (fromBlocks X 0 0 0)

/-- `X` in the `(m, m')` block. -/
def blk₁₂ (X : Matrix m m' T) : Matrix (isoIdx m m') (isoIdx m m') T :=
  fromBlocks 0 (fromCols X 0) 0 0

/-- `X` in the `(m', m)` block. -/
def blk₂₁ (X : Matrix m' m T) : Matrix (isoIdx m m') (isoIdx m m') T :=
  fromBlocks 0 0 (fromRows X 0) 0

variable (X : Matrix m m T) (Y : Matrix m' m' T) (U : Matrix m m' T) (V : Matrix m' m T)
  (X' : Matrix m m T) (Y' : Matrix m' m' T) (U' : Matrix m m' T) (V' : Matrix m' m T)

omit [DecidableEq m] in
@[simp] theorem blk₁_mul_blk₁ : blk₁ m' X * blk₁ m' X' = blk₁ m' (X * X') := by
  simp [blk₁, fromBlocks_multiply]
@[simp] theorem blk₁_mul_blk₁₂ : blk₁ m' X * blk₁₂ U = blk₁₂ (X * U) := by
  simp [blk₁, blk₁₂, fromBlocks_multiply]
@[simp] theorem blk₁_mul_blk₂₁ : blk₁ m' X * blk₂₁ V = 0 := by
  simp [blk₁, blk₂₁, fromBlocks_multiply]
@[simp] theorem blk₁_mul_blk₂ : blk₁ m' X * blk₂ m Y = 0 := by
  simp [blk₁, blk₂, fromBlocks_multiply]
@[simp] theorem blk₁₂_mul_blk₁ : blk₁₂ U * blk₁ m' X = 0 := by
  simp [blk₁, blk₁₂, fromBlocks_multiply]
@[simp] theorem blk₁₂_mul_blk₁₂ : blk₁₂ U * blk₁₂ U' = 0 := by
  simp [blk₁₂, fromBlocks_multiply]
@[simp] theorem blk₁₂_mul_blk₂₁ : blk₁₂ U * blk₂₁ V = blk₁ m' (U * V) := by
  simp [blk₁, blk₁₂, blk₂₁, fromBlocks_multiply, fromCols_mul_fromRows]
@[simp] theorem blk₁₂_mul_blk₂ : blk₁₂ U * blk₂ m Y = blk₁₂ (U * Y) := by
  simp [blk₁₂, blk₂, fromBlocks_multiply, fromCols_mul_fromBlocks]
@[simp] theorem blk₂₁_mul_blk₁ : blk₂₁ V * blk₁ m' X = blk₂₁ (V * X) := by
  simp [blk₁, blk₂₁, fromBlocks_multiply]
@[simp] theorem blk₂₁_mul_blk₁₂ : blk₂₁ V * blk₁₂ U = blk₂ m (V * U) := by
  simp only [blk₂, blk₁₂, blk₂₁, fromBlocks_multiply, fromRows_mul_fromCols]
  ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [fromBlocks, fromRows, fromCols]
@[simp] theorem blk₂₁_mul_blk₂₁ : blk₂₁ V * blk₂₁ V' = 0 := by
  simp [blk₂₁, fromBlocks_multiply]
@[simp] theorem blk₂₁_mul_blk₂ : blk₂₁ V * blk₂ m Y = 0 := by
  simp [blk₂, blk₂₁, fromBlocks_multiply]
@[simp] theorem blk₂_mul_blk₁ : blk₂ m Y * blk₁ m' X = 0 := by
  simp [blk₁, blk₂, fromBlocks_multiply]
@[simp] theorem blk₂_mul_blk₁₂ : blk₂ m Y * blk₁₂ U = 0 := by
  simp [blk₂, blk₁₂, fromBlocks_multiply]
@[simp] theorem blk₂_mul_blk₂₁ : blk₂ m Y * blk₂₁ V = blk₂₁ (Y * V) := by
  simp [blk₂, blk₂₁, fromBlocks_multiply, fromBlocks_mul_fromRows]
omit [DecidableEq m'] in
@[simp] theorem blk₂_mul_blk₂ : blk₂ m Y * blk₂ m Y' = blk₂ m (Y * Y') := by
  simp [blk₂, fromBlocks_multiply]


omit [DecidableEq m] [DecidableEq m'] in
theorem blk₁_mul_mul_blk₂ (Z : Matrix (isoIdx m m') (isoIdx m m') T) :
    blk₁ m' X * Z * blk₂ m Y = blk₁₂ (X * Z.submatrix Sum.inl (Sum.inr ∘ Sum.inl) * Y) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j | j <;>
    simp [blk₁, blk₂, blk₁₂, mul_apply, Fintype.sum_sum_type, Finset.sum_mul]

omit [DecidableEq m] [DecidableEq m'] in
theorem blk₂_mul_mul_blk₁ (Z : Matrix (isoIdx m m') (isoIdx m m') T) :
    blk₂ m Y * Z * blk₁ m' X = blk₂₁ (Y * Z.submatrix (Sum.inr ∘ Sum.inl) Sum.inl * X) := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j <;>
    simp [blk₁, blk₂, blk₂₁, mul_apply, Fintype.sum_sum_type, Finset.sum_mul]

omit [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m'] in
@[simp] theorem blk₁_submatrix : (blk₁ m' X).submatrix Sum.inl Sum.inl = X := by
  ext; simp [blk₁]

omit [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m'] in
@[simp] theorem blk₂_submatrix :
    (blk₂ m Y).submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl) = Y := by
  ext; simp [blk₂]

omit [Fintype m'] in
theorem sum_single_inl :
    ∑ x : m, single (Sum.inl x : isoIdx m m') (Sum.inl x) (1 : T) = blk₁ m' 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blk₁, single_apply, Matrix.sum_apply, one_apply, ite_and, Finset.sum_ite_eq']

omit [Fintype m] in
theorem sum_single_inr :
    ∑ x : m', single ((Sum.inr ∘ Sum.inl) x : isoIdx m m') ((Sum.inr ∘ Sum.inl) x) (1 : T) =
      blk₂ m 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [blk₂, single_apply, Matrix.sum_apply, one_apply, ite_and, Finset.sum_ite_eq']

variable {T' : Type*} [Ring T'] (f : T → T') (hf : f 0 = 0)
include hf

omit [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m'] in
@[simp] theorem blk₁_map : (blk₁ m' X).map f = blk₁ m' (X.map f) := by
  simp [blk₁, fromBlocks_map, hf]

omit [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m'] in
@[simp] theorem blk₂_map : (blk₂ m Y).map f = blk₂ m (Y.map f) := by
  simp [blk₂, fromBlocks_map, hf]

omit [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m'] in
@[simp] theorem blk₁₂_map : (blk₁₂ U).map f = blk₁₂ (U.map f) := by
  simp [blk₁₂, fromBlocks_map, fromCols_map, hf]

omit [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m'] in
@[simp] theorem blk₂₁_map : (blk₂₁ V).map f = blk₂₁ (V.map f) := by
  simp [blk₂₁, fromBlocks_map, fromRows_map, hf]
end Blocks

variable (k) in
/-- `k³ → M₂(k) × k`: `(a, b, c) ↦ (diag(a, b), c)`. -/
noncomputable def isoTarget : (Fin 3 → k) →ₐ[k] (Matrix (Fin 2) (Fin 2) k × k) :=
  idem3Hom (k := k) ((single 0 0 1 : Matrix (Fin 2) (Fin 2) k), (0 : k))
    ((single 1 1 1 : Matrix (Fin 2) (Fin 2) k), (0 : k))
    (by simp) (by simp) (by simp) (by simp)

theorem isoTarget_single (i : Fin 3) :
    isoTarget k (Pi.single i 1) =
      ![((single 0 0 1 : Matrix (Fin 2) (Fin 2) k), (0 : k)),
        ((single 1 1 1 : Matrix (Fin 2) (Fin 2) k), (0 : k)),
        1 - ((single 0 0 1 : Matrix (Fin 2) (Fin 2) k), (0 : k)) -
          ((single 1 1 1 : Matrix (Fin 2) (Fin 2) k), (0 : k))] i :=
  idem3Hom_single _ _ _ _ _ _ i

/-- `k³ → M_N(R)`: the three orthogonal idempotents `diag(D,0,0)`, `diag(0,D',0)`,
`diag(1-D,1-D',1)`. -/
noncomputable def isoSigma {T : Type u} [Ring T] [Algebra k T] (D : Matrix m m T)
    (D' : Matrix m' m' T) (hD : D * D = D) (hD' : D' * D' = D') :
    (Fin 3 → k) →ₐ[k] Matrix (isoIdx m m') (isoIdx m m') T :=
  idem3Hom (k := k) (blk₁ m' D) (blk₂ m D') (by rw [blk₁_mul_blk₁, hD])
    (by rw [blk₂_mul_blk₂, hD'])
    (blk₁_mul_blk₂ _ _) (blk₂_mul_blk₁ _ _)

theorem isoSigma_single {T : Type u} [Ring T] [Algebra k T] (D : Matrix m m T)
    (D' : Matrix m' m' T) (hD : D * D = D) (hD' : D' * D' = D') (i : Fin 3) :
    isoSigma (k := k) D D' hD hD' (Pi.single i 1) =
      ![blk₁ m' D, blk₂ m D', 1 - blk₁ m' D - blk₂ m D'] i :=
  idem3Hom_single _ _ _ _ _ _ i

theorem isoSigma_map {T T' : Type u} [Ring T] [Algebra k T] [Ring T'] [Algebra k T']
    (f : T →ₐ[k] T') (D : Matrix m m T) (D' : Matrix m' m' T) (hD : D * D = D)
    (hD' : D' * D' = D') (hfD : D.map f * D.map f = D.map f)
    (hfD' : D'.map f * D'.map f = D'.map f) :
    (AlgHom.mapMatrix f).comp (isoSigma (k := k) D D' hD hD') =
      isoSigma (D.map f) (D'.map f) hfD hfD' := by
  refine algHom_pi_ext fun i => ?_
  rw [AlgHom.comp_apply, isoSigma_single, isoSigma_single]
  fin_cases i
  · exact blk₁_map D f (map_zero f)
  · exact blk₂_map D' f (map_zero f)
  · simp only [Fin.reduceFinMk, Matrix.cons_val, map_sub, map_one]
    rw [AlgHom.mapMatrix_apply, AlgHom.mapMatrix_apply]
    exact congrArg₂ (fun x y => 1 - x - y) (blk₁_map D f (map_zero f))
      (blk₂_map D' f (map_zero f))

theorem IsIsoExt.left_A {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD : D * D = D) (hS : IsIsoExt j D D' A B) :
    D.map j * A = A := by
  conv_lhs => rw [← hS.cornerA]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, hD, hS.cornerA]

theorem IsIsoExt.right_A {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD' : D' * D' = D') (hS : IsIsoExt j D D' A B) :
    A * D'.map j = A := by
  conv_lhs => rw [← hS.cornerA]
  rw [Matrix.mul_assoc, ← Matrix.map_mul, hD', hS.cornerA]

theorem IsIsoExt.left_B {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD' : D' * D' = D') (hS : IsIsoExt j D D' A B) :
    D'.map j * B = B := by
  conv_lhs => rw [← hS.cornerB]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, hD', hS.cornerB]

theorem IsIsoExt.right_B {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD : D * D = D) (hS : IsIsoExt j D D' A B) :
    B * D.map j = B := by
  conv_lhs => rw [← hS.cornerB]
  rw [Matrix.mul_assoc, ← Matrix.map_mul, hD, hS.cornerB]

/-- The matrix units `diag(D,0,0)`, `A`, `B`, `diag(0,D',0)` of `isoHom`. -/
noncomputable def isoUnits {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    (A : Matrix m m' S) (B : Matrix m' m S) :
    Fin 2 → Fin 2 → Matrix (isoIdx m m') (isoIdx m m') S :=
  ![![blk₁ m' (D.map j), blk₁₂ A], ![blk₂₁ B, blk₂ m (D'.map j)]]

theorem isoUnits_mul {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD : D * D = D) (hD' : D' * D' = D')
    (hS : IsIsoExt j D D' A B) (a b c d : Fin 2) :
    isoUnits (j := j) (D := D) (D' := D') A B a b * isoUnits (j := j) (D := D) (D' := D') A B c d =
      if b = c then isoUnits (j := j) (D := D) (D' := D') A B a d else 0 := by
  have h1 : D.map j * D.map j = D.map j := by rw [← Matrix.map_mul, hD]
  have h2 : D'.map j * D'.map j = D'.map j := by rw [← Matrix.map_mul, hD']
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [isoUnits, h1, h2, hS.left_A hD, hS.right_A hD', hS.left_B hD', hS.right_B hD, hS.mulAB,
      hS.mulBA]

/-- `M₂(k) × k → M_N(S)`, sending the matrix units `e₁₂`, `e₂₁` to `A`, `B` placed in the
`(m, m')` and `(m', m)` blocks. -/
noncomputable def isoHom {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD : D * D = D) (hD' : D' * D' = D')
    (hS : IsIsoExt j D D' A B) :
    (Matrix (Fin 2) (Fin 2) k × k) →ₐ[k] Matrix (isoIdx m m') (isoIdx m m') S :=
  matUnitsProdHom (k := k) (isoUnits (j := j) (D := D) (D' := D') A B) (isoUnits_mul hD hD' hS)

theorem isoHom_single {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD : D * D = D) (hD' : D' * D' = D')
    (hS : IsIsoExt j D D' A B) (a b : Fin 2) :
    isoHom hD hD' hS (single a b 1, 0) = isoUnits (j := j) (D := D) (D' := D') A B a b :=
  matUnitsProdHom_single _ _ a b

theorem isoHom_snd {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD : D * D = D) (hD' : D' * D' = D')
    (hS : IsIsoExt j D D' A B) :
    isoHom hD hD' hS (0, 1) = 1 - (blk₁ m' (D.map j) + blk₂ m (D'.map j)) := by
  rw [isoHom, matUnitsProdHom_snd, Fin.sum_univ_two]
  rfl

/-- **`M_N(R⟨D ≅ D'⟩) = M_N(R) ⊔_{k³} (M₂(k) × k)`.** -/
theorem IsIsoExt.isCoprod {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD : D * D = D) (hD' : D' * D' = D')
    (hS : IsIsoExt j D D' A B) :
    IsCoprod k (pairSigma (isoSigma D D' hD hD') (isoTarget k))
      (Matrix (isoIdx m m') (isoIdx m m') S)
      (isoSigma (D.map j) (D'.map j) (by rw [← Matrix.map_mul, hD])
        (by rw [← Matrix.map_mul, hD']))
      (pairHom (AlgHom.mapMatrix j) (isoHom hD hD' hS)) := by
  let c : isoIdx m m' := Sum.inr (Sum.inr ())
  have hσ := isoSigma_map (k := k) j D D' hD hD' (by rw [← Matrix.map_mul, hD])
    (by rw [← Matrix.map_mul, hD'])
  refine ⟨fun l => ?_, ?_, ?_⟩
  · cases l
    · refine algHom_pi_ext fun i => ?_
      show isoHom hD hD' hS (isoTarget k (Pi.single i 1)) = _
      rw [isoTarget_single, isoSigma_single]
      fin_cases i
      · exact isoHom_single hD hD' hS 0 0
      · exact isoHom_single hD hD' hS 1 1
      · simp only [Fin.reduceFinMk, Matrix.cons_val, map_sub, map_one, isoHom_single]
        rfl
    · exact hσ
  · intro T _ _ f₀ f hf
    let F : Matrix (isoIdx m m') (isoIdx m m') R →ₐ[k] T := f true
    let G : Matrix (Fin 2) (Fin 2) k × k →ₐ[k] T := f false
    have he : IsIdempotentElem (F (single c c 1)) := isIdempotentElem_single F c
    let φ := cornerMap F c he rfl
    let w : Fin 2 → Fin 2 → T := fun a b => G (single a b 1, 0)
    have hw : ∀ a b c d, w a b * w c d = if b = c then w a d else 0 := by
      intro a b c d
      simp only [w, ← map_mul, Prod.mk_mul_mk, mul_zero]
      split_ifs with h
      · subst h; rw [single_mul_single_same, mul_one]
      · rw [single_mul_single_of_ne (h := h), Prod.mk_zero_zero, map_zero]
    have hq : ∀ i, F (isoSigma D D' hD hD' (Pi.single i 1)) = G (isoTarget k (Pi.single i 1)) :=
      fun i => (congrArg (fun φ => φ (Pi.single i 1)) (hf true)).trans
        (congrArg (fun φ => φ (Pi.single i 1)) (hf false)).symm
    have hq1 : F (blk₁ m' D) = w 0 0 := by
      have := hq 0; rw [isoSigma_single, isoTarget_single] at this; exact this
    have hq2 : F (blk₂ m D') = w 1 1 := by
      have := hq 1; rw [isoSigma_single, isoTarget_single] at this; exact this
    have hw0 : ∀ b, w 0 b = w 0 0 * w 0 b := fun b => by rw [hw]; rfl
    have hw0' : ∀ a, w a 0 = w a 0 * w 0 0 := fun a => by rw [hw]; rfl
    have hw1 : ∀ b, w 1 b = w 1 1 * w 1 b := fun b => by rw [hw]; rfl
    have hw1' : ∀ a, w a 1 = w a 1 * w 1 1 := fun a => by rw [hw]; rfl
    have h1l : ∀ b, F (blk₁ m' 1) * w 0 b = w 0 b := fun b => by
      rw [hw0, ← mul_assoc, ← hq1, ← map_mul, blk₁_mul_blk₁, one_mul]
    have h1r : ∀ a, w a 0 * F (blk₁ m' 1) = w a 0 := fun a => by
      rw [hw0', mul_assoc, ← hq1, ← map_mul, blk₁_mul_blk₁, mul_one]
    have h2l : ∀ b, F (blk₂ m 1) * w 1 b = w 1 b := fun b => by
      rw [hw1, ← mul_assoc, ← hq2, ← map_mul, blk₂_mul_blk₂, one_mul]
    have h2r : ∀ a, w a 1 * F (blk₂ m 1) = w a 1 := fun a => by
      rw [hw1', mul_assoc, ← hq2, ← map_mul, blk₂_mul_blk₂, mul_one]
    have hDφ : D.map φ = cornerBlk F c he rfl (w 0 0) Sum.inl Sum.inl := by
      rw [← hq1, cornerBlk_map, blk₁_submatrix]
    have hD'φ : D'.map φ =
        cornerBlk F c he rfl (w 1 1) (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl) := by
      rw [← hq2, cornerBlk_map, blk₂_submatrix]
    have r1 : D.map φ * cornerBlk F c he rfl (w 0 1) Sum.inl (Sum.inr ∘ Sum.inl) * D'.map φ =
        cornerBlk F c he rfl (w 0 1) Sum.inl (Sum.inr ∘ Sum.inl) := by
      rw [hDφ, hD'φ, cornerBlk_mul, cornerBlk_mul, sum_single_inl, sum_single_inr, h1r, hw,
        if_pos rfl, h2r, hw, if_pos rfl]
    have r2 : D'.map φ * cornerBlk F c he rfl (w 1 0) (Sum.inr ∘ Sum.inl) Sum.inl * D.map φ =
        cornerBlk F c he rfl (w 1 0) (Sum.inr ∘ Sum.inl) Sum.inl := by
      rw [hDφ, hD'φ, cornerBlk_mul, cornerBlk_mul, sum_single_inl, sum_single_inr, h2r, hw,
        if_pos rfl, h1r, hw, if_pos rfl]
    have r3 : cornerBlk F c he rfl (w 0 1) Sum.inl (Sum.inr ∘ Sum.inl) *
        cornerBlk F c he rfl (w 1 0) (Sum.inr ∘ Sum.inl) Sum.inl = D.map φ := by
      rw [hDφ, cornerBlk_mul, sum_single_inr, h2r, hw, if_pos rfl]
    have r4 : cornerBlk F c he rfl (w 1 0) (Sum.inr ∘ Sum.inl) Sum.inl *
        cornerBlk F c he rfl (w 0 1) Sum.inl (Sum.inr ∘ Sum.inl) = D'.map φ := by
      rw [hD'φ, cornerBlk_mul, sum_single_inl, h1r, hw, if_pos rfl]
    obtain ⟨ψ, hψj, hψA, hψB⟩ := hS.lift he.Corner φ _ _ r1 r2 r3 r4
    have hgF : (moritaHom F c he rfl ψ).comp (AlgHom.mapMatrix j) = F :=
      moritaHom_comp_mapMatrix F c he rfl ψ j hψj
    have hgY : ∀ Y, moritaHom F c he rfl ψ (Y.map j) = F Y := fun Y =>
      congrArg (fun φ : Matrix (isoIdx m m') (isoIdx m m') R →ₐ[k] T => φ Y) hgF
    have hg1 : moritaHom F c he rfl ψ (blk₁ m' (D.map j)) = w 0 0 := by
      rw [← blk₁_map D j (map_zero j), hgY, hq1]
    have hg2 : moritaHom F c he rfl ψ (blk₂ m (D'.map j)) = w 1 1 := by
      rw [← blk₂_map D' j (map_zero j), hgY, hq2]
    refine ⟨moritaHom F c he rfl ψ, ?_, fun l => ?_⟩
    · rw [← hσ, ← AlgHom.comp_assoc, hgF]
      exact hf true
    cases l
    · show (moritaHom F c he rfl ψ).comp (isoHom hD hD' hS) = G
      refine algHom_matrixProd_ext (fun a b => ?_) ?_
      · rw [AlgHom.comp_apply, isoHom_single]
        fin_cases a <;> fin_cases b
        · exact hg1
        · show moritaHom F c he rfl ψ (blk₁₂ A) = w 0 1
          refine moritaHom_of_cornerEnt F c he rfl ψ _ _ ?_
          have e1 : w 0 1 = F (blk₁ m' D) * w 0 1 * F (blk₂ m D') := by
            rw [hq1, hq2, hw, if_pos rfl, hw, if_pos rfl]
          show _ = cornerBlk F c he rfl (w 0 1) id id
          conv_rhs => rw [e1]
          rw [← cornerBlk_mul_id, ← cornerBlk_mul_id, cornerBlk_map, cornerBlk_map,
            submatrix_id_id, submatrix_id_id, blk₁_map _ _ (map_zero _),
            blk₂_map _ _ (map_zero _), blk₁_mul_mul_blk₂, blk₁₂_map _ _ (map_zero _), hψA]
          exact congrArg blk₁₂ r1.symm
        · show moritaHom F c he rfl ψ (blk₂₁ B) = w 1 0
          refine moritaHom_of_cornerEnt F c he rfl ψ _ _ ?_
          have e1 : w 1 0 = F (blk₂ m D') * w 1 0 * F (blk₁ m' D) := by
            rw [hq1, hq2, hw, if_pos rfl, hw, if_pos rfl]
          show _ = cornerBlk F c he rfl (w 1 0) id id
          conv_rhs => rw [e1]
          rw [← cornerBlk_mul_id, ← cornerBlk_mul_id, cornerBlk_map, cornerBlk_map,
            submatrix_id_id, submatrix_id_id, blk₁_map _ _ (map_zero _),
            blk₂_map _ _ (map_zero _), blk₂_mul_mul_blk₁, blk₂₁_map _ _ (map_zero _), hψB]
          exact congrArg blk₂₁ r2.symm
        · exact hg2
      · have h01 : ((0 : Matrix (Fin 2) (Fin 2) k), (1 : k)) =
            1 - ((single 0 0 1 : Matrix (Fin 2) (Fin 2) k), (0 : k)) -
              ((single 1 1 1 : Matrix (Fin 2) (Fin 2) k), (0 : k)) := by
          refine Prod.ext ?_ (by simp)
          ext a b; fin_cases a <;> fin_cases b <;> simp [one_apply]
        rw [AlgHom.comp_apply, isoHom_snd, map_sub, map_one, map_add, hg1, hg2, h01, map_sub,
          map_sub, map_one, sub_sub]
    · exact hgF
  · intro T _ _ g g' _ hl
    have hlt : g.comp (AlgHom.mapMatrix j) = g'.comp (AlgHom.mapMatrix j) := hl true
    have hlf : g.comp (isoHom hD hD' hS) = g'.comp (isoHom hD hD' hS) := hl false
    have hr : ∀ a b (r : R), g (single a b (j r)) = g' (single a b (j r)) := fun a b r => by
      have := congrArg
        (fun φ : Matrix (isoIdx m m') (isoIdx m m') R →ₐ[k] T => φ (single a b r)) hlt
      simpa [AlgHom.mapMatrix_apply, Matrix.map_single] using this
    have h1 : ∀ a b, g (single a b 1) = g' (single a b 1) := fun a b => by
      simpa using hr a b 1
    have hX : ∀ x, g (isoHom hD hD' hS x) = g' (isoHom hD hD' hS x) := fun x =>
      congrArg (fun φ : Matrix (Fin 2) (Fin 2) k × k →ₐ[k] T => φ x) hlf
    have hA : g (blk₁₂ A) = g' (blk₁₂ A) := by
      have := hX (single 0 1 1, 0); rw [isoHom_single] at this; exact this
    have hB : g (blk₂₁ B) = g' (blk₂₁ B) := by
      have := hX (single 1 0 1, 0); rw [isoHom_single] at this; exact this
    refine ext_of_cornerMap c h1 (hS.ext _ _ _ ?_ ?_ ?_)
    · ext r
      exact corner_ext _ (hr c c r)
    · ext a b
      refine corner_ext _ ?_
      have hs : single c (Sum.inl a) (1 : S) * blk₁₂ A * single (Sum.inr (Sum.inl b)) c 1 =
          single c c (A a b) := by
        simp [single_mul_mul_single, blk₁₂]
      simp only [Matrix.map_apply, cornerMap_val]
      rw [← hs, map_mul, map_mul, map_mul, map_mul, h1, h1, hA]
    · ext a b
      refine corner_ext _ ?_
      have hs : single c (Sum.inr (Sum.inl a)) (1 : S) * blk₂₁ B * single (Sum.inl b) c 1 =
          single c c (B a b) := by
        simp [single_mul_mul_single, blk₂₁]
      simp only [Matrix.map_apply, cornerMap_val]
      rw [← hs, map_mul, map_mul, map_mul, map_mul, h1, h1, hB]

end Iso

end Bergman
