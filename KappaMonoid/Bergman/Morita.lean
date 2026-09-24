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
    (Fin 2 → k) →ₐ[k] Matrix (Fin n) (Fin n) S := sorry

theorem idemHom_apply {E : Matrix (Fin n) (Fin n) S} (hE : E * E = E) (v : Fin 2 → k) :
    idemHom n hE v = v 0 • E + v 1 • (1 - E) := sorry

/-- **`M_n(R⟨E⟩) = M_n(R) ⊔_k (k × k)`.** -/
theorem IsIdemExt.isCoprod {j : R →ₐ[k] S} {E : Matrix (Fin n) (Fin n) S}
    (hS : IsIdemExt j n E) (hn : 1 ≤ n) :
    IsCoprod k (pairSigma (unitScalar n R) (diagTwo k)) (Matrix (Fin n) (Fin n) S)
      (unitScalar n S) (pairHom (AlgHom.mapMatrix j) (idemHom n hS.idem)) := sorry

end Idem

/-! ## The universal isomorphism -/

section Iso

variable {m m' : Type} [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m']

/-- The index type `m ⊕ m' ⊕ Unit` of the matrix ring in which `R^{1×m} D`, `R^{1×m'} D'` and a
nonzero complement become cyclic. -/
abbrev isoIdx (m m' : Type) : Type := m ⊕ m' ⊕ Unit

variable (k) in
/-- `k³ → M₂(k) × k`: `(a, b, c) ↦ (diag(a, b), c)`. -/
noncomputable def isoTarget : (Fin 3 → k) →ₐ[k] (Matrix (Fin 2) (Fin 2) k × k) := sorry

/-- `k³ → M_N(R)`: the three orthogonal idempotents `diag(D,0,0)`, `diag(0,D',0)`,
`diag(1-D,1-D',1)`. -/
noncomputable def isoSigma {T : Type u} [Ring T] [Algebra k T] (D : Matrix m m T)
    (D' : Matrix m' m' T) (hD : D * D = D) (hD' : D' * D' = D') :
    (Fin 3 → k) →ₐ[k] Matrix (isoIdx m m') (isoIdx m m') T := sorry

/-- `M₂(k) × k → M_N(S)`, sending the matrix units `e₁₂`, `e₂₁` to `A`, `B` placed in the
`(m, m')` and `(m', m)` blocks. -/
noncomputable def isoHom {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD : D * D = D) (hD' : D' * D' = D')
    (hS : IsIsoExt j D D' A B) :
    (Matrix (Fin 2) (Fin 2) k × k) →ₐ[k] Matrix (isoIdx m m') (isoIdx m m') S := sorry

/-- **`M_N(R⟨D ≅ D'⟩) = M_N(R) ⊔_{k³} (M₂(k) × k)`.** -/
theorem IsIsoExt.isCoprod {j : R →ₐ[k] S} {D : Matrix m m R} {D' : Matrix m' m' R}
    {A : Matrix m m' S} {B : Matrix m' m S} (hD : D * D = D) (hD' : D' * D' = D')
    (hS : IsIsoExt j D D' A B) :
    IsCoprod k (pairSigma (isoSigma D D' hD hD') (isoTarget k))
      (Matrix (isoIdx m m') (isoIdx m m') S)
      (isoSigma (D.map j) (D'.map j) (by rw [← Matrix.map_mul, hD])
        (by rw [← Matrix.map_mul, hD']))
      (pairHom (AlgHom.mapMatrix j) (isoHom hD hD' hS)) := sorry

end Iso

end Bergman
