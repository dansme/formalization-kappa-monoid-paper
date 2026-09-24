/-
**The two construction steps and their effect on `V`.**

**Bergman, *Coproducts and some universal ring constructions* (1974), Theorems 5.1 and 5.2**,
in the form needed here, as statements about presentations of `V`:

* adjoining a universal idempotent `n × n` matrix `E` (`n ≥ 1`, `R ≠ 0`) adds two generators
  `[E]`, `[1 - E]` and the one relation `[E] + [1 - E] = n [R]`;
* adjoining a universal isomorphism between two nonzero finitely generated projectives
  `P`, `Q` adds the one relation `[P] = [Q]`.

Both come from Bergman's coproduct theorem (`Bergman/Coprod.lean`) applied to the matrix-ring
descriptions of `Bergman/Morita.lean`, together with `V(M_n(S)) ≅ V(S)`, `V(k × k) = ℕ²` and
`V(M₂(k) × k) = ℕ²`.
-/
import KappaMonoid.Bergman.Morita
import KappaMonoid.Bergman.Coprod

universe u

namespace Bergman

open Matrix

variable {k : Type u} [Field k] {R S : Type u} [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {A : Type u} {γ : A → V R} {rel : Multiset A → Multiset A → Prop}

/-- The relations of `R`, read in `A ⊕ Bool`. -/
def liftRel (rel : Multiset A → Multiset A → Prop) (x y : Multiset (A ⊕ Bool)) : Prop :=
  ∃ x' y', rel x' y' ∧ x = x'.map Sum.inl ∧ y = y'.map Sum.inl

/-- The new relation `p + q = n • a₀` of a universal idempotent. -/
def idemRel (a₀ : A) (n : ℕ) (x y : Multiset (A ⊕ Bool)) : Prop :=
  x = {Sum.inr true, Sum.inr false} ∧ y = n • {Sum.inl a₀}

/-- The generators after adjoining a universal idempotent `E`: the old ones, `[E]` and
`[1 - E]`. -/
noncomputable def idemGen (j : R →ₐ[k] S) (γ : A → V R) {n : ℕ} {E : Matrix (Fin n) (Fin n) S}
    (hE : E * E = E) : A ⊕ Bool → V S :=
  Sum.elim (fun a => V.map j.toRingHom (γ a))
    (fun b => if b then cls E hE else
      cls (1 - E) (one_sub_idem hE))

/-- **Theorem 5.1** (on `V`): a universal idempotent adds `[E]`, `[1 - E]` and the relation
`[E] + [1 - E] = n [R]`. -/
theorem PresentedBy.idemExt (h : PresentedBy γ rel) (a₀ : A) (ha₀ : γ a₀ = V.one R)
    (hne : V.one R ≠ 0) {n : ℕ} (hn : 1 ≤ n) {j : R →ₐ[k] S} {E : Matrix (Fin n) (Fin n) S}
    (hS : IsIdemExt j n E) :
    PresentedBy (idemGen j γ hS.idem) (liftRel rel ⊔ idemRel a₀ n) := sorry

/-- **Theorem 5.2** (on `V`): a universal isomorphism between two nonzero projectives adds the
relation `[P] = [Q]`. -/
theorem PresentedBy.isoExt (h : PresentedBy γ rel) {m m' : Type} [Fintype m] [Fintype m']
    [DecidableEq m] [DecidableEq m'] {D : Matrix m m R} {D' : Matrix m' m' R}
    (hD : D * D = D) (hD' : D' * D' = D') (x y : Multiset A)
    (hx : cls D hD = msum γ x) (hy : cls D' hD' = msum γ y)
    (hx0 : msum γ x ≠ 0) (hy0 : msum γ y ≠ 0) {j : R →ₐ[k] S} {Aₘ : Matrix m m' S}
    {Bₘ : Matrix m' m S} (hS : IsIsoExt j D D' Aₘ Bₘ) :
    PresentedBy (fun a => V.map j.toRingHom (γ a)) (rel ⊔ fun x' y' => x' = x ∧ y' = y) := sorry

end Bergman
