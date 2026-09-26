/-
**The presentation of the realising algebra: definitions.**

The data `RingPres G J` of a presentation, its generators and defining relations, the realising
algebra `P.ring k` with its universal property, the atoms' classes `P.γ k` in `V` and the
relations `P.mrel` among them.  The two theorems about it are in `Bergman/MainRing.lean`.
-/
import KappaMonoid.Bergman.Idem
import Mathlib.Algebra.RingQuot


universe u

namespace Bergman

open Matrix

/-- An atom of a presentation: `R` itself, or the image of `E_g`, or of `1 - E_g`. -/
inductive Atom (G : Type u) : Type u
  | free
  | img (g : G)
  | coimg (g : G)

/-- The data of a presentation of the realising algebra. -/
structure RingPres (G J : Type u) where
  /-- The size of the universal idempotent matrix `E_g`. -/
  size : G → ℕ
  /-- The left-hand side of relation `j`: a list of atoms. -/
  lhs : J → List (Atom G)
  /-- The right-hand side of relation `j`. -/
  rhs : J → List (Atom G)

namespace RingPres

variable {G J : Type u} (P : RingPres G J)

/-- The size of the matrix of an atom. -/
def atomSize : Atom G → ℕ
  | .free => 1
  | .img g => P.size g
  | .coimg g => P.size g

/-- The index type of the block matrix of a list of atoms. -/
abbrev Idx (l : List (Atom G)) : Type := Σ t : Fin l.length, Fin (P.atomSize l[t])

/-- The generators. -/
inductive Gen : Type u
  | e (g : G) (a b : Fin (P.size g))
  | fwd (j : J) (a : P.Idx (P.lhs j)) (b : P.Idx (P.rhs j))
  | bwd (j : J) (a : P.Idx (P.rhs j)) (b : P.Idx (P.lhs j))

section Matrices

variable {T : Type u} [Ring T] (x : P.Gen → T)

/-- The matrix `E_g` of an assignment of the generators. -/
def emat (g : G) : Matrix (Fin (P.size g)) (Fin (P.size g)) T := fun a b => x (.e g a b)

/-- The matrix of an atom. -/
def atomMat : (α : Atom G) → Matrix (Fin (P.atomSize α)) (Fin (P.atomSize α)) T
  | .free => 1
  | .img g => P.emat x g
  | .coimg g => (1 : Matrix (Fin (P.size g)) (Fin (P.size g)) T) - P.emat x g

/-- The block matrix of a list of atoms. -/
def dmat (l : List (Atom G)) : Matrix (P.Idx l) (P.Idx l) T :=
  Matrix.blockDiagonal' fun t => P.atomMat x l[t]

/-- The matrix `A_j`. -/
def amat (j : J) : Matrix (P.Idx (P.lhs j)) (P.Idx (P.rhs j)) T := fun a b => x (.fwd j a b)

/-- The matrix `B_j`. -/
def bmat (j : J) : Matrix (P.Idx (P.rhs j)) (P.Idx (P.lhs j)) T := fun a b => x (.bwd j a b)

/-- The defining relations hold for the assignment `x`. -/
structure Holds : Prop where
  idem : ∀ g, P.emat x g * P.emat x g = P.emat x g
  cornerA : ∀ j, P.dmat x (P.lhs j) * P.amat x j * P.dmat x (P.rhs j) = P.amat x j
  cornerB : ∀ j, P.dmat x (P.rhs j) * P.bmat x j * P.dmat x (P.lhs j) = P.bmat x j
  mulAB : ∀ j, P.amat x j * P.bmat x j = P.dmat x (P.lhs j)
  mulBA : ∀ j, P.bmat x j * P.amat x j = P.dmat x (P.rhs j)

section Map

variable {T' : Type u} [Ring T'] (f : T →+* T')

theorem emat_map (g : G) : P.emat (f ∘ x) g = (P.emat x g).map f := rfl

theorem atomMat_map (α : Atom G) : P.atomMat (f ∘ x) α = (P.atomMat x α).map f := by
  cases α with
  | free => simp [atomMat]
  | img g => rfl
  | coimg g =>
    show (1 : Matrix (Fin (P.size g)) (Fin (P.size g)) T') - (P.emat x g).map f =
      ((1 : Matrix (Fin (P.size g)) (Fin (P.size g)) T) - P.emat x g).map f
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]

theorem dmat_map (l : List (Atom G)) : P.dmat (f ∘ x) l = (P.dmat x l).map f := by
  simp only [dmat, atomMat_map, Matrix.blockDiagonal'_map _ _ (map_zero f)]

theorem amat_map (j : J) : P.amat (f ∘ x) j = (P.amat x j).map f := rfl

theorem bmat_map (j : J) : P.bmat (f ∘ x) j = (P.bmat x j).map f := rfl

/-- The relations are preserved by ring maps. -/
theorem Holds.map (hx : P.Holds x) : P.Holds (f ∘ x) := by
  refine ⟨fun g => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [emat_map, ← Matrix.map_mul, hx.idem]
  · rw [dmat_map, dmat_map, amat_map, ← Matrix.map_mul, ← Matrix.map_mul, hx.cornerA]
  · rw [dmat_map, dmat_map, bmat_map, ← Matrix.map_mul, ← Matrix.map_mul, hx.cornerB]
  · rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, hx.mulAB]
  · rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, hx.mulBA]

end Map

/-- The idempotents depend only on the values of `x` on the generators `e`. -/
theorem dmat_congr {x' : P.Gen → T} (h : ∀ g a b, x (.e g a b) = x' (.e g a b))
    (l : List (Atom G)) : P.dmat x l = P.dmat x' l := by
  have he : ∀ g, P.emat x g = P.emat x' g := fun g => by ext a b; exact h g a b
  have ha : ∀ α, P.atomMat x α = P.atomMat x' α := fun α => by
    cases α with
    | free => rfl
    | img g => exact he g
    | coimg g =>
      show (1 : Matrix (Fin (P.size g)) (Fin (P.size g)) T) - P.emat x g = 1 - P.emat x' g
      rw [he]
  simp only [dmat, ha]

end Matrices

variable (k : Type u) [Field k]

/-- The defining relations, entrywise, in the free algebra. -/
inductive Rel : FreeAlgebra k P.Gen → FreeAlgebra k P.Gen → Prop
  | idem (g a b) : Rel ((P.emat (FreeAlgebra.ι k) g * P.emat (FreeAlgebra.ι k) g) a b)
      (P.emat (FreeAlgebra.ι k) g a b)
  | cornerA (j a b) : Rel ((P.dmat (FreeAlgebra.ι k) (P.lhs j) * P.amat (FreeAlgebra.ι k) j *
      P.dmat (FreeAlgebra.ι k) (P.rhs j)) a b) (P.amat (FreeAlgebra.ι k) j a b)
  | cornerB (j a b) : Rel ((P.dmat (FreeAlgebra.ι k) (P.rhs j) * P.bmat (FreeAlgebra.ι k) j *
      P.dmat (FreeAlgebra.ι k) (P.lhs j)) a b) (P.bmat (FreeAlgebra.ι k) j a b)
  | mulAB (j a b) : Rel ((P.amat (FreeAlgebra.ι k) j * P.bmat (FreeAlgebra.ι k) j) a b)
      (P.dmat (FreeAlgebra.ι k) (P.lhs j) a b)
  | mulBA (j a b) : Rel ((P.bmat (FreeAlgebra.ι k) j * P.amat (FreeAlgebra.ι k) j) a b)
      (P.dmat (FreeAlgebra.ι k) (P.rhs j) a b)

/-- **The realising algebra** of the presentation. -/
def ring : Type u := RingQuot (P.Rel k)

instance : Ring (P.ring k) := inferInstanceAs (Ring (RingQuot (P.Rel k)))

instance : Algebra k (P.ring k) := inferInstanceAs (Algebra k (RingQuot (P.Rel k)))

/-- The generators, in the realising algebra. -/
def gen : P.Gen → P.ring k := fun g => RingQuot.mkAlgHom k (P.Rel k) (FreeAlgebra.ι k g)

/-- The relations hold for `f ∘ ι` iff `f` kills `Rel`. -/
theorem holds_comp_iff {T : Type u} [Ring T] (f : FreeAlgebra k P.Gen →+* T) :
    P.Holds (f ∘ FreeAlgebra.ι k) ↔ ∀ a b, P.Rel k a b → f a = f b := by
  have entry : ∀ {m n : Type} (M N : Matrix m n (FreeAlgebra k P.Gen)),
      M.map f = N.map f ↔ ∀ a b, f (M a b) = f (N a b) := fun M N =>
    ⟨fun h a b => congrFun (congrFun h a) b, fun h => by ext a b; exact h a b⟩
  constructor
  · intro hx a b h
    cases h with
    | idem g a b =>
      have := hx.idem g
      rw [emat_map, ← Matrix.map_mul, entry] at this
      exact this a b
    | cornerA j a b =>
      have := hx.cornerA j
      rw [dmat_map, dmat_map, amat_map, ← Matrix.map_mul, ← Matrix.map_mul, entry] at this
      exact this a b
    | cornerB j a b =>
      have := hx.cornerB j
      rw [dmat_map, dmat_map, bmat_map, ← Matrix.map_mul, ← Matrix.map_mul, entry] at this
      exact this a b
    | mulAB j a b =>
      have := hx.mulAB j
      rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, entry] at this
      exact this a b
    | mulBA j a b =>
      have := hx.mulBA j
      rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, entry] at this
      exact this a b
  · intro hf
    refine ⟨fun g => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
    · rw [emat_map, ← Matrix.map_mul, entry]; exact fun a b => hf _ _ (.idem g a b)
    · rw [dmat_map, dmat_map, amat_map, ← Matrix.map_mul, ← Matrix.map_mul, entry]
      exact fun a b => hf _ _ (.cornerA j a b)
    · rw [dmat_map, dmat_map, bmat_map, ← Matrix.map_mul, ← Matrix.map_mul, entry]
      exact fun a b => hf _ _ (.cornerB j a b)
    · rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, entry]
      exact fun a b => hf _ _ (.mulAB j a b)
    · rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, entry]
      exact fun a b => hf _ _ (.mulBA j a b)

theorem holds_gen : P.Holds (P.gen k) :=
  (P.holds_comp_iff k (RingQuot.mkAlgHom k (P.Rel k)).toRingHom).2
    fun _ _ h => RingQuot.mkAlgHom_rel k h

/-- The universal property: assignments satisfying the relations extend uniquely. -/
theorem lift {T : Type u} [Ring T] [Algebra k T] (x : P.Gen → T) (hx : P.Holds x) :
    ∃ ψ : P.ring k →ₐ[k] T, ∀ g, ψ (P.gen k g) = x g := by
  let f := FreeAlgebra.lift k x
  have hfx : (f.toRingHom : FreeAlgebra k P.Gen → T) ∘ FreeAlgebra.ι k = x :=
    funext fun g => FreeAlgebra.lift_ι_apply x g
  have key : ∀ a b, P.Rel k a b → f a = f b :=
    (P.holds_comp_iff k f.toRingHom).1 (hfx ▸ hx)
  refine ⟨RingQuot.liftAlgHom k ⟨f, key⟩, fun g => ?_⟩
  change RingQuot.liftAlgHom k ⟨f, key⟩ (RingQuot.mkAlgHom k (P.Rel k) (FreeAlgebra.ι k g)) = x g
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]
  exact FreeAlgebra.lift_ι_apply x g

theorem hom_ext {T : Type u} [Ring T] [Algebra k T] (ψ ψ' : P.ring k →ₐ[k] T)
    (h : ∀ g, ψ (P.gen k g) = ψ' (P.gen k g)) : ψ = ψ' := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  exact h g


/-- The class in `V` of an atom. -/
theorem atomMat_idem {T : Type u} [Ring T] (x : P.Gen → T) (hx : P.Holds x) (α : Atom G) :
    P.atomMat x α * P.atomMat x α = P.atomMat x α := by
  cases α with
  | free => simp [atomMat]
  | img g => exact hx.idem g
  | coimg g => exact one_sub_idem (hx.idem g)

theorem dmat_idem {T : Type u} [Ring T] (x : P.Gen → T)
    (hx : ∀ g, P.emat x g * P.emat x g = P.emat x g) (l : List (Atom G)) :
    P.dmat x l * P.dmat x l = P.dmat x l := by
  refine blockDiagonal'_idem _ fun t => ?_
  cases h : l[t] with
  | free => simp [atomMat]
  | img g => exact hx g
  | coimg g => exact one_sub_idem (hx g)


noncomputable def γ (α : Atom G) : V (P.ring k) :=
  cls (m := Fin (P.atomSize α)) (P.atomMat (P.gen k) α) (P.atomMat_idem (P.gen k) (P.holds_gen k) α)

/-- The relations among the atoms. -/
def mrel (x y : Multiset (Atom G)) : Prop :=
  (∃ g, x = {.img g, .coimg g} ∧ y = P.size g • {.free}) ∨ (∃ j, x = ↑(P.lhs j) ∧ y = ↑(P.rhs j))


end RingPres

end Bergman
