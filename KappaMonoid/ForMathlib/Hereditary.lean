/-
**Hereditary rings.**

Mathlib has no notion of a hereditary ring, so it is defined here.  A ring is *left hereditary*
when every left ideal is projective as a left module, *right hereditary* when every right ideal is
projective as a right module, and *hereditary* when it is both.

Handedness matters in this development and in the paper.  `Ideal R` is `Submodule R R`, so it is
the *left* ideals, and `Module R M` is a *left* module; the paper works with right modules
throughout and its Corollary 4.7(1)(iii) accordingly says "right hereditary ring".  The two are
mirror images, and everything here is stated on the left, which is the side the formalisation uses.
Right ideals of `R` are the left ideals of `Rᵐᵒᵖ`, which is how `IsRightHereditary` is phrased.
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Ring.Opposite
import Mathlib.RingTheory.Ideal.Defs

universe u

/-- A ring is **left hereditary** when every left ideal is projective as a left module. -/
class IsLeftHereditary (R : Type u) [Ring R] : Prop where
  /-- Every left ideal is projective. -/
  projective_ideal : ∀ I : Ideal R, Module.Projective R I

/-- A ring is **right hereditary** when every right ideal is projective as a right module.  The
right ideals of `R` are the left ideals of `Rᵐᵒᵖ`. -/
class IsRightHereditary (R : Type u) [Ring R] : Prop where
  /-- Every right ideal is projective. -/
  projective_ideal : ∀ I : Ideal Rᵐᵒᵖ, Module.Projective Rᵐᵒᵖ I

/-- A ring is **hereditary** when it is both left and right hereditary.  The two are independent:
there are rings satisfying one and not the other. -/
class IsHereditary (R : Type u) [Ring R] : Prop where
  /-- A hereditary ring is left hereditary. -/
  toIsLeftHereditary : IsLeftHereditary R
  /-- A hereditary ring is right hereditary. -/
  toIsRightHereditary : IsRightHereditary R

attribute [instance] IsHereditary.toIsLeftHereditary IsHereditary.toIsRightHereditary

/-- Every left ideal of a left hereditary ring is projective. -/
instance IsLeftHereditary.projective {R : Type u} [Ring R] [IsLeftHereditary R] (I : Ideal R) :
    Module.Projective R I :=
  IsLeftHereditary.projective_ideal I

/-- Every right ideal of a right hereditary ring is projective. -/
instance IsRightHereditary.projective {R : Type u} [Ring R] [IsRightHereditary R]
    (I : Ideal Rᵐᵒᵖ) : Module.Projective Rᵐᵒᵖ I :=
  IsRightHereditary.projective_ideal I

/-- Right hereditary is left hereditary on the opposite ring, by definition. -/
theorem isRightHereditary_iff_isLeftHereditary_op {R : Type u} [Ring R] :
    IsRightHereditary R ↔ IsLeftHereditary Rᵐᵒᵖ :=
  ⟨fun h => ⟨h.projective_ideal⟩, fun h => ⟨h.projective_ideal⟩⟩

theorem IsHereditary.mk' {R : Type u} [Ring R] (hleft : ∀ I : Ideal R, Module.Projective R I)
    (hright : ∀ I : Ideal Rᵐᵒᵖ, Module.Projective Rᵐᵒᵖ I) : IsHereditary R :=
  ⟨⟨hleft⟩, ⟨hright⟩⟩
