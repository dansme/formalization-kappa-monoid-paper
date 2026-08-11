import Mathlib
#check @Submodule.smul_mem_smul
#check @Ideal.IsTwoSided
#check @Submodule.map_smul''
#check @Finsupp.linearCombination_apply
#check @Finsupp.lapply
#check @LinearMap.mulRight
#check @Ideal.mul_le_left
#check @Ideal.mul_le_right
example (R : Type) [Ring R] (I : Ideal R) [I.IsTwoSided] (a r : R) (h : a ∈ I) : a * r ∈ I := by
  exact I.mul_mem_right r h
example (R : Type) [Ring R] (P : Type) [AddCommGroup P] [Module R P] (f : P →ₗ[R] R) (r : R) :
    P →ₗ[R] R := (LinearMap.mulRight R r).comp f
example (R : Type) [Ring R] (I : Ideal R) : I • (⊤ : Submodule R R) ≤ I := by
  exact Submodule.smul_le.2 (fun a ha x _ => by exact?)
