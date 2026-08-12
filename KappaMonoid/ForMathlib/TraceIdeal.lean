/-
Trace ideals.

Mathlib has no trace ideal — `Module.trace` is the trace of an endomorphism, unrelated — so the
definition and the facts Proposition 5.4 rests on are developed here.  They are elementary and
entirely general: nothing in this file mentions `κ`-monoids, and it depends only on Mathlib.

`Tr(P) = Σ_{f ∈ Hom(P,R)} im f` is a *two-sided* ideal, it satisfies `P = Tr(P)·P` for projective
`P` and is the least two-sided ideal that does, it is idempotent, it is an isomorphism invariant,
`Tr(R) = R`, a direct summand has a smaller trace ideal and a direct sum has the supremum.
-/
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Ideal.Operations

universe u v

variable (R : Type u) [Ring R] (P : Type u) [AddCommGroup P] [Module R P]

/-- The **trace ideal** `Tr(P) = Σ_{f ∈ Hom(P,R)} im f`. -/
noncomputable def traceIdeal : Ideal R := ⨆ f : P →ₗ[R] R, LinearMap.range f

theorem le_traceIdeal (f : P →ₗ[R] R) : LinearMap.range f ≤ traceIdeal R P :=
  le_iSup (fun f : P →ₗ[R] R => LinearMap.range f) f

/-- **The trace ideal is two-sided**, so `Ideal R` (= left ideals) is not the wrong home for it:
right multiplication by `r` is a left-`R`-linear endomorphism of `R`, so `f (·) * r` is again a
functional on `P`.

This is needed because `I • (⊤ : Submodule R R) ≤ I` is *false* for a one-sided ideal, and that
inclusion is what `traceIdeal_le_of_smul_eq` and `traceIdeal_mul_self` rest on. -/
instance traceIdeal_isTwoSided : (traceIdeal R P).IsTwoSided where
  mul_mem_of_left := by
    intro a r ha
    -- `a` lies in a sum of ranges; push the whole sum through `· * r`
    have hle : traceIdeal R P ≤ Submodule.comap (LinearMap.mulRight R r) (traceIdeal R P) := by
      refine iSup_le fun f => ?_
      rintro x ⟨p, rfl⟩
      exact le_traceIdeal R P ((LinearMap.mulRight R r).comp f) ⟨p, rfl⟩
    exact hle ha

/-- `P = Tr(P) · P` for projective `P`.

Proof: `Module.projective_def` gives `s : P →ₗ[R] P →₀ R` splitting `linearCombination R id`, so
`x = Σ_{p ∈ supp (s x)} (s x) p • p`.  Each coefficient map `x ↦ (s x) p` is the linear functional
`Finsupp.lapply p ∘ₗ s`, hence lands in `Tr(P)`; so `x ∈ Tr(P) • ⊤`. -/
theorem smul_traceIdeal_eq [Module.Projective R P] :
    traceIdeal R P • (⊤ : Submodule R P) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨s, hs⟩ := (Module.projective_def (R := R) (P := P)).mp inferInstance
  have hx : (Finsupp.linearCombination R id) (s x) = x := hs x
  rw [← hx, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  have hcoef : (s x) p ∈ traceIdeal R P :=
    le_traceIdeal R P ((Finsupp.lapply p).comp s) ⟨x, rfl⟩
  exact Submodule.smul_mem_smul hcoef Submodule.mem_top

/-- `Tr(P)` is the least *two-sided* ideal `I` with `P = I · P`.

Proof: if `I • ⊤ = ⊤` then for any `f : P →ₗ[R] R`, `im f = f (I • ⊤) = I * im f ⊆ I`, the last
step by two-sidedness. -/
theorem traceIdeal_le_of_smul_eq {I : Ideal R} [I.IsTwoSided]
    (h : I • (⊤ : Submodule R P) = ⊤) : traceIdeal R P ≤ I := by
  refine iSup_le fun f => ?_
  rw [LinearMap.range_eq_map, ← h, Submodule.map_smul'']
  exact Submodule.smul_le.2 fun a ha x _ => Ideal.IsTwoSided.mul_mem_of_left x ha

/-- `Tr(P)` is idempotent.

Proof: `Tr(P) • ⊤ = ⊤` gives `im f = f (Tr(P) • ⊤) = Tr(P) * im f ⊆ Tr(P) * Tr(P)` for every `f`,
so `Tr(P) ≤ Tr(P) * Tr(P)`; the reverse inclusion is `Ideal.mul_le_left`. -/
theorem traceIdeal_mul_self [Module.Projective R P] :
    traceIdeal R P * traceIdeal R P = traceIdeal R P := by
  refine le_antisymm Ideal.mul_le_left (iSup_le fun f => ?_)
  rw [LinearMap.range_eq_map, ← smul_traceIdeal_eq R P, Submodule.map_smul'']
  refine Submodule.smul_le.2 fun a ha x hx => ?_
  exact Ideal.mul_mem_mul ha (le_traceIdeal R P f ((LinearMap.range_eq_map f) ▸ hx))


/-! ### The trace ideal as an invariant

Proposition 5.4 needs three more facts, all elementary: the trace ideal only depends on the
isomorphism class, `Tr(R) = R`, and the trace ideal of a direct sum is the supremum of the trace
ideals of the summands (only `≤` is used, together with the reverse inclusion for a single
summand). -/

/-- The trace ideal is an isomorphism invariant. -/
theorem traceIdeal_of_iso {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (e : M ≃ₗ[R] N) : traceIdeal R M = traceIdeal R N := by
  refine le_antisymm (iSup_le fun f => ?_) (iSup_le fun f => ?_)
  · rintro y ⟨m, rfl⟩
    exact le_traceIdeal R N (f.comp (e.symm : N →ₗ[R] M)) ⟨e m, by simp⟩
  · rintro y ⟨n, rfl⟩
    exact le_traceIdeal R M (f.comp (e : M →ₗ[R] N)) ⟨e.symm n, by simp⟩

/-- `Tr(R) = R`: the identity is a functional with full image. -/
theorem traceIdeal_self : traceIdeal R R = ⊤ :=
  eq_top_iff.mpr fun x _ => le_traceIdeal R R LinearMap.id ⟨x, rfl⟩

/-- A direct summand has a smaller trace ideal: compose a functional with the projection. -/
theorem traceIdeal_le_of_prod {M N K : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup K] [Module R K] (e : M ≃ₗ[R] N × K) :
    traceIdeal R N ≤ traceIdeal R M := by
  refine iSup_le fun f => ?_
  rintro y ⟨n, rfl⟩
  refine le_traceIdeal R M (f.comp ((LinearMap.fst R N K).comp (e : M →ₗ[R] N × K))) ?_
  exact ⟨e.symm (n, 0), by simp⟩

/-- The trace ideal of a direct sum is contained in the supremum of the trace ideals: a functional
on the sum restricts to each summand, and every element is a finite sum of its components. -/
theorem traceIdeal_dsum_le {ι : Type u} (M : ι → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] :
    traceIdeal R (DirectSum ι M) ≤ ⨆ i, traceIdeal R (M i) := by
  classical
  refine iSup_le fun f => ?_
  rintro y ⟨x, rfl⟩
  have hx : (∑ i ∈ x.support, DirectSum.of (fun i => M i) i (x i)) = x := DFinsupp.sum_single
  rw [← hx, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine Submodule.mem_iSup_of_mem i ?_
  exact le_traceIdeal R (M i) (f.comp (DirectSum.lof R ι M i)) ⟨x i, rfl⟩


/-- **If the trace ideal is everything, finitely many functionals already witness `1`.**  This is
the paper's "let `1_R ∈ im(f₁) + ⋯ + im(f_k)`". -/
theorem exists_sum_eq_one_of_traceIdeal_eq_top (h : traceIdeal R P = ⊤) :
    ∃ (n : ℕ) (f : Fin n → (P →ₗ[R] R)) (x : Fin n → P), ∑ j, f j (x j) = 1 := by
  classical
  let N : Ideal R :=
    { carrier := {r | ∃ (n : ℕ) (f : Fin n → (P →ₗ[R] R)) (x : Fin n → P), ∑ j, f j (x j) = r}
      zero_mem' := ⟨0, Fin.elim0, Fin.elim0, by simp⟩
      add_mem' := by
        rintro a b ⟨n, f, x, rfl⟩ ⟨m, g, y, rfl⟩
        exact ⟨n + m, Fin.append f g, Fin.append x y, by rw [Fin.sum_univ_add]; simp⟩
      smul_mem' := by
        rintro c a ⟨n, f, x, rfl⟩
        refine ⟨n, f, fun j => c • x j, ?_⟩
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => map_smul (f j) c (x j) }
  have hle : traceIdeal R P ≤ N := by
    refine iSup_le fun f => ?_
    rintro y ⟨p, rfl⟩
    exact ⟨1, fun _ => f, fun _ => p, by simp⟩
  exact hle (by rw [h]; trivial)
