/-
**Section 5: Proposition 5.4**, the trace ideal criterion.

`Tr(P₂) ⊆ Tr(P₁)`, `Tr(P₁) = R` and `P₂ | P₁^{(ℵ₀)}` are equivalent for two generators of
`V^{ℵ₀}(R)`, and over a ring whose projectives are direct sums of finitely generated modules
`Tr(P₁) = Tr(P₂)` says exactly that every countably but not finitely generated projective is free.

The trace ideal itself is general ring theory and lives in `KappaMonoid/ForMathlib/TraceIdeal.lean`;
what is here is its interaction with `V^{ℵ₀}(R)`.
-/
import KappaMonoid.TwoGen.Realization
import KappaMonoid.ForMathlib.TraceIdeal
import Mathlib.LinearAlgebra.Projection

universe u v

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

-- The cardinal universe is pinned to `H`'s: `§5` fixes `κ = ℵ₀` and works in a single universe, and
-- leaving `ℵ₀`'s universe to be auto-bound makes two occurrences in one statement refer to
-- *different* universes (trap 5 of `CLAUDE.md`).
variable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]

section Prop54

variable (R : Type u) [Ring R]

/-- `ℵ₀` copies of a class are represented by the countable direct sum of its representative. -/
theorem rep_cmul_top_dsum (p : (projClass R ℵ₀ le_rfl).carrier) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    Nonempty ((projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)
      ≃ₗ[R] DirectSum (Idx (ℵ₀ : Cardinal.{u})) (fun _ => (projClass R ℵ₀ le_rfl).rep p)) := by
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  rw [show KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p
      = KMonoid.sumOf (κ := ℵ₀) (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u})))
        (fun _ : Idx (ℵ₀ : Cardinal.{u}) => p) from
    (KMonoid.cmul_congr (mk_Idx (ℵ₀ : Cardinal.{u})).symm le_rfl
        (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u}))) p).trans
      (KMonoid.cmul_eq_sumOf (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u}))) p)]
  exact (projClass R ℵ₀ le_rfl).rep_sumOf le_rfl (le_of_eq (mk_Idx _))
    (fun _ : Idx (ℵ₀ : Cardinal.{u}) => p)

/-- **`Tr(P₁) = R` makes `R` a direct summand of a finite power of `P₁`**, hence `[R] ≼ n [P₁]`
in `V^{ℵ₀}(R)`.

The finitely many functionals of `exists_sum_eq_one_of_traceIdeal_eq_top` assemble into an
epimorphism `P₁ⁿ ↠ R`; it splits because `R` is projective, and the resulting idempotent cuts
`P₁ⁿ` into `R` and a complement, both of which are again classes because `V^{ℵ₀}(R)` is closed
under direct summands. -/
theorem addLe_cmul_of_traceIdeal_eq_top (p₁ : (projClass R ℵ₀ le_rfl).carrier)
    (k : Idx (ℵ₀ : Cardinal.{u}))
    (h : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    ∃ n : ℕ, Projective.unitClass R ℵ₀ le_rfl k
      ≼ KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u})
          (le_of_lt Cardinal.natCast_lt_aleph0) p₁ := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  set P := (projClass R ℵ₀ le_rfl).rep p₁ with hP
  obtain ⟨n, f, x, hfx⟩ := exists_sum_eq_one_of_traceIdeal_eq_top R P h
  refine ⟨n, ?_⟩
  -- the epimorphism `P₁ⁿ ↠ R`
  set Φ : DirectSum (ULift.{u} (Fin n)) (fun _ => P) →ₗ[R] R :=
    DirectSum.toModule R _ _ (fun j => f j.down) with hΦ
  have hone : (1 : R) ∈ LinearMap.range Φ := by
    refine ⟨∑ j : ULift.{u} (Fin n), DirectSum.lof R _ (fun _ => P) j (x j.down), ?_⟩
    rw [map_sum, ← hfx]
    exact Fintype.sum_equiv Equiv.ulift _ _
      (fun j => DirectSum.toModule_lof R (M := fun _ => P) j (x j.down))
  have hsurj : Function.Surjective Φ :=
    LinearMap.range_eq_top.mp (Ideal.eq_top_iff_one _ |>.mpr hone)
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property Φ LinearMap.id hsurj
  have hψinv : ∀ r : R, Φ (ψ r) = r := fun r => congrFun (congrArg DFunLike.coe hψ) r
  -- the idempotent `ψ ∘ Φ` splits `P₁ⁿ`
  set π : DirectSum (ULift.{u} (Fin n)) (fun _ => P) →ₗ[R]
      DirectSum (ULift.{u} (Fin n)) (fun _ => P) := ψ.comp Φ with hπ
  have hidem : IsIdempotentElem π := by
    refine LinearMap.ext fun y => ?_
    show ψ (Φ (ψ (Φ y))) = ψ (Φ y)
    rw [hψinv]
  have hcompl : IsCompl (LinearMap.range π) (LinearMap.ker π) := LinearMap.IsIdempotentElem.isCompl hidem
  have hrange : LinearMap.range π = LinearMap.range ψ := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨z, rfl⟩
      exact ⟨Φ z, rfl⟩
    · rintro y ⟨r, rfl⟩
      exact ⟨ψ r, by show ψ (Φ (ψ r)) = ψ r; rw [hψinv]⟩
  have hRiso : R ≃ₗ[R] ↥(LinearMap.range π) :=
    (LinearEquiv.ofInjective ψ (Function.LeftInverse.injective hψinv)).trans
      (LinearEquiv.ofEq _ _ hrange.symm)
  -- `P₁ⁿ` is the representative of `n · p₁`
  have hcard : #(ULift.{u} (Fin n)) = ((n : ℕ) : Cardinal.{u}) := by simp
  have hle : #(ULift.{u} (Fin n)) ≤ (ℵ₀ : Cardinal.{u}) :=
    le_of_eq_of_le hcard (le_of_lt Cardinal.natCast_lt_aleph0)
  have hAeq : KMonoid.cmul (κ := ℵ₀) #(ULift.{u} (Fin n)) hle p₁
      = KMonoid.sumOf (κ := ℵ₀) hle (fun _ : ULift.{u} (Fin n) => p₁) :=
    KMonoid.cmul_eq_sumOf hle p₁
  have e : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) #(ULift.{u} (Fin n)) hle p₁)
      ≃ₗ[R] DirectSum (ULift.{u} (Fin n)) (fun _ => P) := by
    rw [hAeq]
    exact ((projClass R ℵ₀ le_rfl).rep_sumOf le_rfl hle (fun _ : ULift.{u} (Fin n) => p₁)).some
  -- both pieces are classes, and they add up
  obtain ⟨b, hb⟩ := (projClass R ℵ₀ le_rfl).exists_class_of_summand _ e hcompl
  obtain ⟨c, hc⟩ := (projClass R ℵ₀ le_rfl).exists_class_of_summand _ e hcompl.symm
  have hbunit : b = Projective.unitClass R ℵ₀ le_rfl k :=
    (projClass R ℵ₀ le_rfl).eq_of_iso
      (hb.some.trans (hRiso.symm.trans (Projective.rep_unitClass R ℵ₀ le_rfl k).some.symm))
  have hsum := (projClass R ℵ₀ le_rfl).add_eq_of_relCompl le_rfl hcompl.disjoint
    (codisjoint_iff.mp hcompl.codisjoint) hb hc ⟨e.trans Submodule.topEquiv.symm⟩
  refine ⟨c, ?_⟩
  rw [← hbunit, hsum]
  exact KMonoid.cmul_congr hcard hle (le_of_lt Cardinal.natCast_lt_aleph0) p₁


/-- **If both generators have trace ideal inside `I`, then `I = R`.**

The class of `R` is an `ℵ₀`-sum of copies of the two generators, and the trace ideal of a direct
sum is contained in the supremum of the trace ideals of the summands; `Tr(R) = R` finishes.  This
is the paper's "if `J ⊆ I` then `P₂ I = P₂`, and hence `I = R`". -/
theorem eq_top_of_traceIdeal_generators (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier))
    {I : Ideal R}
    (h₁ : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) ≤ I)
    (h₂ : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) ≤ I) : I = ⊤ := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  -- the classes whose trace ideal fits inside `I` form a `κ`-submonoid
  have hsub : KMonoid.IsKSubmonoid (ℵ₀ : Cardinal.{u})
      {a : (projClass R ℵ₀ le_rfl).carrier |
        traceIdeal R ((projClass R ℵ₀ le_rfl).rep a) ≤ I} := by
    constructor
    · show traceIdeal R ((projClass R ℵ₀ le_rfl).rep 0) ≤ I
      haveI := (projClass R ℵ₀ le_rfl).subsingleton_rep_of_eq_zero
        ((projClass R ℵ₀ le_rfl).instKMonoid_zero le_rfl)
      refine iSup_le fun f => ?_
      rintro y ⟨m, rfl⟩
      rw [Subsingleton.elim m 0, map_zero]
      exact Submodule.zero_mem I
    · intro z hz
      show traceIdeal R ((projClass R ℵ₀ le_rfl).rep
        (KMonoid.sumOf (κ := ℵ₀) (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u}))) z)) ≤ I
      rw [traceIdeal_of_iso R
        ((projClass R ℵ₀ le_rfl).rep_sumOf le_rfl (le_of_eq (mk_Idx _)) z).some]
      exact le_trans (traceIdeal_dsum_le R _) (iSup_le fun i => hz i)
  have hmem : traceIdeal R ((projClass R ℵ₀ le_rfl).rep (Projective.unitClass R ℵ₀ le_rfl k))
      ≤ I := by
    refine KMonoid.kclosure_le ?_ hsub (KMonoid.kGenerates_iff.mp hgen _)
    rintro w (rfl | rfl)
    · exact h₁
    · exact h₂
  refine top_le_iff.mp ?_
  rw [← traceIdeal_self R, ← traceIdeal_of_iso R (Projective.rep_unitClass R ℵ₀ le_rfl k).some]
  exact hmem

/-- **`Tr(P) = R` makes `ℵ₀ [R]` a summand of `ℵ₀ [P]`.**  Scale `[R] ≼ n [P]` by `ℵ₀`, using
`ℵ₀ · (n+1) = ℵ₀`. -/
theorem cmul_top_unitClass_addLe (p : (projClass R ℵ₀ le_rfl).carrier)
    (k : Idx (ℵ₀ : Cardinal.{u})) (h : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p) = ⊤) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (Projective.unitClass R ℵ₀ le_rfl k)
      ≼ KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p := by
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  obtain ⟨n, c, hc⟩ := addLe_cmul_of_traceIdeal_eq_top R p k h
  obtain ⟨t, ht⟩ : Projective.unitClass R ℵ₀ le_rfl k
      ≼ KMonoid.cmul (κ := ℵ₀) (((n + 1 : ℕ)) : Cardinal.{u})
          (le_of_lt Cardinal.natCast_lt_aleph0) p :=
    AddLe.trans ⟨c, hc⟩ (KMonoid.cmul_le_cmul _ _ (by exact_mod_cast Nat.le_succ n) p)
  have hmul : (ℵ₀ : Cardinal.{u}) * (((n + 1 : ℕ)) : Cardinal.{u}) = ℵ₀ :=
    Cardinal.mul_eq_left le_rfl (le_of_lt Cardinal.natCast_lt_aleph0)
      (by exact_mod_cast Nat.succ_ne_zero n)
  refine ⟨KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl t, ?_⟩
  rw [← KMonoid.cmul_top_distrib, ht, KMonoid.cmul_cmul le_rfl
    (le_of_lt Cardinal.natCast_lt_aleph0) (le_of_eq hmul)]
  exact KMonoid.cmul_congr hmul (le_of_eq hmul) le_rfl p

/-- **Proposition 5.4**: for a ring with non-cyclic `V^{ℵ₀}(R)` generated by `[P₁]` and `[P₂]`,
`Tr(P₂) ⊆ Tr(P₁)`, `Tr(P₁) = R` and `P₂ | P₁^{(ℵ₀)}` are equivalent.

The two classes are given as carrier elements `p₁ p₂` and their modules as `rep p₁`, `rep p₂` —
`ModuleClass` has no constructor taking a module to its class, only `rep` going the other way.

(i) ⇒ (ii) is `eq_top_of_traceIdeal_generators`, which replaces the paper's `P₂ Tr(P₁) = P₂` by
the trace ideal of a direct sum.  (ii) ⇒ (iii) is the paper's "`1 ∈ im f₁ + ⋯ + im f_k`", giving
`[R] ≼ n [P₁]` (`addLe_cmul_of_traceIdeal_eq_top`); scaling by `ℵ₀` and using that `[R]` is an
order-unit puts `[P₂]` below `ℵ₀ [P₁]`.  (iii) ⇒ (i) is the trace ideal of a summand. -/
theorem prop_5_4 (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier))
    (_hnoncyclic : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      ∀ x : (projClass R ℵ₀ le_rfl).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set (projClass R ℵ₀ le_rfl).carrier)) :
    (traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) ≤ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁)
        ↔ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤) ∧
      (traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤ ↔
        ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
          Nonempty (DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) ≃ₗ[R]
            (projClass R ℵ₀ le_rfl).rep p₂ × Q)) := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  -- the free module on `ℕ` and on `Idx ℵ₀` agree
  have hIdxNat : Idx (ℵ₀ : Cardinal.{u}) ≃ ℕ := idxEquivNats.{u}.trans Equiv.ulift
  have hfirst : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂)
      ≤ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁)
      ↔ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤ := by
    refine ⟨fun h => eq_top_of_traceIdeal_generators R p₁ p₂ hgen le_rfl h, fun h => ?_⟩
    rw [h]
    exact le_top
  refine ⟨hfirst, ⟨fun h => ?_, fun h => ?_⟩⟩
  · -- `Tr(P₁) = R` gives `ℵ₀ [R] ≼ ℵ₀ [P₁]`, hence `[P₂] ≼ ℵ₀ [P₁]`
    obtain ⟨d, hd⟩ := AddLe.trans (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k p₂)
      (cmul_top_unitClass_addLe R p₁ k h)
    -- read the relation as an isomorphism of modules
    refine ⟨(projClass R ℵ₀ le_rfl).rep d, inferInstance, inferInstance, ?_⟩
    have e1 : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p₁)
        ≃ₗ[R] DirectSum (Idx (ℵ₀ : Cardinal.{u}))
          (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) := by
      exact (rep_cmul_top_dsum R p₁).some
    have e2 : DirectSum (Idx (ℵ₀ : Cardinal.{u}))
        (fun _ => (projClass R ℵ₀ le_rfl).rep p₁)
        ≃ₗ[R] DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) :=
      DirectSum.lequivCongrLeft R hIdxNat
    have e3 : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p₁)
        ≃ₗ[R] (projClass R ℵ₀ le_rfl).rep p₂ × (projClass R ℵ₀ le_rfl).rep d := by
      rw [← hd]
      exact ((projClass R ℵ₀ le_rfl).rep_add le_rfl p₂ d).some
    exact ⟨(e2.symm.trans e1.symm).trans e3⟩
  · -- a summand of `P₁^{(ℕ)}` has a smaller trace ideal
    obtain ⟨Q, hQ₁, hQ₂, e⟩ := h
    letI := hQ₁
    letI := hQ₂
    obtain ⟨e'⟩ := e
    have s1 : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂)
        ≤ traceIdeal R (DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁)) :=
      traceIdeal_le_of_prod R
        (M := DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁))
        (N := (projClass R ℵ₀ le_rfl).rep p₂) (K := Q) e'
    have hlift : DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁)
        ≃ₗ[R] DirectSum (ULift.{u} ℕ) (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) :=
      DirectSum.lequivCongrLeft R Equiv.ulift.symm
    have s2 : traceIdeal R (DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁))
        ≤ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) := by
      rw [traceIdeal_of_iso R hlift]
      exact le_trans
        (traceIdeal_dsum_le R (fun _ : ULift.{u} ℕ => (projClass R ℵ₀ le_rfl).rep p₁))
        (iSup_le fun _ => le_rfl)
    exact hfirst.mp (le_trans s1 s2)

/-- **`ℵ₀` copies of a nonzero class are never finitely generated.**

If `rep (ℵ₀ p)` were finitely generated it would be `ℵ₀⁻`-small, so in its decomposition as
`⨁_{Idx ℵ₀} rep p` only finitely many components could ever be nonzero; but every component is
hit, so `rep p` is trivial.  This is what makes `ℵ₀ [P₁]` an admissible input to the "every
countably but not finitely generated projective is free" hypothesis. -/
theorem eq_zero_of_finite_cmul_top {p : (projClass R ℵ₀ le_rfl).carrier}
    (h : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      Module.Finite R ((projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p))) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    p = 0 := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  -- the decomposition of `ℵ₀ p`
  have e : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)
      ≃ₗ[R] DirectSum (Idx (ℵ₀ : Cardinal.{u})) (fun _ => (projClass R ℵ₀ le_rfl).rep p) := by
    exact (rep_cmul_top_dsum R p).some
  obtain ⟨s, hs, hzero⟩ := isLambdaSmall_aleph0_of_fg R _ h
    (fun _ : Idx (ℵ₀ : Cardinal.{u}) => (projClass R ℵ₀ le_rfl).rep p)
    (fun _ => inferInstance) (fun _ => inferInstance) (e : _ →ₗ[R] _)
  -- some index escapes the finite support
  have hsfin : s.Finite := Cardinal.lt_aleph0_iff_set_finite.mp hs
  haveI : Infinite (Idx (ℵ₀ : Cardinal.{u})) :=
    Cardinal.infinite_iff.mpr (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u})).symm)
  obtain ⟨i₀, hi₀⟩ := hsfin.infinite_compl.nonempty
  -- so that component of `rep p` vanishes identically
  refine (projClass R ℵ₀ le_rfl).eq_zero_of_subsingleton ⟨fun y z => ?_⟩
  have hval : ∀ w : (projClass R ℵ₀ le_rfl).rep p, w = 0 := by
    intro w
    have := hzero (e.symm (DirectSum.lof R _
      (fun _ : Idx (ℵ₀ : Cardinal.{u}) => (projClass R ℵ₀ le_rfl).rep p) i₀ w)) i₀ hi₀
    rwa [show (e : _ →ₗ[R] _) (e.symm (DirectSum.lof R _ _ i₀ w))
        = DirectSum.lof R _ (fun _ : Idx (ℵ₀ : Cardinal.{u}) =>
          (projClass R ℵ₀ le_rfl).rep p) i₀ w from e.apply_symm_apply _,
      DirectSum.component.lof_self] at this
  rw [hval y, hval z]

/-- **Proposition 5.4**, final statement: `Tr(P₁) = Tr(P₂)` exactly when every countably but not
finitely generated projective module is free.

**This corrects the scaffold twice.**  The quantifier ranged over *all* projective modules, which
makes the right-hand side false as soon as `R ≠ 0` — `R^{(ℵ₁)}` is projective and not finitely
generated, but is not free on a countable basis (axiom A1).  The paper says "any countably (non
finitely) generated projective module", so the statement is over the classes of `V^{ℵ₀}(R)`, which
are exactly those.  And, as in Theorem 5.3, hereditariness is replaced by
`EveryProjectiveIsSumOfFG R`: the proof needs `P₁` and `P₂` finitely generated, which the paper
gets from Lemma 5.1 through the quoted Corollary 4.6.

Forward: both traces are `R`, so `ℵ₀ [P₁] = ℵ₀ [R] = ℵ₀ [P₂]` by Lemma 2.14.  A class that is not
finitely generated cannot have a finite form — `P₁` and `P₂` are finitely generated by
`mem_of_divisorClosed_of_generates` — so its form has an infinite coefficient, and Lemma 2.14
collapses it to `ℵ₀ [R]`, which is free.  Backward: `ℵ₀ [P₁]` is never finitely generated
(`eq_zero_of_finite_cmul_top`), so it is free, and a free module on a nonempty basis has trace
ideal `R`. -/
theorem prop_5_4_hereditary (hfg : EveryProjectiveIsSumOfFG R)
    (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier))
    (hnoncyclic : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      ∀ x : (projClass R ℵ₀ le_rfl).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set (projClass R ℵ₀ le_rfl).carrier)) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁)
        = traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) ↔
      ∀ q : (projClass R ℵ₀ le_rfl).carrier, ¬ Module.Finite R ((projClass R ℵ₀ le_rfl).rep q) →
        ∃ ι : Type u, #ι ≤ ℵ₀ ∧
          Nonempty ((projClass R ℵ₀ le_rfl).rep q ≃ₗ[R] DirectSum ι (fun _ => R)) := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    ((projClass R ℵ₀ le_rfl).lambdaSmallPart_isLSubset le_rfl ℵ₀ Cardinal.isRegular_aleph0 le_rfl)
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  have hgen' : KMonoid.KGenerates (ℵ₀ : Cardinal.{u})
      ({p₂, p₁} : Set (projClass R ℵ₀ le_rfl).carrier) := by rwa [Set.pair_comm]
  have hWsub := (projClass R ℵ₀ le_rfl).lambdaSmallPart_isLSubset le_rfl ℵ₀
    Cardinal.isRegular_aleph0 le_rfl
  -- both generators are finitely generated, by the paper's parenthetical
  have hWsat : ∀ a ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀,
      ∀ b c : (projClass R ℵ₀ le_rfl).carrier, a = b + c →
      b ∈ (projClass R ℵ₀ le_rfl).lambdaSmallPart ℵ₀ :=
    fun a ha b c habc =>
      (projClass R ℵ₀ le_rfl).lambdaSmallPart_summand le_rfl ℵ₀ a ha b ⟨c, habc.symm⟩
  obtain ⟨hp₁W, hp₂W⟩ := mem_of_divisorClosed_of_generates p₁ p₂ hWsat
    ((corollary_4_5_three.{u, u} R ℵ₀ le_rfl hfg).1.kGenerates_coe) hgen hnoncyclic
  -- `V(R)` is closed under binary sums and finite multiples
  constructor
  · -- `Tr(P₁) = Tr(P₂)` forces both to be `R`, and every infinite form to be `ℵ₀ [R]`
    intro h
    have htop₁ : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤ :=
      (prop_5_4 R p₁ p₂ hgen hnoncyclic).1.mp (le_of_eq h.symm)
    have htop₂ : traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) = ⊤ :=
      (prop_5_4 R p₂ p₁ hgen' hnoncyclic).1.mp (le_of_eq h)
    have hcollapse : ∀ p : (projClass R ℵ₀ le_rfl).carrier,
        traceIdeal R ((projClass R ℵ₀ le_rfl).rep p) = ⊤ →
        KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p
          = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (Projective.unitClass R ℵ₀ le_rfl k) := by
      intro p hp
      obtain ⟨w, hw⟩ := cmul_top_unitClass_addLe R p k hp
      exact KMonoid.eq_cmul_top_of_add (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k) w hw.symm
    have hR₁ := hcollapse p₁ htop₁
    have hR₂ := hcollapse p₂ htop₂
    intro q hq
    obtain ⟨F, hF⟩ := exists_form p₁ p₂ hgen q
    -- a finite form would make `q` finitely generated
    have hinf : F.1 = ⊤ ∨ F.2 = ⊤ := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨a, ha⟩ : ∃ a : ℕ, F.1 = (a : ℕ∞) := ⟨F.1.toNat, (ENat.natCast_toNat hcon.1).symm⟩
      obtain ⟨b, hb⟩ : ∃ b : ℕ, F.2 = (b : ℕ∞) := ⟨F.2.toNat, (ENat.natCast_toNat hcon.2).symm⟩
      refine hq (finite_of_isLambdaSmall_aleph0 R ℵ₀ q.out
        ((projClass R ℵ₀ le_rfl).isLambdaSmall_of_mem ?_))
      rw [← hF, eval, ha, hb, ecmul_natCast, ecmul_natCast]
      exact hWsub.add_mem le_rfl (hWsub.nsmul_mem le_rfl hp₁W a)
        (hWsub.nsmul_mem le_rfl hp₂W b)
    -- an infinite form collapses to `ℵ₀ [R]`
    have hq' : q = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (Projective.unitClass R ℵ₀ le_rfl k) := by
      rcases hinf with hc | hc
      · refine KMonoid.eq_cmul_top_of_add (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k)
          (ecmul F.2 p₂) ?_
        rw [← hF, eval, hc, ecmul_top, hR₁]
      · refine KMonoid.eq_cmul_top_of_add (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k)
          (ecmul F.1 p₁) ?_
        rw [← hF, eval, hc, ecmul_top, hR₂, add_comm]
    refine ⟨Idx (ℵ₀ : Cardinal.{u}), le_of_eq (mk_Idx _), ?_⟩
    rw [hq']
    exact ⟨(Projective.rep_cmul_unitClass R ℵ₀ le_rfl le_rfl k).some⟩
  · -- freeness of `ℵ₀ [P₁]` and `ℵ₀ [P₂]` makes both trace ideals `R`
    intro h
    obtain ⟨hne₁, hne₂⟩ := ne_zero_of_not_cyclic p₁ p₂ hgen hnoncyclic
    have key : ∀ p : (projClass R ℵ₀ le_rfl).carrier, p ≠ 0 →
        traceIdeal R ((projClass R ℵ₀ le_rfl).rep p) = ⊤ := by
      intro p hp
      obtain ⟨ι, hι, e⟩ := h (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)
        (fun hfin => hp (eq_zero_of_finite_cmul_top R hfin))
      -- the basis is nonempty, since `ℵ₀ p ≠ 0`
      have hιne : Nonempty ι := by
        by_contra hcon
        rw [not_nonempty_iff] at hcon
        refine hp ?_
        have hsub : Subsingleton ((projClass R ℵ₀ le_rfl).rep
            (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)) := Equiv.subsingleton e.some.toEquiv
        have hzero : KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p = 0 :=
          ((projClass R ℵ₀ le_rfl).eq_zero_of_subsingleton hsub).trans
            ((projClass R ℵ₀ le_rfl).instKMonoid_zero le_rfl).symm
        obtain ⟨w, hw⟩ : p ≼ KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p := by
          refine ⟨KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p, ?_⟩
          exact KMonoid.add_cmul_top_self (ℵ₀ : Cardinal.{u}) _ p
        rw [hzero] at hw
        exact (KMonoid.isConical (ℵ₀ : Cardinal.{u}) _ p w hw).1
      obtain ⟨i₀⟩ := hιne
      -- a free module on a nonempty basis has trace ideal `R`
      have hfree : traceIdeal R (DirectSum ι (fun _ => R)) = ⊤ := by
        refine eq_top_iff.mpr fun y _ => ?_
        refine le_traceIdeal R _ (DirectSum.component R ι (fun _ => R) i₀) ?_
        exact ⟨DirectSum.lof R ι (fun _ => R) i₀ y, by rw [DirectSum.component.lof_self]⟩
      have hcm : traceIdeal R ((projClass R ℵ₀ le_rfl).rep
          (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)) = ⊤ := by
        rw [traceIdeal_of_iso R e.some]
        exact hfree
      have hdec : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)
          ≃ₗ[R] DirectSum (Idx (ℵ₀ : Cardinal.{u}))
            (fun _ => (projClass R ℵ₀ le_rfl).rep p) := by
          exact (rep_cmul_top_dsum R p).some
      refine top_le_iff.mp ?_
      rw [← hcm, traceIdeal_of_iso R hdec]
      exact le_trans (traceIdeal_dsum_le R (fun _ : Idx (ℵ₀ : Cardinal.{u}) =>
        (projClass R ℵ₀ le_rfl).rep p)) (iSup_le fun _ => le_rfl)
    rw [key p₁ hne₁, key p₂ hne₂]

/-- **`[P₂] ≼ ℵ₀ [P₁]` forces `Tr(P₁) = R`**, by the second half of Proposition 5.4. -/
theorem traceIdeal_eq_top_of_addLe (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier))
    (hnoncyclic : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      ∀ x : (projClass R ℵ₀ le_rfl).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set (projClass R ℵ₀ le_rfl).carrier))
    (h : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      p₂ ≼ KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p₁) :
    traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤ := by
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  obtain ⟨c, hc⟩ := h
  refine (prop_5_4 R p₁ p₂ hgen hnoncyclic).2.mpr
    ⟨(projClass R ℵ₀ le_rfl).rep c, inferInstance, inferInstance, ?_⟩
  have e1 := (rep_cmul_top_dsum R p₁).some
  have e2 : DirectSum (Idx (ℵ₀ : Cardinal.{u})) (fun _ => (projClass R ℵ₀ le_rfl).rep p₁)
      ≃ₗ[R] DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) :=
    DirectSum.lequivCongrLeft R (idxEquivNats.{u}.trans Equiv.ulift)
  have e3 : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p₁)
      ≃ₗ[R] (projClass R ℵ₀ le_rfl).rep p₂ × (projClass R ℵ₀ le_rfl).rep c := by
    rw [← hc]
    exact ((projClass R ℵ₀ le_rfl).rep_add le_rfl p₂ c).some
  exact ⟨(e2.symm.trans e1.symm).trans e3⟩

/-- **If every countably but not finitely generated projective is free, `ℵ₀ [P] = ℵ₀ [R]`** for
every nonzero class `[P]`: `ℵ₀ [P]` is never finitely generated, so it is free on a basis that
cannot be finite, hence on a countably infinite one. -/
theorem cmul_top_eq_unitClass_of_free (k : Idx (ℵ₀ : Cardinal.{u}))
    (p : (projClass R ℵ₀ le_rfl).carrier)
    (hp : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl; p ≠ 0)
    (hfree : ∀ q : (projClass R ℵ₀ le_rfl).carrier, ¬ Module.Finite R ((projClass R ℵ₀ le_rfl).rep q)
      → ∃ ι : Type u, #ι ≤ ℵ₀ ∧
        Nonempty ((projClass R ℵ₀ le_rfl).rep q ≃ₗ[R] DirectSum ι (fun _ => R))) :
    letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p
      = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (Projective.unitClass R ℵ₀ le_rfl k) := by
  classical
  letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
  have hnf : ¬ Module.Finite R ((projClass R ℵ₀ le_rfl).rep
      (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)) := fun hfin => hp (eq_zero_of_finite_cmul_top R hfin)
  obtain ⟨ι, hι, e⟩ := hfree _ hnf
  -- the basis cannot be finite
  haveI : Infinite ι := by
    by_contra hcon
    rw [not_infinite_iff_finite] at hcon
    haveI := hcon
    haveI := Fintype.ofFinite ι
    refine hnf (Module.Finite.equiv (e.some.trans (DirectSum.linearEquivFunOnFintype R ι
      (fun _ => R))).symm)
  have hmk : #ι = (ℵ₀ : Cardinal.{u}) :=
    le_antisymm hι (Cardinal.infinite_iff.mp inferInstance)
  obtain ⟨ε⟩ : Nonempty (ι ≃ Idx (ℵ₀ : Cardinal.{u})) :=
    Cardinal.eq.mp (hmk.trans (mk_Idx (ℵ₀ : Cardinal.{u})).symm)
  have efin : (projClass R ℵ₀ le_rfl).rep (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl p)
      ≃ₗ[R] (projClass R ℵ₀ le_rfl).rep
        (KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (Projective.unitClass R ℵ₀ le_rfl k)) :=
    e.some.trans ((DirectSum.lequivCongrLeft R ε).trans
      (Projective.rep_cmul_unitClass R ℵ₀ le_rfl le_rfl k).some.symm)
  exact (projClass R ℵ₀ le_rfl).eq_of_iso efin

end Prop54

end TwoGen

end KappaMonoid
