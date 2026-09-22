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

/-! ### From a full trace ideal to a divisibility in `V^{ℵ₀}(R)`

`Tr(P) = R` says that finitely many homomorphisms `P → R` have images summing to `R`; that makes
`R` a summand of a finite power of `P`, which is the divisibility `[R] ≼ n [P]` these lemmas
extract. -/

/-- **`Tr(P₁) = R` makes `R` a direct summand of a finite power of `P₁`**, hence `[R] ≼ n [P₁]`
in `V^{ℵ₀}(R)`.

The finitely many functionals of `exists_sum_eq_one_of_traceIdeal_eq_top` assemble into an
epimorphism `P₁ⁿ ↠ R`; it splits because `R` is projective, and the resulting idempotent cuts
`P₁ⁿ` into `R` and a complement, both of which are again classes because `V^{ℵ₀}(R)` is closed
under direct summands. -/
theorem addLe_cmul_of_traceIdeal_eq_top (p₁ : V(R).carrier)
    (k : Idx (ℵ₀ : Cardinal.{u}))
    (h : traceIdeal R (V(R).rep p₁) = ⊤) :
    ∃ n : ℕ, Projective.unitClass R ℵ₀ le_rfl k
      ≼ KMonoid.cmul (κ := ℵ₀) ((n : ℕ) : Cardinal.{u})
          (le_of_lt Cardinal.natCast_lt_aleph0) p₁ := by
  classical
  set P := V(R).rep p₁ with hP
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
  have e : V(R).rep (KMonoid.cmul (κ := ℵ₀) #(ULift.{u} (Fin n)) hle p₁)
      ≃ₗ[R] DirectSum (ULift.{u} (Fin n)) (fun _ => P) := by
    rw [hAeq]
    exact (V(R).rep_sumOf le_rfl hle (fun _ : ULift.{u} (Fin n) => p₁)).some
  -- both pieces are classes, and they add up
  obtain ⟨b, hb⟩ := V(R).exists_class_of_summand _ e hcompl
  obtain ⟨c, hc⟩ := V(R).exists_class_of_summand _ e hcompl.symm
  have hbunit : b = Projective.unitClass R ℵ₀ le_rfl k :=
    V(R).eq_of_iso
      (hb.some.trans (hRiso.symm.trans (Projective.rep_unitClass R ℵ₀ le_rfl k).some.symm))
  have hsum := V(R).add_eq_of_relCompl le_rfl hcompl.disjoint
    (codisjoint_iff.mp hcompl.codisjoint) hb hc ⟨e.trans Submodule.topEquiv.symm⟩
  refine ⟨c, ?_⟩
  rw [← hbunit, hsum]
  exact KMonoid.cmul_congr hcard hle (le_of_lt Cardinal.natCast_lt_aleph0) p₁


/-- **If both generators have trace ideal inside `I`, then `I = R`.**

The class of `R` is an `ℵ₀`-sum of copies of the two generators, and the trace ideal of a direct
sum is contained in the supremum of the trace ideals of the summands; `Tr(R) = R` finishes.  This
is the paper's "if `J ⊆ I` then `P₂ I = P₂`, and hence `I = R`". -/
theorem eq_top_of_traceIdeal_generators (p₁ p₂ : V(R).carrier)
    (hgen : letI := V(R).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set V(R).carrier))
    {I : Ideal R}
    (h₁ : traceIdeal R (V(R).rep p₁) ≤ I)
    (h₂ : traceIdeal R (V(R).rep p₂) ≤ I) : I = ⊤ := by
  classical
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  -- the classes whose trace ideal fits inside `I` form a `κ`-submonoid
  have hsub : KMonoid.IsKSubmonoid (ℵ₀ : Cardinal.{u})
      {a : V(R).carrier |
        traceIdeal R (V(R).rep a) ≤ I} := by
    constructor
    · show traceIdeal R (V(R).rep 0) ≤ I
      have := V(R).subsingleton_rep_of_eq_zero
        (V(R).instKMonoid_zero le_rfl)
      refine iSup_le fun f => ?_
      rintro y ⟨m, rfl⟩
      rw [Subsingleton.elim m 0, map_zero]
      exact Submodule.zero_mem I
    · intro z hz
      show traceIdeal R (V(R).rep
        (KMonoid.sumOf (κ := ℵ₀) (le_of_eq (mk_Idx (ℵ₀ : Cardinal.{u}))) z)) ≤ I
      rw [traceIdeal_of_iso R
        (V(R).rep_sumOf le_rfl (le_of_eq (mk_Idx _)) z).some]
      exact le_trans (traceIdeal_dsum_le R _) (iSup_le fun i => hz i)
  have hmem : traceIdeal R (V(R).rep (Projective.unitClass R ℵ₀ le_rfl k))
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
theorem cmul_top_unitClass_addLe (p : V(R).carrier)
    (k : Idx (ℵ₀ : Cardinal.{u})) (h : traceIdeal R (V(R).rep p) = ⊤) :
    ℵ₀∙(Projective.unitClass R ℵ₀ le_rfl k)
      ≼ ℵ₀∙p := by
  obtain ⟨n, c, hc⟩ := addLe_cmul_of_traceIdeal_eq_top R p k h
  obtain ⟨t, ht⟩ : Projective.unitClass R ℵ₀ le_rfl k
      ≼ KMonoid.cmul (κ := ℵ₀) (((n + 1 : ℕ)) : Cardinal.{u})
          (le_of_lt Cardinal.natCast_lt_aleph0) p :=
    AddLe.trans ⟨c, hc⟩ (KMonoid.cmul_le_cmul _ _ (by exact_mod_cast Nat.le_succ n) p)
  have hmul : (ℵ₀ : Cardinal.{u}) * (((n + 1 : ℕ)) : Cardinal.{u}) = ℵ₀ :=
    Cardinal.mul_eq_left le_rfl (le_of_lt Cardinal.natCast_lt_aleph0)
      (by exact_mod_cast Nat.succ_ne_zero n)
  refine ⟨ℵ₀∙t, ?_⟩
  rw [← KMonoid.cmul_top_distrib, ht, KMonoid.cmul_cmul le_rfl
    (le_of_lt Cardinal.natCast_lt_aleph0) (le_of_eq hmul)]
  exact KMonoid.cmul_congr hmul (le_of_eq hmul) le_rfl p

/-! ### Proposition 5.4 -/

/-- **Proposition 5.4**: for a ring with non-cyclic `V^{ℵ₀}(R)` generated by `[P₁]` and `[P₂]`,
`Tr(P₂) ⊆ Tr(P₁)`, `Tr(P₁) = R` and `P₂ | P₁^{(ℵ₀)}` are equivalent.

The two classes are given as carrier elements `p₁ p₂` and their modules as `rep p₁`, `rep p₂` —
`ModuleClass` has no constructor taking a module to its class, only `rep` going the other way.

(i) ⇒ (ii) is `eq_top_of_traceIdeal_generators`, which replaces the paper's `P₂ Tr(P₁) = P₂` by
the trace ideal of a direct sum.  (ii) ⇒ (iii) is the paper's "`1 ∈ im f₁ + ⋯ + im f_k`", giving
`[R] ≼ n [P₁]` (`addLe_cmul_of_traceIdeal_eq_top`); scaling by `ℵ₀` and using that `[R]` is an
order-unit puts `[P₂]` below `ℵ₀ [P₁]`.  (iii) ⇒ (i) is the trace ideal of a summand. -/
theorem prop_5_4 (p₁ p₂ : V(R).carrier)
    (hgen : letI := V(R).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set V(R).carrier))
    (_hnoncyclic : letI := V(R).instKMonoid le_rfl
      ∀ x : V(R).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set V(R).carrier)) :
    (traceIdeal R (V(R).rep p₂) ≤ traceIdeal R (V(R).rep p₁)
        ↔ traceIdeal R (V(R).rep p₁) = ⊤) ∧
      (traceIdeal R (V(R).rep p₁) = ⊤ ↔
        ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
          Nonempty (DirectSum ℕ (fun _ => V(R).rep p₁) ≃ₗ[R]
            V(R).rep p₂ × Q)) := by
  classical
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  -- the free module on `ℕ` and on `Idx ℵ₀` agree
  have hIdxNat : Idx (ℵ₀ : Cardinal.{u}) ≃ ℕ := idxEquivNats.{u}.trans Equiv.ulift
  have hfirst : traceIdeal R (V(R).rep p₂)
      ≤ traceIdeal R (V(R).rep p₁)
      ↔ traceIdeal R (V(R).rep p₁) = ⊤ := by
    refine ⟨fun h => eq_top_of_traceIdeal_generators R p₁ p₂ hgen le_rfl h, fun h => ?_⟩
    rw [h]
    exact le_top
  refine ⟨hfirst, ⟨fun h => ?_, fun h => ?_⟩⟩
  · -- `Tr(P₁) = R` gives `ℵ₀ [R] ≼ ℵ₀ [P₁]`, hence `[P₂] ≼ ℵ₀ [P₁]`
    obtain ⟨d, hd⟩ := AddLe.trans (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k p₂)
      (cmul_top_unitClass_addLe R p₁ k h)
    -- read the relation as an isomorphism of modules
    refine ⟨V(R).rep d, inferInstance, inferInstance, ?_⟩
    have e1 : V(R).rep (ℵ₀∙p₁)
        ≃ₗ[R] DirectSum (Idx (ℵ₀ : Cardinal.{u}))
          (fun _ => V(R).rep p₁) := by
      exact (rep_cmul_top_dsum R p₁).some
    have e2 : DirectSum (Idx (ℵ₀ : Cardinal.{u}))
        (fun _ => V(R).rep p₁)
        ≃ₗ[R] DirectSum ℕ (fun _ => V(R).rep p₁) :=
      DirectSum.lequivCongrLeft R hIdxNat
    have e3 : V(R).rep (ℵ₀∙p₁)
        ≃ₗ[R] V(R).rep p₂ × V(R).rep d := by
      rw [← hd]
      exact (V(R).rep_add le_rfl p₂ d).some
    exact ⟨(e2.symm.trans e1.symm).trans e3⟩
  · -- a summand of `P₁^{(ℕ)}` has a smaller trace ideal
    obtain ⟨Q, hQ₁, hQ₂, e⟩ := h
    let := hQ₁
    let := hQ₂
    obtain ⟨e'⟩ := e
    have s1 : traceIdeal R (V(R).rep p₂)
        ≤ traceIdeal R (DirectSum ℕ (fun _ => V(R).rep p₁)) :=
      traceIdeal_le_of_prod R
        (M := DirectSum ℕ (fun _ => V(R).rep p₁))
        (N := V(R).rep p₂) (K := Q) e'
    have hlift : DirectSum ℕ (fun _ => V(R).rep p₁)
        ≃ₗ[R] DirectSum (ULift.{u} ℕ) (fun _ => V(R).rep p₁) :=
      DirectSum.lequivCongrLeft R Equiv.ulift.symm
    have s2 : traceIdeal R (DirectSum ℕ (fun _ => V(R).rep p₁))
        ≤ traceIdeal R (V(R).rep p₁) := by
      rw [traceIdeal_of_iso R hlift]
      exact le_trans
        (traceIdeal_dsum_le R (fun _ : ULift.{u} ℕ => V(R).rep p₁))
        (iSup_le fun _ => le_rfl)
    exact hfirst.mp (le_trans s1 s2)

/-! ### The hereditary half: `Tr(P₁) = Tr(P₂)` and freeness

The second statement of Proposition 5.4 identifies equality of the two trace ideals with freeness
of every countably but not finitely generated projective.  The ingredients are that `ℵ₀[P]` is
never finitely generated for `P ≠ 0`, and that a free `P^{(ℵ₀)}` forces `Tr(P) = R`. -/

/-- **A free `P^{(ℵ₀)}` forces `Tr(P) = R`.**  The basis is nonempty because `ℵ₀ [P] ≠ 0`, so the
free module has full trace ideal; and the trace ideal of `P^{(ℵ₀)}` is contained in that of `P`,
being a direct sum of copies of it. -/
theorem traceIdeal_eq_top_of_iso_free {p : V(R).carrier}
    (hp : letI := V(R).instKMonoid le_rfl; p ≠ 0) {ι : Type u}
    (e : letI := V(R).instKMonoid le_rfl
      Nonempty (V(R).rep (ℵ₀∙p)
        ≃ₗ[R] DirectSum ι (fun _ => R))) :
    traceIdeal R (V(R).rep p) = ⊤ := by
  classical
  -- the basis is nonempty, since `ℵ₀ p ≠ 0`
  have hιne : Nonempty ι := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    refine hp ?_
    have hsub : Subsingleton (V(R).rep
        (ℵ₀∙p)) := Equiv.subsingleton e.some.toEquiv
    have hzero : ℵ₀∙p = 0 :=
      (V(R).eq_zero_of_subsingleton hsub).trans
        (V(R).instKMonoid_zero le_rfl).symm
    obtain ⟨w, hw⟩ : p ≼ ℵ₀∙p := by
      refine ⟨ℵ₀∙p, ?_⟩
      exact KMonoid.add_cmul_top_self (ℵ₀ : Cardinal.{u}) _ p
    rw [hzero] at hw
    exact (KMonoid.isConical (ℵ₀ : Cardinal.{u}) _ p w hw).1
  obtain ⟨i₀⟩ := hιne
  -- a free module on a nonempty basis has trace ideal `R`
  have hfree : traceIdeal R (DirectSum ι (fun _ => R)) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    refine le_traceIdeal R _ (DirectSum.component R ι (fun _ => R) i₀) ?_
    exact ⟨DirectSum.lof R ι (fun _ => R) i₀ y, by rw [DirectSum.component.lof_self]⟩
  have hcm : traceIdeal R (V(R).rep
      (ℵ₀∙p)) = ⊤ := by
    rw [traceIdeal_of_iso R e.some]
    exact hfree
  have hdec : V(R).rep (ℵ₀∙p)
      ≃ₗ[R] DirectSum (Idx (ℵ₀ : Cardinal.{u}))
        (fun _ => V(R).rep p) := by
      exact (rep_cmul_top_dsum R p).some
  refine top_le_iff.mp ?_
  rw [← hcm, traceIdeal_of_iso R hdec]
  exact le_trans (traceIdeal_dsum_le R (fun _ : Idx (ℵ₀ : Cardinal.{u}) =>
    V(R).rep p)) (iSup_le fun _ => le_rfl)


/-- **Proposition 5.4**, clause (iv): `Tr(P₁) = R` if and only if `P₁^{(ℵ₀)}` is free.

Paper proof: from `Tr(P₁) = R` the class `ℵ₀ [R]` is a summand of `ℵ₀ [P₁]`
(`cmul_top_unitClass_addLe`), and `[R]` is an order-unit, so Lemma 2.8(2) collapses `ℵ₀ [P₁]` to
`ℵ₀ [R]` — which is represented by `R^{(ℵ₀)}`.  Conversely a free `P₁^{(ℵ₀)}` has full trace ideal
(`traceIdeal_eq_top_of_iso_free`), the basis being nonempty because `[P₁] ≠ 0`.

Together with `prop_5_4` this is the paper's four-way equivalence
`Tr(P₂) ⊆ Tr(P₁)` ⟺ `Tr(P₁) = R` ⟺ `P₂ | P₁^{(ℵ₀)}` ⟺ `P₁^{(ℵ₀)}` free. -/
theorem prop_5_4_free (p₁ p₂ : V(R).carrier)
    (hgen : letI := V(R).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set V(R).carrier))
    (hnoncyclic : letI := V(R).instKMonoid le_rfl
      ∀ x : V(R).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set V(R).carrier)) :
    traceIdeal R (V(R).rep p₁) = ⊤ ↔
      ∃ ι : Type u, #ι ≤ ℵ₀ ∧
        letI := V(R).instKMonoid le_rfl
        Nonempty (V(R).rep (ℵ₀∙p₁) ≃ₗ[R] DirectSum ι (fun _ => R)) := by
  classical
  let := V(R).instKMonoid le_rfl
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  constructor
  · intro h
    obtain ⟨w, hw⟩ := cmul_top_unitClass_addLe R p₁ k h
    have hcollapse : ℵ₀∙p₁ = ℵ₀∙(Projective.unitClass R ℵ₀ le_rfl k) :=
      KMonoid.eq_cmul_top_of_add (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k) w hw.symm
    refine ⟨Idx (ℵ₀ : Cardinal.{u}), le_of_eq (mk_Idx _), ?_⟩
    rw [hcollapse]
    exact ⟨(Projective.rep_cmul_unitClass R ℵ₀ le_rfl le_rfl k).some⟩
  · rintro ⟨ι, -, e⟩
    exact traceIdeal_eq_top_of_iso_free R (ne_zero_of_not_cyclic p₁ p₂ hgen hnoncyclic).1 e

/-- **Proposition 5.4**, final statement: `Tr(P₁) = Tr(P₂)` exactly when every countably but not
finitely generated projective module is free.

**Two corrections to the paper's transcription.**  Quantified over *all* projective modules the
right-hand side is false as soon as `R ≠ 0` — `R^{(ℵ₁)}` is projective and not finitely generated,
but is not free on a countable basis (invariance of infinite rank).  The paper says "any countably
(non finitely) generated projective module", so the statement is over the classes of `V^{ℵ₀}(R)`,
which are exactly those.  And hereditariness — the paper's hypothesis here — is *weakened* to
`EveryProjectiveIsSumOfFG R`: what the proof needs is that `P₁` and `P₂` are finitely generated,
which the paper gets from Lemma 5.1 through Corollary 4.6, and that is exactly this hypothesis.
Albrecht's theorem (`ForMathlib/Albrecht.lean`) says hereditary rings have it, so the statement
here implies the paper's; it is also the form Corollary 5.5 needs, since the paper states those
for this class of rings rather than for hereditary ones.

Forward: both traces are `R`, so `ℵ₀ [P₁] = ℵ₀ [R] = ℵ₀ [P₂]` by Lemma 2.14.  A class that is not
finitely generated cannot have a finite form — `P₁` and `P₂` are finitely generated by
`mem_of_divisorClosed_of_generates` — so its form has an infinite coefficient, and Lemma 2.14
collapses it to `ℵ₀ [R]`, which is free.  Backward: `ℵ₀ [P₁]` is never finitely generated
(`eq_zero_of_finite_cmul_top`), so it is free, and a free module on a nonempty basis has trace
ideal `R`. -/
theorem prop_5_4_hereditary (hfg : EveryProjectiveIsSumOfFG R)
    (p₁ p₂ : V(R).carrier)
    (hgen : letI := V(R).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set V(R).carrier))
    (hnoncyclic : letI := V(R).instKMonoid le_rfl
      ∀ x : V(R).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set V(R).carrier)) :
    traceIdeal R (V(R).rep p₁)
        = traceIdeal R (V(R).rep p₂) ↔
      ∀ q : V(R).carrier, ¬ Module.Finite R (V(R).rep q) →
        ∃ ι : Type u, #ι ≤ ℵ₀ ∧
          Nonempty (V(R).rep q ≃ₗ[R] DirectSum ι (fun _ => R)) := by
  classical
  let := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (V(R).lambdaGenPart_isLSubset le_rfl ℵ₀ Cardinal.isRegular_aleph0 (Order.le_succ ℵ₀))
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  have hgen' : KMonoid.KGenerates (ℵ₀ : Cardinal.{u})
      ({p₂, p₁} : Set V(R).carrier) := by rwa [Set.pair_comm]
  have hWsub := V(R).lambdaGenPart_isLSubset le_rfl ℵ₀
    Cardinal.isRegular_aleph0 (Order.le_succ ℵ₀)
  -- both generators are finitely generated, by the paper's parenthetical
  have hWsat : ∀ a ∈ V(R).lambdaGenPart ℵ₀,
      ∀ b c : V(R).carrier, a = b + c →
      b ∈ V(R).lambdaGenPart ℵ₀ :=
    fun a ha b c habc =>
      V(R).lambdaGenPart_summand le_rfl ℵ₀ a ha b ⟨c, habc.symm⟩
  obtain ⟨hp₁W, hp₂W⟩ := mem_of_divisorClosed_of_generates p₁ p₂ hWsat
    ((corollary_4_5_three.{u, u} R ℵ₀ le_rfl hfg).1.kGenerates_coe) hgen hnoncyclic
  -- `V(R)` is closed under binary sums and finite multiples
  constructor
  · -- `Tr(P₁) = Tr(P₂)` forces both to be `R`, and every infinite form to be `ℵ₀ [R]`
    intro h
    have htop₁ : traceIdeal R (V(R).rep p₁) = ⊤ :=
      (prop_5_4 R p₁ p₂ hgen hnoncyclic).1.mp (le_of_eq h.symm)
    have htop₂ : traceIdeal R (V(R).rep p₂) = ⊤ :=
      (prop_5_4 R p₂ p₁ hgen' hnoncyclic).1.mp (le_of_eq h)
    have hcollapse : ∀ p : V(R).carrier,
        traceIdeal R (V(R).rep p) = ⊤ →
        ℵ₀∙p
          = ℵ₀∙(Projective.unitClass R ℵ₀ le_rfl k) := by
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
      push Not at hcon
      obtain ⟨a, ha⟩ : ∃ a : ℕ, F.1 = (a : ℕ∞) := ⟨F.1.toNat, (ENat.natCast_toNat hcon.1).symm⟩
      obtain ⟨b, hb⟩ : ∃ b : ℕ, F.2 = (b : ℕ∞) := ⟨F.2.toNat, (ENat.natCast_toNat hcon.2).symm⟩
      refine hq (IsLambdaGenerated.finite_aleph0 (V(R).isLambdaGenerated_of_mem ?_))
      rw [← hF, eval, ha, hb, ecmul_natCast, ecmul_natCast]
      exact hWsub.add_mem le_rfl (hWsub.nsmul_mem le_rfl hp₁W a)
        (hWsub.nsmul_mem le_rfl hp₂W b)
    -- an infinite form collapses to `ℵ₀ [R]`
    have hq' : q = ℵ₀∙(Projective.unitClass R ℵ₀ le_rfl k) := by
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
    have key : ∀ p : V(R).carrier, p ≠ 0 →
        traceIdeal R (V(R).rep p) = ⊤ := by
      intro p hp
      obtain ⟨ι, hι, e⟩ := h (ℵ₀∙p)
        (fun hfin => hp (eq_zero_of_finite_cmul_top R hfin))
      exact traceIdeal_eq_top_of_iso_free R hp e
    rw [key p₁ hne₁, key p₂ hne₂]

/-! ### Consequences used in Corollary 5.5 -/

/-- **`[P₂] ≼ ℵ₀ [P₁]` forces `Tr(P₁) = R`**, by the second half of Proposition 5.4. -/
theorem traceIdeal_eq_top_of_addLe (p₁ p₂ : V(R).carrier)
    (hgen : letI := V(R).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set V(R).carrier))
    (hnoncyclic : letI := V(R).instKMonoid le_rfl
      ∀ x : V(R).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set V(R).carrier))
    (h : letI := V(R).instKMonoid le_rfl
      p₂ ≼ ℵ₀∙p₁) :
    traceIdeal R (V(R).rep p₁) = ⊤ := by
  obtain ⟨c, hc⟩ := h
  refine (prop_5_4 R p₁ p₂ hgen hnoncyclic).2.mpr
    ⟨V(R).rep c, inferInstance, inferInstance, ?_⟩
  have e1 := (rep_cmul_top_dsum R p₁).some
  have e2 : DirectSum (Idx (ℵ₀ : Cardinal.{u})) (fun _ => V(R).rep p₁)
      ≃ₗ[R] DirectSum ℕ (fun _ => V(R).rep p₁) :=
    DirectSum.lequivCongrLeft R (idxEquivNats.{u}.trans Equiv.ulift)
  have e3 : V(R).rep (ℵ₀∙p₁)
      ≃ₗ[R] V(R).rep p₂ × V(R).rep c := by
    rw [← hc]
    exact (V(R).rep_add le_rfl p₂ c).some
  exact ⟨(e2.symm.trans e1.symm).trans e3⟩

/-- **If every countably but not finitely generated projective is free, `ℵ₀ [P] = ℵ₀ [R]`** for
every nonzero class `[P]`: `ℵ₀ [P]` is never finitely generated, so it is free on a basis that
cannot be finite, hence on a countably infinite one. -/
theorem cmul_top_eq_unitClass_of_free (k : Idx (ℵ₀ : Cardinal.{u}))
    (p : V(R).carrier)
    (hp : letI := V(R).instKMonoid le_rfl; p ≠ 0)
    (hfree : ∀ q : V(R).carrier, ¬ Module.Finite R (V(R).rep q)
      → ∃ ι : Type u, #ι ≤ ℵ₀ ∧
        Nonempty (V(R).rep q ≃ₗ[R] DirectSum ι (fun _ => R))) :
    ℵ₀∙p
      = ℵ₀∙(Projective.unitClass R ℵ₀ le_rfl k) := by
  classical
  have hnf : ¬ Module.Finite R (V(R).rep
      (ℵ₀∙p)) := fun hfin => hp (eq_zero_of_finite_cmul_top R hfin)
  obtain ⟨ι, hι, e⟩ := hfree _ hnf
  -- the basis cannot be finite
  have : Infinite ι := by
    by_contra hcon
    rw [not_infinite_iff_finite] at hcon
    have := hcon
    have := Fintype.ofFinite ι
    refine hnf (Module.Finite.equiv (e.some.trans (DirectSum.linearEquivFunOnFintype R ι
      (fun _ => R))).symm)
  have hmk : #ι = (ℵ₀ : Cardinal.{u}) :=
    le_antisymm hι (Cardinal.infinite_iff.mp inferInstance)
  obtain ⟨ε⟩ : Nonempty (ι ≃ Idx (ℵ₀ : Cardinal.{u})) :=
    Cardinal.eq.mp (hmk.trans (mk_Idx (ℵ₀ : Cardinal.{u})).symm)
  have efin : V(R).rep (ℵ₀∙p)
      ≃ₗ[R] V(R).rep
        (ℵ₀∙(Projective.unitClass R ℵ₀ le_rfl k)) :=
    e.some.trans ((DirectSum.lequivCongrLeft R ε).trans
      (Projective.rep_cmul_unitClass R ℵ₀ le_rfl le_rfl k).some.symm)
  exact V(R).eq_of_iso efin

end Prop54

end TwoGen

end KappaMonoid
