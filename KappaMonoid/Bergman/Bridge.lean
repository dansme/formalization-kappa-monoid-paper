/-
**From `V R ≅ M` to `BergmanDicksData`.**
-/
import KappaMonoid.Bergman.Data
import KappaMonoid.Bergman.IdemModule

universe u

namespace Bergman

open KappaMonoid

/-- A hereditary `k`-algebra `R` together with a monoid isomorphism `M ≃+ V R` carrying `u` to
`[R]` is Bergman–Dicks data for `(M, u)`.

Proof: realise `a ∈ M` by `rowMod e_a` for an idempotent `e_a` representing `Φ a`; the
dictionary of `Bergman/IdemModule.lean` turns the four monoid-isomorphism conditions into
statements about classes of idempotents. -/
theorem nonempty_bergmanDicksData_of_V (k : Type u) [Field k] (M : Type u) [AddCommMonoid M]
    (u : M) (R : Type u) [Ring R] [Algebra k R] (hR : IsHereditary R) (Φ : M ≃+ V R)
    (hΦ : Φ u = V.one R) : Nonempty (BergmanDicksData k M u) := by
  choose n e he hcls using fun a : M => cls_surjective (Φ a)
  refine ⟨{
    R := R
    hereditary := hR
    P := fun a => rowMod (e a)
    addCommGroup := fun _ => inferInstance
    module := fun _ => inferInstance
    proj := fun a => rowMod.projective (he a)
    fin := fun _ => inferInstance
    iso_zero := ?_
    iso_add := ?_
    inj := ?_
    surj := ?_
    iso_unit := ?_ }⟩
  · show Subsingleton (rowMod (e 0))
    rw [rowMod_subsingleton_iff (he 0), ← cls_eq_zero_iff (he 0), hcls, map_zero]
  · intro a b
    obtain ⟨φ⟩ := (rowModEquiv_iff_cls_eq (he (a + b)) (fromBlocks_idem (he a) (he b))).2
      (by rw [cls_fromBlocks (he a) (he b), hcls a, hcls b, hcls (a + b), map_add])
    obtain ⟨ψ⟩ := rowMod_fromBlocks (he a) (he b)
    exact ⟨φ.trans ψ⟩
  · intro a b h
    apply Φ.injective
    have := (rowModEquiv_iff_cls_eq (he a) (he b)).1 h
    rwa [hcls, hcls] at this
  · intro Q _ _ _ _
    obtain ⟨p, f, hf, ⟨φ⟩⟩ := exists_rowModEquiv (R := R) Q
    refine ⟨Φ.symm (cls f hf), ?_⟩
    obtain ⟨ψ⟩ := (rowModEquiv_iff_cls_eq hf (he _)).2 (by rw [hcls, AddEquiv.apply_symm_apply])
    exact ⟨φ.trans ψ⟩
  · obtain ⟨φ⟩ := (rowModEquiv_iff_cls_eq (he u)
      (by simp : (1 : Matrix (Fin 1) (Fin 1) R) * 1 = 1)).2 (by rw [hcls, hΦ]; rfl)
    obtain ⟨ψ⟩ := rowMod_one (R := R)
    exact ⟨φ.trans ψ⟩

/-- Over a zero ring every module is projective (it is zero, hence free). -/
theorem projective_of_subsingleton_ring {S : Type*} [Ring S] [Subsingleton S] (N : Type*)
    [AddCommGroup N] [Module S N] : Module.Projective S N := by
  have := Module.subsingleton S N
  have := Module.Free.of_subsingleton S N
  exact Module.Projective.of_free

/-- The trivial monoid is realised by the zero ring. -/
theorem nonempty_bergmanDicksData_of_subsingleton (k : Type u) [Field k] (M : Type u)
    [AddCommMonoid M] [Subsingleton M] (u : M) : Nonempty (BergmanDicksData k M u) :=
  ⟨{
    R := PUnit.{u + 1}
    hereditary := IsHereditary.mk' (fun I => projective_of_subsingleton_ring I)
      (fun I => projective_of_subsingleton_ring I)
    P := fun _ => PUnit.{u + 1}
    proj := fun _ => inferInstance
    fin := fun _ => inferInstance
    iso_zero := inferInstance
    iso_add := fun _ _ => ⟨LinearEquiv.ofSubsingleton _ _⟩
    inj := fun _ _ _ => Subsingleton.elim _ _
    surj := fun Q _ _ _ _ => by
      have := Module.subsingleton PUnit.{u + 1} Q
      exact ⟨u, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    iso_unit := ⟨LinearEquiv.refl _ _⟩ }⟩

end Bergman
