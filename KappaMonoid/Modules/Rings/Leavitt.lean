/-
**Leavitt's realisation theorem, deduced from Bergman–Dicks.**

Every cyclic monoid `C_{m,n}` with `m ≥ 1`, `n ≥ 1` is the monoid of finitely generated free
modules over some ring.  It is a consequence of the Bergman–Dicks realisation theorem, which is
the deeper statement and is needed anyway (`Bergman/Realization.lean`).

The deduction is the obvious one once `BergmanDicksData` records that the order-unit is the class
of the ring itself (`iso_unit`, `[R] = u`, which is what Bergman's construction gives):

* `C_{m,n}` is a monoid — `ForMathlib/CyclicMonoid.lean` builds it as `ℕ₀` modulo the congruence
  `∼_{m,n}` — it is conical exactly because `m ≥ 1`, and the class of `1` is an order-unit;
* so Bergman–Dicks hands back a hereditary algebra `R` with `V(R) ≅ C_{m,n}` and `[R] ↦ 1`;
* the module realising `k • 1` is then `R^k`, by induction on `k` from `iso_add` and `iso_unit`;
* and `a ↦ [P a]` being injective turns `R^k ≅ R^l` into `k ∼_{m,n} l`.

`Nontrivial R` comes out of the same injectivity: over a trivial ring every module is trivial, so
`P 1 ≅ P 0`, forcing `1 = 0` in `C_{m,n}` — false for `m ≥ 1`.

The trade is deliberate and worth stating plainly: §2.3 rests on Bergman–Dicks rather than on
Leavitt's much more elementary theorem, because Bergman–Dicks is needed for §§4–5 anyway.  Leavitt's own proof is a seven-page minimal-counterexample
argument on leading terms, and it covers only type `(1,k)` — his type `(n,1)` rings are in the
earlier [Leavitt56; Leavitt57], and even the normal form his argument computes with is quoted from
there.
-/
import KappaMonoid.Bergman.Realization
import KappaMonoid.ForMathlib.CyclicMonoid

universe u

open DirectSum

namespace KappaMonoid

/-- A ring realising the cyclic monoid `C_{m,n}` as its monoid of finitely generated free
modules: `R^k ≅ R^l` exactly when `k ∼_{m,n} l`. -/
structure LeavittData (m n : ℕ) where
  /-- The realising ring. -/
  R : Type u
  [ring : Ring R]
  [nontrivial : Nontrivial R]
  /-- Isomorphism of finitely generated free modules is exactly `∼_{m,n}`. -/
  iso_iff : ∀ k l : ℕ,
    Nonempty ((⨁ _ : Fin k, R) ≃ₗ[R] (⨁ _ : Fin l, R)) ↔ CyclicRel m n k l

attribute [instance] LeavittData.ring LeavittData.nontrivial

namespace Leavitt

/-- Any two subsingleton modules are isomorphic. -/
private def equivOfSubsingleton (R : Type u) [Ring R] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton M] [Subsingleton N] : M ≃ₗ[R] N where
  toFun _ := 0
  invFun _ := 0
  map_add' _ _ := (add_zero 0).symm
  map_smul' r _ := (smul_zero r).symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- `R^(k+1) ≅ R^k ⊕ R`. -/
private def freeSplitSucc (R : Type u) [Ring R] (k : ℕ) :
    (Fin (k + 1) → R) ≃ₗ[R] (Fin k → R) × R :=
  ((LinearEquiv.funCongrLeft R R (finSumFinEquiv (m := k) (n := 1))).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin 1) R R)).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl R _) (LinearEquiv.funUnique (Fin 1) R R))

end Leavitt

/-- **Leavitt's realisation theorem** (Leavitt 1962), here deduced from Bergman–Dicks.

`m ≥ 1` is necessary, not a convenience: `C_{0,n}` identifies `0` with `n`, so a realising ring
would have `R^0 ≅ R^n`, forcing `R = 0`.  It is also exactly where the deduction needs it —
`C_{0,n}` is a group, and Bergman–Dicks realises conical monoids. -/
noncomputable def leavittData (m n : ℕ) (hm : 1 ≤ m) (_hn : 1 ≤ n) : LeavittData.{u} m n := by
  classical
  -- `C_{m,n}` is conical, with the class of `1` as an order-unit
  have hred : ∀ a b : CyclicMonoidU.{u} m n, a + b = 0 → a = 0 :=
    CyclicMonoidU.eq_zero_of_add_eq_zero hm
  have hunit : ∀ y : CyclicMonoidU.{u} m n, ∃ (z : CyclicMonoidU.{u} m n) (t : ℕ),
      y + z = t • CyclicMonoidU.mk m n 1 := by
    intro y
    obtain ⟨k, rfl⟩ := CyclicMonoidU.surjective_mk m n y
    exact ⟨0, k, by rw [add_zero, CyclicMonoidU.nsmul_mk_one]⟩
  -- so Bergman–Dicks realises it
  have bd := bergmanDicksData (ULift.{u} ℚ) (CyclicMonoidU.{u} m n)
    (CyclicMonoidU.mk m n 1) hred hunit
  -- the module realising `k • 1` is `R^k`
  have hpow : ∀ k : ℕ,
      Nonempty (bd.P (k • CyclicMonoidU.mk.{u} m n 1) ≃ₗ[bd.R] (Fin k → bd.R)) := by
    intro k
    induction k with
    | zero =>
      have := bd.iso_zero
      rw [zero_nsmul]
      exact ⟨Leavitt.equivOfSubsingleton bd.R _ _⟩
    | succ k ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨e₁⟩ := bd.iso_add (k • CyclicMonoidU.mk.{u} m n 1) (CyclicMonoidU.mk.{u} m n 1)
      obtain ⟨e₂⟩ := bd.iso_unit
      rw [succ_nsmul]
      exact ⟨e₁.trans ((e.prodCongr e₂).trans (Leavitt.freeSplitSucc bd.R k).symm)⟩
  have hds : ∀ k : ℕ, ((⨁ _ : Fin k, bd.R) ≃ₗ[bd.R] (Fin k → bd.R)) :=
    fun k => DirectSum.linearEquivFunOnFintype bd.R (Fin k) fun _ => bd.R
  -- the ring is nontrivial, since `C_{m,n}` is not
  have hnt : Nontrivial bd.R := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have := hcon
    have : Subsingleton (bd.P (CyclicMonoidU.mk.{u} m n 1)) := Module.subsingleton bd.R _
    have := bd.iso_zero
    exact CyclicMonoidU.mk_one_ne_zero hm
      (bd.inj _ _ ⟨Leavitt.equivOfSubsingleton bd.R _ _⟩)
  refine { R := bd.R, ring := bd.ring, nontrivial := hnt, iso_iff := fun k l => ?_ }
  obtain ⟨ek⟩ := hpow k
  obtain ⟨el⟩ := hpow l
  constructor
  · rintro ⟨e⟩
    have hkl : k • CyclicMonoidU.mk.{u} m n 1 = l • CyclicMonoidU.mk.{u} m n 1 :=
      bd.inj _ _ ⟨ek.trans (((hds k).symm.trans (e.trans (hds l))).trans el.symm)⟩
    rwa [CyclicMonoidU.nsmul_mk_one, CyclicMonoidU.nsmul_mk_one,
      CyclicMonoidU.mk_eq_mk_iff] at hkl
  · intro h
    have hkl : k • CyclicMonoidU.mk.{u} m n 1 = l • CyclicMonoidU.mk.{u} m n 1 := by
      rw [CyclicMonoidU.nsmul_mk_one, CyclicMonoidU.nsmul_mk_one, CyclicMonoidU.mk_eq_mk_iff]
      exact h
    have hP : Nonempty (bd.P (k • CyclicMonoidU.mk.{u} m n 1) ≃ₗ[bd.R]
        bd.P (l • CyclicMonoidU.mk.{u} m n 1)) := by
      rw [hkl]; exact ⟨LinearEquiv.refl _ _⟩
    obtain ⟨eP⟩ := hP
    exact ⟨(hds k).trans (ek.symm.trans (eP.trans (el.trans (hds l).symm)))⟩

end KappaMonoid
