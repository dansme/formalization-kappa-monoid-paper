/-
**Coproducts of `k^ι`-rings and Bergman's theorem on their projective modules.**

`IsCoprod σ σC inc` says that `C` is the coproduct (pushout) of the `k^ι`-rings `R l`
(`σ l : k^ι → R l`) in the category of `k`-algebras under `k^ι`.  No construction is needed: in
the applications `C` is a matrix ring over a presented algebra, shown to have the universal
property directly (`Bergman/Morita.lean`).

**Bergman, *Modules over coproducts of rings* (1974), Corollaries 2.6 and 2.8, in the form of §9
(`R₀` a finite product of copies of a field)**: if every `σ l` is injective, then `V(C)` is the
pushout of the `V(R l)` over `V(k^ι)`: every finitely generated projective `C`-module is induced
from the factors, and two induced modules are isomorphic iff their components are related by
*basic transfers* (moving a summand `k e_i` from one factor to another).

The proof (`Bergman/Core/…`) follows Bergman §§4–9: the normal form of standard modules, support
and leading terms, well-positioned families (Definition 5.2), Proposition 6.2 (adjusting a
homomorphism by transfers and transvections), Proposition 8.2 and Proposition 8.4.
-/
import KappaMonoid.Bergman.Idem
import KappaMonoid.Bergman.Presentation
import KappaMonoid.Bergman.IsCoprod
import KappaMonoid.Bergman.Core.VBridge

universe u

namespace Bergman

variable (k : Type u) [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Λ : Type} [Fintype Λ] [DecidableEq Λ]
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]

variable {k}

section

variable {σ : ∀ l, (ι → k) →ₐ[k] R l} {C : Type u} [Ring C] [Algebra k C]
  {σC : (ι → k) →ₐ[k] C} {inc : ∀ l, R l →ₐ[k] C}

variable (σC inc) in
/-- The comparison map from the components to `V(C)`: induce each component up to `C`. -/
noncomputable def coprodV : V (ι → k) × (∀ l, V (R l)) →+ V C where
  toFun p := V.map σC.toRingHom p.1 + ∑ l, V.map (inc l).toRingHom (p.2 l)
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
    abel

variable (σ) in
/-- A **basic transfer**: move `a ∈ V(k^ι)` from the `k^ι`-component to the `l`-component. -/
def transferRel (p q : V (ι → k) × (∀ l, V (R l))) : Prop :=
  ∃ (a : V (ι → k)) (l : Λ), p = (a, 0) ∧ q = (0, Pi.single l (V.map (σ l).toRingHom a))

/-- **Bergman's theorem (Cor. 2.6, 2.8)**: every finitely generated projective module over a
coproduct of faithful `k^ι`-rings is induced from the factors. -/
theorem IsCoprod.coprodV_surjective (hC : IsCoprod k σ C σC inc)
    (hσ : ∀ l, Function.Injective (σ l)) : Function.Surjective (coprodV σC inc) := by
  have : Fact (∀ l, Function.Injective (σ l)) := ⟨hσ⟩
  have : Fact (IsCoprod k σ C σC inc) := ⟨hC⟩
  exact Core.exists_pair_of_cls σ

/-- **Bergman's theorem (Cor. 2.8)**: induced modules are isomorphic iff their components are
related by basic transfers. -/
theorem IsCoprod.coprodV_eq_iff (hC : IsCoprod k σ C σC inc)
    (hσ : ∀ l, Function.Injective (σ l)) (p q : V (ι → k) × (∀ l, V (R l))) :
    coprodV σC inc p = coprodV σC inc q ↔ addConGen (transferRel σ) p q := by
  have : Fact (∀ l, Function.Injective (σ l)) := ⟨hσ⟩
  have : Fact (IsCoprod k σ C σC inc) := ⟨hC⟩
  refine ⟨fun h => Core.rel_of_eq σ (transferRel σ) (fun a l => ⟨a, l, rfl, rfl⟩) p q h,
    fun h => ?_⟩
  have hle : addConGen (transferRel σ) ≤ AddCon.ker (coprodV σC inc) :=
    AddCon.addConGen_le.2 fun x y hxy => by
      obtain ⟨a, l, rfl, rfl⟩ := hxy
      rw [AddCon.ker_rel]
      change V.map σC.toRingHom a + ∑ l', V.map (inc l').toRingHom ((0 : ∀ l, V (R l)) l') =
        V.map σC.toRingHom 0 + ∑ l', V.map (inc l').toRingHom
          (Pi.single (M := fun l => V (R l)) l (V.map (σ l).toRingHom a) l')
      simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero, zero_add]
      rw [Finset.sum_eq_single l (fun l' _ h => by rw [Pi.single_eq_of_ne h, map_zero])
        (by simp), Pi.single_eq_same, ← V.map_comp, ← hC.comm l]
      rfl
  exact hle h

end

end Bergman
