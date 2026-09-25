/-
**The Bergman–Dicks realisation theorem.**

> For every field `k`, every reduced commutative monoid `M` with an order-unit `u` is `V(R)` for
> a hereditary `k`-algebra `R`, with `[R] ↦ u`.

(Bergman, *Coproducts and some universal ring constructions*, Trans. AMS 200 (1974), Thm 6.2;
Bergman–Dicks, *Universal derivations and universal ring constructions*, Pacific J. Math. 79
(1978), Thm 3.4.)

## Route

The proof follows Bergman for `V` and departs from both papers for heredity.

1. **Presentation of `M`** (this file).  Generators: an idempotent `n_a × n_a` matrix `E_a` for
   each `a ≠ 0`, where `a + c_a = n_a • u` with `c_a ≠ 0`.  Relations: isomorphisms
   `P_a ⊕ P_b ≅ P_{a+b}`, `Q_a ≅ P_{c_a}` (`Q_a` the image of `1 - E_a`) and `P_u ≅ R`.  The
   monoid so presented is `M`.
2. **The ring** (`MainRing.lean`) is presented by these generators and relations, in one piece.
3. **Heredity** (`QuasiFree.lean`): the ring is quasi-free — idempotents and isomorphisms between
   images of idempotents lift along square-zero extensions — and quasi-free algebras over a field
   are hereditary (`Ω¹` is a projective bimodule).  This replaces Bergman–Dicks's computation of
   universal derivation modules, and needs no direct limits.
4. **`V`** (`MainRing.lean`, `Steps.lean`): by compactness, reduce to finitely many generators and
   relations; add them one at a time.  Adjoining a universal idempotent or a universal isomorphism
   changes `V` as Bergman's Theorems 5.1 and 5.2 say (`Steps.lean`), because after passing to a
   matrix ring the construction is a coproduct over `k^ι` (`Morita.lean`), to which Bergman's
   coproduct theorem applies (`Coprod.lean`).
5. **Bergman's coproduct theorem** (`Coprod.lean` and `Core/`): the normal form of standard
   modules, well-positioned families, and Propositions 6.2, 8.2 and 8.4 of *Modules over
   coproducts of rings* (1974), in the setting of its §9 (`R₀ = k^ι`).
6. **Modules** (`IdemModule.lean`, `Bridge.lean`): `V` is set up with idempotent matrices; the
   dictionary with finitely generated projective modules gives `BergmanDicksData`.
-/
import KappaMonoid.Bergman.MainRing
import KappaMonoid.Bergman.Bridge

universe u

namespace Bergman

open KappaMonoid

/-- The relations of the presentation of `M`. -/
inductive MRel (M : Type u) [AddCommMonoid M] : Type u
  | add (a b : {a : M // a ≠ 0})
  | comp (a : {a : M // a ≠ 0})
  | unit

section Presentation

variable {M : Type u} [AddCommMonoid M] (u : M)

variable (hred : ∀ a b : M, a + b = 0 → a = 0) (hunit : ∀ y : M, ∃ (z : M) (n : ℕ), y + z = n • u)
  (hu : u ≠ 0)

include hred hunit hu in
/-- Every element is a summand of a multiple of `u`, with a nonzero complement. -/
theorem exists_compl (a : M) : ∃ (c : M) (n : ℕ), c ≠ 0 ∧ a + c = n • u := by
  obtain ⟨z, n, hz⟩ := hunit a
  refine ⟨z + u, n + 1, fun h => hu (hred u z (by rwa [add_comm] at h)), ?_⟩
  rw [← add_assoc, hz, succ_nsmul]

/-- The complement `c_a`. -/
noncomputable def compl (a : M) : M := (exists_compl u hred hunit hu a).choose

/-- The multiple `n_a`. -/
noncomputable def mult (a : M) : ℕ := (exists_compl u hred hunit hu a).choose_spec.choose

theorem compl_ne_zero (a : M) : compl u hred hunit hu a ≠ 0 :=
  (exists_compl u hred hunit hu a).choose_spec.choose_spec.1

theorem add_compl (a : M) : a + compl u hred hunit hu a = mult u hred hunit hu a • u :=
  (exists_compl u hred hunit hu a).choose_spec.choose_spec.2

/-- **The presentation of `M`.** -/
noncomputable def mPres : RingPres {a : M // a ≠ 0} (MRel M) where
  size a := mult u hred hunit hu a
  lhs
    | .add a b => [.img a, .img b]
    | .comp a => [.coimg a]
    | .unit => [.img ⟨u, hu⟩]
  rhs
    | .add a b => [.img ⟨a + b, fun h => a.2 (hred _ _ h)⟩]
    | .comp a => [.img ⟨compl u hred hunit hu a, compl_ne_zero u hred hunit hu a⟩]
    | .unit => [.free]

/-- The evaluation of the atoms in `M`. -/
noncomputable def mEv : Atom {a : M // a ≠ 0} → M
  | .free => u
  | .img a => a
  | .coimg a => compl u hred hunit hu a

theorem mEv_rel (x y : Multiset (Atom {a : M // a ≠ 0}))
    (h : (mPres u hred hunit hu).mrel x y) :
    msum (mEv u hred hunit hu) x = msum (mEv u hred hunit hu) y := by
  rcases h with ⟨g, rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · simp [mEv, mPres, add_compl, Multiset.map_nsmul, Multiset.sum_nsmul]
  · cases j <;> simp [mEv, mPres]

theorem mult_pos (a : {a : M // a ≠ 0}) : 1 ≤ mult u hred hunit hu a := by
  by_contra h
  have h0 : mult u hred hunit hu a = 0 := by omega
  have := add_compl u hred hunit hu a
  rw [h0, zero_smul] at this
  exact a.2 (hred _ _ this)

end Presentation

/-- **The Bergman–Dicks realisation theorem**, for `u ≠ 0`. -/
theorem realization (k : Type u) [Field k] (M : Type u) [AddCommMonoid M] (u : M)
    (hred : ∀ a b : M, a + b = 0 → a = 0) (hunit : ∀ y : M, ∃ (z : M) (n : ℕ), y + z = n • u)
    (hu : u ≠ 0) :
    ∃ (R : Type u) (_ : Ring R) (_ : Algebra k R), IsHereditary R ∧
      ∃ Φ : M ≃+ V R, Φ u = V.one R := by
  classical
  set P := mPres u hred hunit hu
  set ev := mEv u hred hunit hu
  have hpres : PresentedBy (P.γ k) P.mrel :=
    P.presentedBy k ev (mEv_rel u hred hunit hu) hu (mult_pos u hred hunit hu)
      (by
        intro j; cases j with
        | add a b => simpa [P, ev, mPres, mEv] using fun h => a.2 (hred _ _ h)
        | comp a => simpa [P, ev, mPres, mEv] using compl_ne_zero u hred hunit hu a
        | unit => simpa [P, ev, mPres, mEv] using hu)
      (by
        intro j; cases j with
        | add a b => simpa [P, ev, mPres, mEv] using fun h => a.2 (hred _ _ h)
        | comp a => simpa [P, ev, mPres, mEv] using compl_ne_zero u hred hunit hu a
        | unit => simpa [P, ev, mPres, mEv] using hu)
  -- the relations hold in `V`
  have hrel : ∀ j, ((P.lhs j).map (P.γ k)).sum = ((P.rhs j).map (P.γ k)).sum := fun j => by
    have := (hpres.2 _ _).2 (AddConGen.Rel.of _ _ (Or.inr ⟨j, rfl, rfl⟩))
    simpa using this
  have hadd : ∀ (a b : {a : M // a ≠ 0}) (hab : (a : M) + b ≠ 0),
      P.γ k (.img ⟨a + b, hab⟩) = P.γ k (.img a) + P.γ k (.img b) := fun a b _ => by
    have := hrel (.add a b)
    rw [show P.lhs (.add a b) = [.img a, .img b] from rfl,
      show P.rhs (.add a b) = [.img ⟨a + b, _⟩] from rfl] at this
    simpa using this.symm
  have hunitγ : P.γ k (.img ⟨u, hu⟩) = P.γ k .free := by
    have := hrel .unit
    rw [show P.lhs .unit = [.img ⟨u, hu⟩] from rfl, show P.rhs .unit = [.free] from rfl] at this
    simpa using this
  have hcomp : ∀ a : {a : M // a ≠ 0}, P.γ k (.img ⟨compl u hred hunit hu a, compl_ne_zero u hred hunit hu a⟩) =
      P.γ k (.coimg a) := fun a => by
    have := hrel (.comp a)
    rw [show P.lhs (.comp a) = [.coimg a] from rfl,
      show P.rhs (.comp a) = [.img ⟨_, compl_ne_zero u hred hunit hu a⟩] from rfl] at this
    simpa using this.symm
  -- `a ↦ [P_a]`
  let φ : M → V (P.ring k) := fun a => if h : a = 0 then 0 else P.γ k (.img ⟨a, h⟩)
  have hφ_img : ∀ a : {a : M // a ≠ 0}, φ a = P.γ k (.img a) := fun a => by simp [φ, a.2]
  have hφ_add : ∀ a b, φ (a + b) = φ a + φ b := by
    intro a b
    by_cases ha : a = 0
    · simp [ha, φ]
    by_cases hb : b = 0
    · simp [hb, φ]
    have hab : a + b ≠ 0 := fun h => ha (hred _ _ h)
    rw [hφ_img ⟨a + b, hab⟩, hφ_img ⟨a, ha⟩, hφ_img ⟨b, hb⟩]
    exact hadd ⟨a, ha⟩ ⟨b, hb⟩ hab
  let Φ₀ : M →+ V (P.ring k) := ⟨⟨φ, by simp [φ]⟩, hφ_add⟩
  obtain ⟨f, hf⟩ := hpres.exists_lift ev (mEv_rel u hred hunit hu)
  have hfΦ : ∀ a, f (Φ₀ a) = a := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp
    · change f (φ a) = a
      rw [hφ_img ⟨a, ha⟩, hf]; rfl
  have hγ : ∀ α, P.γ k α ∈ Set.range Φ₀ := by
    intro α
    cases α with
    | free => exact ⟨u, (hφ_img ⟨u, hu⟩).trans hunitγ⟩
    | img a => exact ⟨a, hφ_img a⟩
    | coimg a => exact ⟨_, (hφ_img ⟨_, compl_ne_zero u hred hunit hu a⟩).trans (hcomp a)⟩
  have hsurj : Function.Surjective Φ₀ := by
    intro v
    obtain ⟨x, rfl⟩ := hpres.1 v
    induction x using Multiset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | cons α x ih =>
      obtain ⟨a, ha⟩ := hγ α
      obtain ⟨b, hb⟩ := ih
      exact ⟨a + b, by simp [map_add, ha, hb]⟩
  have hinj : Function.Injective Φ₀ := fun a b h => by rw [← hfΦ a, h, hfΦ b]
  refine ⟨P.ring k, inferInstance, inferInstance, (P.quasiFree k).isHereditary,
    AddEquiv.ofBijective Φ₀ ⟨hinj, hsurj⟩, ?_⟩
  show φ u = _
  rw [hφ_img ⟨u, hu⟩, hunitγ]
  rfl

/-- **The Bergman–Dicks realisation theorem**, as `BergmanDicksData`. -/
theorem nonempty_bergmanDicksData (k : Type u) [Field k] (M : Type u) [AddCommMonoid M]
    (u : M) (hred : ∀ a b : M, a + b = 0 → a = 0)
    (hunit : ∀ y : M, ∃ (z : M) (n : ℕ), y + z = n • u) :
    Nonempty (BergmanDicksData k M u) := by
  by_cases hu : u = 0
  · have : Subsingleton M := ⟨fun a b => by
      obtain ⟨z, n, hz⟩ := hunit a
      obtain ⟨z', n', hz'⟩ := hunit b
      rw [hu, smul_zero] at hz hz'
      rw [hred _ _ hz, hred _ _ hz']⟩
    exact nonempty_bergmanDicksData_of_subsingleton k M u
  · obtain ⟨R, _, _, hR, Φ, hΦ⟩ := realization k M u hred hunit hu
    exact nonempty_bergmanDicksData_of_V k M u R hR Φ hΦ

end Bergman

namespace KappaMonoid

/-- **The Bergman–Dicks realisation theorem** (Bergman, *Coproducts and some universal ring
constructions*, Trans. AMS 200 (1974), Theorem 6.2; Bergman–Dicks, *Universal derivations and
universal ring constructions*, Pacific J. Math. 79 (1978), Theorem 3.4).  For every field `k`,
every reduced commutative monoid with an order-unit `u` is `V(R)` for a hereditary `k`-algebra
`R`, with `[R] ↦ u`.

*Reduced* is the paper's term for conical: `a + b = 0` forces `a = 0`.  An *order-unit* is a `u`
such that every element divides some multiple of `u`.

This was the one assumed result of the development; it is now `Bergman.nonempty_bergmanDicksData`,
proved in this directory.  Compared with the sources:

* Bergman's Theorem 6.2 is for a *finitely generated* monoid; the arbitrary case is Bergman–Dicks's
  remark after their Theorem 3.4, by direct limits.  Here no direct limit is needed: the ring is
  presented by all generators and relations at once, `V` is computed by compactness, and heredity
  comes from quasi-freeness (`QuasiFree.lean`) rather than from universal derivations.
* The papers are about right modules, this statement about left ones; `hereditary` is the
  two-sided `IsHereditary`, which Bergman's construction gives and the proof here produces.
* There is no `u ≠ 0`: with `_hred` and `_hunit`, `u = 0` forces `M` to be trivial, and the zero
  ring realises the trivial monoid (`nonempty_bergmanDicksData_of_subsingleton`).  Nothing here
  claims `Nontrivial R`; compare `leavittData`, which assumes `m ≥ 1`. -/
noncomputable def bergmanDicksData (k : Type u) [Field k] (M : Type u) [AddCommMonoid M] (u : M)
    (_hred : ∀ a b : M, a + b = 0 → a = 0)
    (_hunit : ∀ y : M, ∃ (z : M) (n : ℕ), y + z = n • u) :
    BergmanDicksData.{u} k M u :=
  (Bergman.nonempty_bergmanDicksData k M u _hred _hunit).some

end KappaMonoid
