import Comparator.Bridge.Modules

/-!
# Bridge, part 4: the main results in the challenge's terms

Each `*_bridge` theorem is a challenge statement, with the challenge's structures explicit (the
instances are erased in the bridge), proved from the library.  `Comparator/Solution.lean`
restates them verbatim.
-/

universe u v t

open Cardinal Function Set DirectSum
open scoped KappaMonoid

namespace KappaChallenge

attribute [-instance] KMonoid.instAdd KMonoid.instSMul LMonoid.instAdd KMonoid.toZero LMonoid.toZero

/-! ## Theorem 3.12 -/

theorem theorem_3_12_bridge {κ : Cardinal.{u}} {ι : Type u} [LinearOrder ι] [WellFoundedLT ι]
    [NoMaxOrder ι] [SuccOrder ι] (hι : #ι = κ) {lam : Cardinal.{u}} (hlk : lam ≤ Order.succ κ)
    (X : Type v)
    (CX : LMonoid lam X)
    (hred : ∀ a b : X, @HAdd.hAdd X X X (@instHAdd X (@LMonoid.instAdd _ _ CX)) a b =
      @OfNat.ofNat X 0 (@Zero.toOfNat0 X CX.toZero) →
        a = @OfNat.ofNat X 0 (@Zero.toOfNat0 X CX.toZero) ∧
          b = @OfNat.ofNat X 0 (@Zero.toOfNat0 X CX.toZero)) :
    ∃ (Hh : Type (max u v)) (C : KMonoid κ Hh) (f : X → Hh), Injective f ∧
      @LMonoid.IsHom lam X CX κ Hh C f ∧ IsBraidedOver ι lam (range f) ∧
      @IsUniversalOver.{u, max u v, t} κ Hh C lam (range f) := by
  let LX := CX.toLib
  have hcon : KappaMonoid.IsConical X := fun a b h => by
    rw [LMonoid.toLib_add] at h
    exact hred a b h
  obtain ⟨Hh, LH, f, hinj, hbr, hU⟩ :=
    KappaMonoid.theorem_3_12.{u, v, t} CX.isRegular hlk X hcon
  have hc := KMonoid.compat_ofLib LH
  refine ⟨Hh, KMonoid.ofLib LH, f, hinj, ⟨hbr.isLHom.1, fun ι x hι => ?_⟩,
    isBraidedOver_of_lib hc hlk ι hι hbr, isUniversalOver_of_lib hc hlk hU⟩
  rw [← LMonoid.toLib_lsumOf CX hι, hbr.isLHom.2 hι x,
    hc.sumOf' (Order.le_of_lt_succ (hι.trans_le hlk))]

/-! ## Rings -/

section Rings

variable {κ : Cardinal.{u}} {H : Type u} (C : KMonoid κ H)

theorem hereditary_iff (k : Type u) [Field k] :
    (∃ (R : Type u) (_ : Ring R) (_ : Algebra k R), IsHereditary R ∧ @IsoV κ R _ H C) ↔
      (letI := C.toLib
       ∃ (R : Type u) (_ : Ring R) (_ : Algebra k R) (_ : _root_.IsHereditary R),
        ∃ e : (KappaMonoid.projClass R κ C.aleph0_le).carrier → H,
          KappaMonoid.KMonoid.IsKHom κ e ∧ Bijective e) := by
  constructor
  · rintro ⟨R, i₁, i₂, hR, hV⟩
    exact ⟨R, i₁, i₂, isHereditary_iff.mp hR, (isoV_iff C).mp hV⟩
  · rintro ⟨R, i₁, i₂, hR, hV⟩
    exact ⟨R, i₁, i₂, isHereditary_iff.mpr hR, (isoV_iff C).mpr hV⟩

end Rings

/-! ## §5 -/

section TwoGen

variable {H : Type u} (C : KMonoid (ℵ₀ : Cardinal.{u}) H)

local notation "LH" => C.toLib

theorem ecmul_eq (a : ℕ∞) (x : H) : (letI := LH; KappaMonoid.TwoGen.ecmul a x) = a •[C] x := by
  let := LH
  exact (KMonoid.compat_toLib C).smul a x

theorem eval_eq (x₁ x₂ : H) (F : ℕ∞ × ℕ∞) :
    (letI := LH; KappaMonoid.TwoGen.eval x₁ x₂ F) = F.1 •[C] x₁ +[C] F.2 •[C] x₂ := by
  let := LH
  rw [KappaMonoid.TwoGen.eval, (KMonoid.compat_toLib C).add, ecmul_eq, ecmul_eq]

theorem aleph0_smul_eq (x : H) :
    (letI := LH; KappaMonoid.KMonoid.cmul ℵ₀ le_rfl x) = ⊤ •[C] x := by
  let := LH
  rw [← ecmul_eq, KappaMonoid.TwoGen.ecmul_top]

theorem conditions53_iff (a b : H) :
    @Conditions53 H C a b ↔ (letI := LH; KappaMonoid.TwoGen.Cond1 a b ∧ KappaMonoid.TwoGen.Cond2 a b) := by
  let := LH
  have hc := KMonoid.compat_toLib C
  simp only [Conditions53, KappaMonoid.TwoGen.Cond1, KappaMonoid.TwoGen.Cond2, eval_eq, hc.add,
    hc.smul_natCast, aleph0_smul_eq, hc.addOf]

theorem noMixedForms_iff (x₁ x₂ : H) :
    @NoMixedForms H C x₁ x₂ ↔ (letI := LH; KappaMonoid.TwoGen.NoMixedForms x₁ x₂) := by
  let := LH
  simp only [NoMixedForms, KappaMonoid.TwoGen.NoMixedForms, KappaMonoid.TwoGen.HasFiniteForm,
    KappaMonoid.TwoGen.HasInfiniteForm, KappaMonoid.TwoGen.Form.IsFinite,
    KappaMonoid.TwoGen.Form.IsInfinite, eval_eq]
  constructor
  · rintro h y ⟨⟨F, hF, rfl⟩, ⟨G, hG, hGF⟩⟩
    have := h F.1 F.2 G.1 G.2 hGF.symm hF.1 hF.2
    rcases hG with hG | hG
    · exact this.1 hG
    · exact this.2 hG
  · intro h α β γ δ heq hα hβ
    by_contra hne
    refine h _ ⟨⟨(α, β), ⟨hα, hβ⟩, rfl⟩, ⟨(γ, δ), ?_, heq.symm⟩⟩
    by_contra h'
    exact hne ⟨fun h1 => h' (Or.inl h1), fun h2 => h' (Or.inr h2)⟩

theorem generates_iff (S : Set H) :
    @KMonoid.Generates _ H C S ↔ (letI := LH; KappaMonoid.KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) S) := by
  let := LH
  exact (KMonoid.compat_toLib C).generates S

theorem isRealizable_iff :
    (∃ (R : Type u) (_ : Ring R), ProjectivesAreSumsOfFG R ∧ @IsoV _ R _ H C) ↔
      (letI := LH; KappaMonoid.TwoGen.IsRealizableAsV H) := by
  let := LH
  constructor
  · rintro ⟨R, _, hfg, hV⟩
    exact ⟨R, _, projectivesAreSumsOfFG_iff.mp hfg, (isoV_iff C).mp hV⟩
  · rintro ⟨R, _, hfg, hV⟩
    exact ⟨R, _, projectivesAreSumsOfFG_iff.mpr hfg, (isoV_iff C).mpr hV⟩

end TwoGen

end KappaChallenge
