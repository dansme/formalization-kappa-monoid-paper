/-
**Lemma 5.1**: if `H ≅ V^{ℵ₀}(R)` for a ring whose projectives are direct sums of finitely
generated modules, then `H` is braided over `add (x₁ + x₂)`.  The one module-theoretic file of
§5's braiding material.
-/
import KappaMonoid.TwoGen.Prelim
import KappaMonoid.TwoGen.Lemma52
import KappaMonoid.Modules.Corollary47

universe u v

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

variable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]

section Lemma51

variable (R : Type u) [Ring R]

/-- **Lemma 5.1, the core**: under an isomorphism `H ≅ V^{ℵ₀}(R)` with `R` a ring whose
projectives are direct sums of finitely generated modules, the elements of `H` whose modules are
finitely generated are exactly `add (x₁ + x₂)`, and each of them is `m x₁ + n x₂` for natural
numbers `m`, `n`.

Paper proof: `S := e⁻¹(V(R))` is a divisor-closed submonoid generating `H`, so by the paper's
parenthetical (`mem_of_divisorClosed_of_generates`) both `x₁` and `x₂` lie in `S` — otherwise `V(R)`
and hence `V^{ℵ₀}(R)` would be cyclic.  That gives `add (x₁ + x₂) ⊆ S`.  Conversely, every `a ∈ S`
has a form `α x₁ + β x₂` (`exists_form`); an infinite coefficient would put `ℵ₀ x₁` or `ℵ₀ x₂` in
`S`, and `ℵ₀ [P]` is finitely generated only for `[P] = 0` (`eq_zero_of_finite_cmul_top`), which
contradicts `x₁, x₂ ≠ 0`.  So the coefficients are finite, and `m x₁ + n x₂` is a summand of
`(m+n)(x₁+x₂)`. -/
theorem lemma_5_1_core (hfg : EveryProjectiveIsSumOfFG R) (x₁ x₂ : H)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H))
    (e : H → V(R).carrier)
    (hhom : KMonoid.IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) :
    (∀ a ∈ e ⁻¹' (V(R).lambdaGenPart ℵ₀), ∃ m n : ℕ, a = m • x₁ + n • x₂) ∧
      e ⁻¹' (V(R).lambdaGenPart ℵ₀) = add((x₁ + x₂)) := by
  classical
  -- Corollary 4.5(3): `V^{ℵ₀}(R)` is braided over `V(R)`, the finitely generated classes
  have hbrV := (corollary_4_5_three.{u, u} R ℵ₀ le_rfl hfg).1
  set S : Set H := e ⁻¹' (V(R).lambdaGenPart ℵ₀) with hSdef
  have hWsub := V(R).lambdaGenPart_isLSubset ℵ₀
    Cardinal.isRegular_aleph0 (Order.le_succ ℵ₀)
  have h0S : (0 : H) ∈ S := by
    show e 0 ∈ V(R).lambdaGenPart ℵ₀
    rw [hhom.1]
    exact hWsub.zero_mem
  -- `V(R)` is closed under binary sums: `+` is a two-element `ℵ₀⁻`-sum
  have haddS : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := by
    intro a ha b hb
    show e (a + b) ∈ V(R).lambdaGenPart ℵ₀
    rw [KMonoid.IsKHom.map_add hhom]
    exact hWsub.add_mem le_rfl ha hb
  -- `S` is divisor-closed, because `V(R)` is (a summand of a f.g. module is f.g.)
  have hSsat : ∀ a ∈ S, ∀ b c : H, a = b + c → b ∈ S := by
    intro a ha b c habc
    exact V(R).lambdaGenPart_summand ℵ₀ (e a) ha (e b)
      ⟨e c, by rw [← KMonoid.IsKHom.map_add hhom, ← habc]⟩
  -- and `S` generates `H`, because `V(R)` generates `V^{ℵ₀}(R)`
  have hSgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) S := by
    refine KMonoid.kGenerates_iff.mpr fun h => ?_
    obtain ⟨z, hz⟩ := hbrV.generates (e h)
    choose w hw using fun i => hbij.2 ((z i : V(R).carrier))
    refine (KMonoid.mem_kclosure_iff (S := S) h0S h).mpr ⟨w, fun i => ?_, hbij.1 ?_⟩
    · show e (w i) ∈ V(R).lambdaGenPart ℵ₀
      rw [hw i]
      exact (z i).2
    · rw [hz, hhom.2 w]
      exact congrArg _ (funext fun i => (hw i).symm)
  -- **the paper's parenthetical**: both generators lie in `S`, else `H` would be cyclic
  obtain ⟨hx₁S, hx₂S⟩ :=
    mem_of_divisorClosed_of_generates x₁ x₂ hSsat hSgen hgen hnoncyclic
  obtain ⟨hne₁, hne₂⟩ := ne_zero_of_not_cyclic x₁ x₂ hgen hnoncyclic
  -- an infinite coefficient is impossible: `ℵ₀ [P]` is finitely generated only for `[P] = 0`
  have hkill : ∀ x : H, x ≠ 0 → ℵ₀∙x ∉ S := by
    intro x hx hmem
    have hfin : Module.Finite R (V(R).rep (ℵ₀∙(e x))) := by
      have hrw : e (ℵ₀∙x) = ℵ₀∙(e x) := KMonoid.IsKHom.map_cmul hhom le_rfl x
      exact IsLambdaGenerated.finite_aleph0 (V(R).isLambdaGenerated_of_mem (hrw ▸ hmem))
    exact hx (hbij.1 ((eq_zero_of_finite_cmul_top R hfin).trans hhom.1.symm))
  -- every element of `S` has natural-number coefficients
  have hnat : ∀ a ∈ S, ∃ m n : ℕ, a = m • x₁ + n • x₂ := by
    intro a ha
    obtain ⟨F, hF⟩ := exists_form x₁ x₂ hgen a
    have hfin : ¬ F.IsInfinite := by
      rintro (hc | hc)
      · exact hkill x₁ hne₁ (hSsat a ha _ (ecmul F.2 x₂) (by rw [← hF, eval, hc, ecmul_top]))
      · exact hkill x₂ hne₂ (hSsat a ha _ (ecmul F.1 x₁)
          (by rw [← hF, eval, hc, ecmul_top, add_comm]))
    rw [Form.not_isInfinite_iff] at hfin
    obtain ⟨m, hm⟩ : ∃ m : ℕ, F.1 = (m : ℕ∞) := ⟨F.1.toNat, (ENat.natCast_toNat hfin.1).symm⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, F.2 = (n : ℕ∞) := ⟨F.2.toNat, (ENat.natCast_toNat hfin.2).symm⟩
    exact ⟨m, n, by rw [← hF, eval, hm, hn, ecmul_natCast, ecmul_natCast]⟩
  refine ⟨hnat, Set.Subset.antisymm (fun a ha => ?_) (fun a ha => ?_)⟩
  · -- `m x₁ + n x₂` is a summand of `(m+n)(x₁+x₂)`
    obtain ⟨m, n, rfl⟩ := hnat a ha
    refine ⟨n • x₁ + m • x₂, m + n, ?_⟩
    rw [KMonoid.cmul_natCast, smul_add, add_smul, add_smul]
    abel
  · -- `add (x₁ + x₂) ⊆ S`, since `S` is a divisor-closed submonoid containing `x₁ + x₂`
    have hnsmulS : ∀ (k : ℕ) (b : H), b ∈ S → k • b ∈ S := by
      intro k b hb
      induction k with
      | zero => rwa [zero_nsmul]
      | succ p hp => rw [succ_nsmul]; exact haddS _ hp _ hb
    obtain ⟨z, k, hzk⟩ := ha
    refine hSsat _ ?_ a z hzk.symm
    rw [KMonoid.cmul_natCast]
    exact hnsmulS k _ (haddS _ hx₁S _ hx₂S)

/-- **Lemma 5.1**: two generators of `V^{ℵ₀}(R)` force braidedness over `add (x₁ + x₂)`.

Corollary 4.5(3) braids `V^{ℵ₀}(R)` over `V(R)`, and `lemma_5_1_core` identifies the preimage of
`V(R)` with `add (x₁ + x₂)`; `IsBraidedOver.of_kIso_subset` moves the braiding across. -/
theorem lemma_5_1 (hfg : EveryProjectiveIsSumOfFG R) (x₁ x₂ : H)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H))
    (e : H → V(R).carrier)
    (hhom : KMonoid.IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) :

    IsBraidedOver ℵ₀ ℵ₀ ↥(add((x₁ + x₂))) H (Order.le_succ ℵ₀) (fun y => (y : H)) := by
  classical
  have hbrV := (corollary_4_5_three.{u, u} R ℵ₀ le_rfl hfg).1
  have hWsub := V(R).lambdaGenPart_isLSubset ℵ₀
    Cardinal.isRegular_aleph0 (Order.le_succ ℵ₀)
  have hpre := (lemma_5_1_core R hfg x₁ x₂ hgen hnoncyclic e hhom hbij).2
  have hTS : ∀ a ∈ add((x₁ + x₂)), e a ∈ V(R).lambdaGenPart ℵ₀ := by
    intro a ha
    rw [← hpre] at ha
    exact ha
  -- `add (x₁ + x₂)` generates `H`, since it contains both generators
  have hx₁T : x₁ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  have hTgen : KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) (add((x₁ + x₂))) := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hgen]
    refine KMonoid.kclosure_le ?_ (KMonoid.isKSubmonoid_kclosure _ _)
    rintro w (rfl | rfl)
    · exact KMonoid.subset_kclosure hx₁T
    · exact KMonoid.subset_kclosure hx₂T
  exact IsBraidedOver.of_kIso_subset Cardinal.isRegular_aleph0 hWsub
    (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)) hbrV hhom hbij hTS
    (KMonoid.addOf_isSaturated (x₁ + x₂)) hTgen

/-- **Lemma 5.1**, first conclusion: `x₁` and `x₂` correspond to finitely generated modules. -/
theorem lemma_5_1_fg (hfg : EveryProjectiveIsSumOfFG R) (x₁ x₂ : H)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H))
    (e : H → V(R).carrier)
    (hhom : KMonoid.IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) :
    Module.Finite R (V(R).rep (e x₁)) ∧ Module.Finite R (V(R).rep (e x₂)) := by
  have hpre := (lemma_5_1_core R hfg x₁ x₂ hgen hnoncyclic e hhom hbij).2
  have hx₁ : x₁ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂ : x₂ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  rw [← hpre] at hx₁ hx₂
  exact ⟨IsLambdaGenerated.finite_aleph0 (V(R).isLambdaGenerated_of_mem hx₁),
    IsLambdaGenerated.finite_aleph0 (V(R).isLambdaGenerated_of_mem hx₂)⟩

/-- **Lemma 5.1**, third conclusion, first half: `add (x₁ + x₂) = ⟨x₁, x₂⟩`, the ordinary
submonoid generated by the two elements. -/
theorem lemma_5_1_addOf_eq_closure (hfg : EveryProjectiveIsSumOfFG R) (x₁ x₂ : H)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H))
    (e : H → V(R).carrier)
    (hhom : KMonoid.IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) :
    add((x₁ + x₂)) = (AddSubmonoid.closure ({x₁, x₂} : Set H) : Set H) := by
  obtain ⟨hnat, hpre⟩ := lemma_5_1_core R hfg x₁ x₂ hgen hnoncyclic e hhom hbij
  have hsub : IsLSubset ℵ₀ (Order.le_succ ℵ₀) (add((x₁ + x₂))) :=
    KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)
  have hx₁T : x₁ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₁ x₂ rfl
  have hx₂T : x₂ ∈ add((x₁ + x₂)) :=
    KMonoid.addOf_isSaturated (x₁ + x₂) _ (KMonoid.self_mem_addOf _) x₂ x₁ (add_comm x₁ x₂)
  refine Set.Subset.antisymm (fun a ha => ?_) (fun a ha => ?_)
  · obtain ⟨m, n, rfl⟩ := hnat a (by rw [hpre]; exact ha)
    have hcl : ∀ (w : H), w ∈ ({x₁, x₂} : Set H) →
        ∀ k : ℕ, k • w ∈ AddSubmonoid.closure ({x₁, x₂} : Set H) :=
      fun w hw k => nsmul_mem (AddSubmonoid.subset_closure hw) k
    exact AddSubmonoid.add_mem _ (hcl x₁ (Set.mem_insert _ _) m)
      (hcl x₂ (Set.mem_insert_of_mem _ rfl) n)
  · induction ha using AddSubmonoid.closure_induction with
    | mem w hw => rcases hw with rfl | rfl
                  · exact hx₁T
                  · exact hx₂T
    | zero => exact hsub.zero_mem
    | add p q _ _ hp hq => exact hsub.add_mem le_rfl hp hq

/-- **Lemma 5.1**, third conclusion, second half: `V(R) ≅ add (x₁ + x₂)` as `ℵ₀⁻`-monoids — the
restriction of the isomorphism `H ≅ V^{ℵ₀}(R)`. -/
theorem lemma_5_1_iso (hfg : EveryProjectiveIsSumOfFG R) (x₁ x₂ : H)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H))
    (e : H → V(R).carrier)
    (hhom : KMonoid.IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) :
    ∃ φ : ↥(add((x₁ + x₂))) → ↥(V(R).lambdaGenPart ℵ₀),
      IsLMonoidHom ℵ₀ φ ∧ Function.Bijective φ := by
  classical
  let hW := V(R).lambdaGenPart_isLSubset ℵ₀ Cardinal.isRegular_aleph0 (Order.le_succ ℵ₀)
  have hpre := (lemma_5_1_core R hfg x₁ x₂ hgen hnoncyclic e hhom hbij).2
  have hmaps : ∀ a ∈ add((x₁ + x₂)), e a ∈ V(R).lambdaGenPart ℵ₀ := by
    intro a ha
    rw [← hpre] at ha
    exact ha
  refine ⟨fun a => ⟨e a, hmaps a a.2⟩,
    hhom.restrict_isLMonoidHom Cardinal.isRegular_aleph0
      (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂)) hW hmaps, ?_, ?_⟩
  · exact fun a b hab => Subtype.ext (hbij.1 (Subtype.ext_iff.mp hab))
  · rintro ⟨w, hw⟩
    obtain ⟨a, rfl⟩ := hbij.2 w
    exact ⟨⟨a, by rw [← hpre]; exact hw⟩, rfl⟩

end Lemma51

end TwoGen

end KappaMonoid
