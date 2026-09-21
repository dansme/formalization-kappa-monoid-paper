/-
**Section 5: Corollary 5.5**, realizability in each of the three ways `add x₁` and `add x₂` can
compare — incomparable, equal, or `add x₁ ⊊ add x₂`.

All three are bookkeeping on top of Theorem 5.3; (2) and (3) additionally go through Proposition
5.4.  The two "the converse is not true" claims are witnessed by `ℕ₀² ∪ {∞}`, in
`KappaMonoid/TwoGen/Counterexample.lean`.
-/
import KappaMonoid.TwoGen.Trace

universe u v

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

-- The cardinal universe is pinned to `H`'s: `§5` fixes `κ = ℵ₀` and works in a single universe, and
-- leaving `ℵ₀`'s universe to be auto-bound makes two occurrences in one statement refer to
-- *different* universes (trap 5 of `CLAUDE.md`).
variable {H : Type u} [KMonoid (ℵ₀ : Cardinal.{u}) H]

/-! ### The statements Corollary 5.5 compares

Each part of the corollary equates a condition on the relations of `H` with realizability of `H`
as `V^{ℵ₀}(R)` for a ring carrying some extra structure.  Both sides are named here, so that the
three parts read as the paper writes them instead of repeating a ten-line existential. -/

/-- `H ≅ V^{ℵ₀}(R)` for a ring whose projective modules are direct sums of finitely generated
ones.  This is the paper's own phrasing of realizability in Corollary 5.5(1) and (3). -/
def IsRealizableAsV (H : Type u) [KMonoid (ℵ₀ : Cardinal.{u}) H] : Prop :=
  ∃ (R : Type u) (_ : Ring R), EveryProjectiveIsSumOfFG R ∧
    ∃ e : V(R).carrier → H, KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e

/-- `H ≅ V^{ℵ₀}(R)` for a ring whose countably (non finitely) generated projective modules are
free — the realizability of Corollary 5.5(2).  The freeness clause is over the classes of
`V^{ℵ₀}(R)`, not over all projective modules, for which it is false; and it needs no condition on
decompositions of projectives, because it implies one (`everyProjectiveIsSumOfFG_of_free`). -/
def IsRealizableAsVFree (H : Type u) [KMonoid (ℵ₀ : Cardinal.{u}) H] : Prop :=
  ∃ (R : Type u) (_ : Ring R),
    (∀ q : V(R).carrier, ¬ Module.Finite R (V(R).rep q) →
        ∃ ι : Type u, #ι ≤ ℵ₀ ∧ Nonempty (V(R).rep q ≃ₗ[R] DirectSum ι (fun _ => R))) ∧
      ∃ e : V(R).carrier → H, KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e

/-- `IsRealizableAsV` with, in addition, a finitely generated projective `P` whose `P^{(ℵ₀)}` is
not free — the first clause of Corollary 5.5(3). -/
def IsRealizableAsVNonfree (H : Type u) [KMonoid (ℵ₀ : Cardinal.{u}) H] : Prop :=
  ∃ (R : Type u) (_ : Ring R), EveryProjectiveIsSumOfFG R ∧
    (∃ p : V(R).carrier, Module.Finite R (V(R).rep p) ∧
        ¬ ∃ ι : Type u, Nonempty (DirectSum ℕ (fun _ => V(R).rep p)
          ≃ₗ[R] DirectSum ι (fun _ => R))) ∧
      ∃ e : V(R).carrier → H, KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e

/-- `H ≅ V^{ℵ₀}(R)` for a ring with two finitely generated projective generators `P₁`, `P₂` of
`V^{ℵ₀}(R)` satisfying `Tr(P₁) ⊊ Tr(P₂)` — the third clause of Corollary 5.5(3).  No condition on
decompositions of projectives appears: generation by finitely generated classes supplies it
(`everyProjectiveIsSumOfFG_of_kGenerates_finite`). -/
def IsRealizableAsVTracePair (H : Type u) [KMonoid (ℵ₀ : Cardinal.{u}) H] : Prop :=
  ∃ (R : Type u) (_ : Ring R), ∃ p₁ p₂ : V(R).carrier,
    Module.Finite R (V(R).rep p₁) ∧ Module.Finite R (V(R).rep p₂) ∧
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set V(R).carrier) ∧
        traceIdeal R (V(R).rep p₁) < traceIdeal R (V(R).rep p₂) ∧
          ∃ e : V(R).carrier → H, KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e

/-- The relation condition of Corollary 5.5(3) (the paper's `hc:sub:relations`): if
`ℵ₀x₁ + nx₂ = ℵ₀x₁ + βx₂` with `n` finite, then `β` is finite too, and the two forms already agree
after replacing the infinite `x₁`-coefficient by finite ones. -/
def Relations3 (x₁ x₂ : H) : Prop :=
  ∀ (n : ℕ) (β : ℕ∞), eval x₁ x₂ (⊤, (n : ℕ∞)) = eval x₁ x₂ (⊤, β) →
    β ≠ ⊤ ∧ ∃ m m' : ℕ, eval x₁ x₂ ((m : ℕ∞), β) = eval x₁ x₂ ((m' : ℕ∞), (n : ℕ∞))

/-! ## Theorem 5.3, in the form the paper states it

`TwoGen.theorem_5_3` is the equivalence for a *hereditary* `k`-algebra, which is the shape the
proof produces.  The paper states the equivalence for `IsRealizableAsV` — "a ring `R` whose
projective modules are direct sums of finitely generated modules" — and then adds: *"In fact, if
`H` satisfies these conditions, then `H ≅ V^{ℵ₀}(R)` for a hereditary ring `R`."*  Both readings
are recorded, and Albrecht's theorem is what makes them agree. -/

section Theorem53Paper

variable (x₁ x₂ : H)

/-- **Theorem 5.3**: `H` is `V^{ℵ₀}(R)` for a ring whose projective modules are direct sums of
finitely generated modules if and only if the three conditions hold.

The "in fact" of the paper — that such an `R` may then be taken hereditary, and a `k`-algebra for
any field `k` — is `theorem_5_3_backward`; conversely a hereditary ring satisfies the condition by
Albrecht's theorem, so the two equivalences have the same right-hand side. -/
theorem theorem_5_3_sumFG (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    IsRealizableAsV H ↔
      (Cond1 x₁ x₂ ∧ Cond1 x₂ x₁ ∧ Cond2 x₁ x₂ ∧ Cond2 x₂ x₁ ∧ NoMixedForms x₁ x₂) := by
  constructor
  · rintro ⟨R, _, hfg, e, hhom, hbij⟩
    exact theorem_5_3_forward x₁ x₂ R hfg hgen hnoncyclic e hhom hbij
  · rintro ⟨hc1, hc1', hc2, hc2', hmix⟩
    obtain ⟨R, hring, -, hher, e, hhom, hbij⟩ :=
      theorem_5_3_backward x₁ x₂ (ULift.{u} ℚ) hgen hc1 hc1' hc2 hc2' hmix
    exact ⟨R, hring, Albrecht.exists_directSum_fg, e, hhom, hbij⟩

end Theorem53Paper

/-! ## Corollary 5.5 (`hereditarycase`)

Case analysis on how `add x₁` and `add x₂` compare.  All three parts are bookkeeping on top of
Theorem 5.3, with Proposition 5.4 for part (3)'s trace formulation. -/

section Cor55

variable (x₁ x₂ : H)

/-- **Transporting the standing hypotheses along a realization.**  Given an isomorphism
`e : V^{ℵ₀}(R) ≅ H`, its inverse is again an `ℵ₀`-homomorphism, the two generators of `H` pull
back to generators of `V^{ℵ₀}(R)`, and no single class generates `V^{ℵ₀}(R)`.  All three parts of
Corollary 5.5 open with this. -/
theorem exists_inv_generators (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) (R : Type u) [Ring R]
    (e : V(R).carrier → H) (hhom : KMonoid.IsKHom ℵ₀ e) (hbij : Function.Bijective e) :
    ∃ e' : H → V(R).carrier, Function.LeftInverse e' e ∧ Function.RightInverse e' e ∧
      KMonoid.IsKHom (ℵ₀ : Cardinal.{u}) e' ∧
      KMonoid.KGenerates (ℵ₀ : Cardinal.{u}) ({e' x₁, e' x₂} : Set V(R).carrier) ∧
      ∀ p : V(R).carrier, ¬ KMonoid.KGenerates ℵ₀ ({p} : Set V(R).carrier) := by
  refine ⟨(Equiv.ofBijective e hbij).symm, (Equiv.ofBijective e hbij).left_inv,
    (Equiv.ofBijective e hbij).right_inv, hhom.inv hbij (Equiv.ofBijective e hbij).right_inv,
    ?_, ?_⟩
  · have := KMonoid.KGenerates.map (hhom.inv hbij (Equiv.ofBijective e hbij).right_inv)
      (Equiv.ofBijective e hbij).left_inv.surjective hgen
    rwa [Set.image_pair] at this
  · intro p hp
    refine hnoncyclic (e p) ?_
    have := KMonoid.KGenerates.map hhom hbij.2 hp
    rwa [Set.image_singleton] at this

/-! ### Part (1): incomparable generators -/

/-- **Corollary 5.5(1)**: for incomparable generators, realizability is equivalent to an explicit
condition on the relations of `H`.

The class of rings is the paper's own: part (1) reads "for a ring whose projective modules are
direct sums of finitely generated modules", which is `EveryProjectiveIsSumOfFG R` verbatim — the
corollary does not ask for hereditariness, and neither does this statement.

**A correction to the paper's transcription.**  The condition is quantified over `1 ≤ i ≠ j ≤ 2`,
so each of its two clauses has two instances, and both are needed.  Without the `X₂`-half of the first clause a finite and an infinite form could
share a value, so condition (iii) of Theorem 5.3 would not follow; and the two halves of the second
clause are exactly condition (ii) of Theorem 5.3 for the two orderings.

(i) ⇒ (ii): adding `ℵ₀ x_j` to a relation with one infinite and one finite `X_i`-coefficient turns
it into the hypothesis of Theorem 5.3(i), whose conclusion `x_i ∈ add x_j` is excluded; the second
clause is Theorem 5.3(ii).  (ii) ⇒ (i): Theorem 5.3(i) holds vacuously — its hypothesis would make
an infinite coefficient equal a finite one — (ii) is the assumption, and (iii) follows from the
first clause. -/
theorem corollary_5_5_one (h₁ : x₁ ∉ add(x₂))
    (h₂ : x₂ ∉ add(x₁))
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    IsRealizableAsV H ↔
      ((∀ F G : Form, eval x₁ x₂ F = eval x₁ x₂ G → (F.1 = ⊤ ↔ G.1 = ⊤) ∧ (F.2 = ⊤ ↔ G.2 = ⊤)) ∧
        (∀ F G : Form, F.1 = ⊤ → G.1 = ⊤ → eval x₁ x₂ F = eval x₁ x₂ G →
          ∃ m₁ m₂ : ℕ, eval x₁ x₂ ((m₁ : ℕ∞), F.2) = eval x₁ x₂ ((m₂ : ℕ∞), G.2)) ∧
        (∀ F G : Form, F.2 = ⊤ → G.2 = ⊤ → eval x₁ x₂ F = eval x₁ x₂ G →
          ∃ n₁ n₂ : ℕ, eval x₁ x₂ (F.1, (n₁ : ℕ∞)) = eval x₁ x₂ (G.1, (n₂ : ℕ∞)))) := by
  constructor
  · rintro ⟨R, _, hfg, e, hhom, hbij⟩
    obtain ⟨hc1, hc1', hc2, hc2', hmix⟩ :=
      theorem_5_3_forward x₁ x₂ R hfg hgen hnoncyclic e hhom hbij
    -- an infinite `X₁`-coefficient against a finite one would give `x₁ ∈ add x₂`
    have key1 : ∀ F G : Form, eval x₁ x₂ F = eval x₁ x₂ G → F.1 = ⊤ → G.1 ≠ ⊤ → False := by
      intro F G hFG hF hG
      obtain ⟨m, hm⟩ : ∃ m : ℕ, G.1 = (m : ℕ∞) := ⟨G.1.toNat, (ENat.natCast_toNat hG).symm⟩
      refine h₁ (hc1 m ?_).2
      have hadd : eval x₁ x₂ F + ℵ₀∙x₂
          = eval x₁ x₂ G + ℵ₀∙x₂ := by rw [hFG]
      rw [eval, eval, hF, hm, add_assoc, add_assoc, ecmul_add_cmul_top, ecmul_add_cmul_top,
        ecmul_top, ecmul_natCast] at hadd
      exact hadd.symm
    -- and symmetrically for the `X₂`-coefficient
    have key2 : ∀ F G : Form, eval x₁ x₂ F = eval x₁ x₂ G → F.2 = ⊤ → G.2 ≠ ⊤ → False := by
      intro F G hFG hF hG
      obtain ⟨n, hn⟩ : ∃ n : ℕ, G.2 = (n : ℕ∞) := ⟨G.2.toNat, (ENat.natCast_toNat hG).symm⟩
      refine h₂ (hc1' n ?_).2
      have hadd : eval x₁ x₂ F + ℵ₀∙x₁
          = eval x₁ x₂ G + ℵ₀∙x₁ := by rw [hFG]
      have hL : eval x₁ x₂ F + ℵ₀∙x₁
          = ℵ₀∙x₂ + ℵ₀∙x₁ := by
        rw [eval, hF]
        calc ecmul F.1 x₁ + ecmul (⊤ : ℕ∞) x₂ + ℵ₀∙x₁
            = (ecmul F.1 x₁ + ℵ₀∙x₁) + ecmul (⊤ : ℕ∞) x₂ := by abel
          _ = ℵ₀∙x₂ + ℵ₀∙x₁ := by
              rw [ecmul_add_cmul_top, ecmul_top, add_comm]
      have hR : eval x₁ x₂ G + ℵ₀∙x₁ = n • x₂ + ℵ₀∙x₁ := by
        rw [eval, hn]
        calc ecmul G.1 x₁ + ecmul ((n : ℕ) : ℕ∞) x₂ + ℵ₀∙x₁
            = (ecmul G.1 x₁ + ℵ₀∙x₁)
              + ecmul ((n : ℕ) : ℕ∞) x₂ := by abel
          _ = _ := by
              rw [ecmul_add_cmul_top, ecmul_natCast, add_comm]
      rw [hL, hR] at hadd
      exact hadd.symm
    have hcl1 : ∀ F G : Form, eval x₁ x₂ F = eval x₁ x₂ G →
        (F.1 = ⊤ ↔ G.1 = ⊤) ∧ (F.2 = ⊤ ↔ G.2 = ⊤) := by
      intro F G hFG
      exact ⟨⟨fun h => not_not.mp fun hc => key1 F G hFG h hc,
          fun h => not_not.mp fun hc => key1 G F hFG.symm h hc⟩,
        ⟨fun h => not_not.mp fun hc => key2 F G hFG h hc,
          fun h => not_not.mp fun hc => key2 G F hFG.symm h hc⟩⟩
    refine ⟨hcl1, fun F G hF hG hFG => ?_, fun F G hF hG hFG => ?_⟩
    · -- both `X₁`-coefficients infinite: Theorem 5.3(ii) for the ordering `(x₂, x₁)`
      by_cases hF2 : F.2 = ⊤
      · exact ⟨0, 0, by rw [hF2, ((hcl1 F G hFG).2).mp hF2]⟩
      obtain ⟨a, ha⟩ : ∃ a : ℕ, F.2 = (a : ℕ∞) := ⟨F.2.toNat, (ENat.natCast_toNat hF2).symm⟩
      have hG2 : G.2 ≠ ⊤ := fun h => hF2 (((hcl1 F G hFG).2).mpr h)
      obtain ⟨b, hb⟩ : ∃ b : ℕ, G.2 = (b : ℕ∞) := ⟨G.2.toNat, (ENat.natCast_toNat hG2).symm⟩
      have e1 : F = ((⊤ : ℕ∞), ((a : ℕ) : ℕ∞)) := by rw [← hF, ← ha]
      have e2 : G = ((⊤ : ℕ∞), ((b : ℕ) : ℕ∞)) := by rw [← hG, ← hb]
      obtain ⟨k, k', hkk'⟩ := hc2' h₂ a b (by
        rw [eval_swap x₂ x₁, eval_swap x₂ x₁]
        show eval x₁ x₂ ((⊤ : ℕ∞), ((a : ℕ) : ℕ∞)) = eval x₁ x₂ ((⊤ : ℕ∞), ((b : ℕ) : ℕ∞))
        rw [← e1, ← e2]
        exact hFG)
      refine ⟨k, k', ?_⟩
      rw [ha, hb]
      rw [eval_swap x₂ x₁, eval_swap x₂ x₁] at hkk'
      exact hkk'
    · -- both `X₂`-coefficients infinite: Theorem 5.3(ii) for the ordering `(x₁, x₂)`
      by_cases hF1 : F.1 = ⊤
      · exact ⟨0, 0, by rw [hF1, ((hcl1 F G hFG).1).mp hF1]⟩
      obtain ⟨a, ha⟩ : ∃ a : ℕ, F.1 = (a : ℕ∞) := ⟨F.1.toNat, (ENat.natCast_toNat hF1).symm⟩
      have hG1 : G.1 ≠ ⊤ := fun h => hF1 (((hcl1 F G hFG).1).mpr h)
      obtain ⟨b, hb⟩ : ∃ b : ℕ, G.1 = (b : ℕ∞) := ⟨G.1.toNat, (ENat.natCast_toNat hG1).symm⟩
      have e1 : F = (((a : ℕ) : ℕ∞), (⊤ : ℕ∞)) := by rw [← hF, ← ha]
      have e2 : G = (((b : ℕ) : ℕ∞), (⊤ : ℕ∞)) := by rw [← hG, ← hb]
      obtain ⟨k, k', hkk'⟩ := hc2 h₁ a b (by rw [← e1, ← e2]; exact hFG)
      exact ⟨k, k', by rw [ha, hb]; exact hkk'⟩
  · rintro ⟨hcl1, hcl2, hcl3⟩
    -- the three conditions of Theorem 5.3
    have hc1 : Cond1 x₁ x₂ := by
      intro n hn
      refine absurd ((hcl1 (((n : ℕ) : ℕ∞), ⊤) ((⊤ : ℕ∞), ⊤) ?_).1.mpr rfl) (ENat.natCast_ne_top n)
      show ecmul ((n : ℕ) : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂
        = ecmul (⊤ : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂
      rw [ecmul_natCast, ecmul_top, ecmul_top]
      exact hn
    have hc1' : Cond1 x₂ x₁ := by
      intro n hn
      refine absurd ((hcl1 ((⊤ : ℕ∞), ((n : ℕ) : ℕ∞)) ((⊤ : ℕ∞), ⊤) ?_).2.mpr rfl)
        (ENat.natCast_ne_top n)
      show ecmul (⊤ : ℕ∞) x₁ + ecmul ((n : ℕ) : ℕ∞) x₂
        = ecmul (⊤ : ℕ∞) x₁ + ecmul (⊤ : ℕ∞) x₂
      rw [ecmul_natCast, ecmul_top, ecmul_top, add_comm (ℵ₀∙x₁) (n • x₂),
        add_comm (ℵ₀∙x₁) (ℵ₀∙x₂)]
      exact hn
    have hmix : NoMixedForms x₁ x₂ := by
      rintro y ⟨⟨F, hF, hFe⟩, ⟨G, hG, hGe⟩⟩
      rcases hG with h | h
      · exact hF.1 (((hcl1 F G (hFe.trans hGe.symm)).1).mpr h)
      · exact hF.2 (((hcl1 F G (hFe.trans hGe.symm)).2).mpr h)
    obtain ⟨R, hring, -, hher, e, hhom, hbij⟩ :=
      theorem_5_3_backward x₁ x₂ (ULift.{u} ℚ) hgen hc1 hc1'
        (fun _ m n hmn => hcl3 (((m : ℕ) : ℕ∞), ⊤) (((n : ℕ) : ℕ∞), ⊤) rfl rfl hmn)
        (fun _ m n hmn => by
          obtain ⟨k, k', hkk'⟩ := hcl2 ((⊤ : ℕ∞), ((m : ℕ) : ℕ∞)) ((⊤ : ℕ∞), ((n : ℕ) : ℕ∞))
            rfl rfl (by rw [eval_swap x₂ x₁, eval_swap x₂ x₁] at hmn; exact hmn)
          exact ⟨k, k', by rw [eval_swap x₂ x₁, eval_swap x₂ x₁]; exact hkk'⟩)
        hmix
    exact ⟨R, hring, Albrecht.exists_directSum_fg, e, hhom, hbij⟩

/-! ### Part (2): `add x₁ = add x₂` -/

/-- **Corollary 5.5(2)**, first claim: if `add x₁ = add x₂` then `H` has exactly one element with
an infinite form, namely `ℵ₀ x₁ = ℵ₀ x₂`.

Each generator absorbs the other by `cmul_top_absorb`, which both identifies `ℵ₀ x₁` with `ℵ₀ x₂`
and collapses every infinite form to it. -/
theorem corollary_5_5_two_unique (h : add(x₁) = add(x₂))
    (_hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H)) :
    ∀ F G : Form, F.IsInfinite → G.IsInfinite → eval x₁ x₂ F = eval x₁ x₂ G := by
  have h₁ : x₁ ∈ add(x₂) := by rw [← h]; exact KMonoid.self_mem_addOf x₁
  have h₂ : x₂ ∈ add(x₁) := by rw [h]; exact KMonoid.self_mem_addOf x₂
  have habs₁ := cmul_top_absorb x₁ x₂ h₁
  have habs₂ := cmul_top_absorb x₂ x₁ h₂
  -- the two infinite multiples agree, both being `ℵ₀ x₁ + ℵ₀ x₂`
  have heq : ℵ₀∙x₁ = ℵ₀∙x₂ := by
    have e₁ := habs₁ ⊤
    have e₂ := habs₂ ⊤
    rw [ecmul_top] at e₁ e₂
    rw [← e₂, add_comm, e₁]
  -- every infinite form evaluates to `ℵ₀ x₁`
  have key : ∀ F : Form, F.IsInfinite → eval x₁ x₂ F = ℵ₀∙x₁ := by
    intro F hF
    rcases hF with hc | hc
    · rw [eval, hc, ecmul_top]
      exact habs₂ F.2
    · rw [eval, hc, ecmul_top, add_comm, habs₁ F.1, heq]
  exact fun F G hF hG => (key F hF).trans (key G hG).symm

/-- **Corollary 5.5(2)**, equivalence: `add x₁ = add x₂` with no mixed forms is exactly
realizability by a ring whose countably (non finitely) generated projectives are all free.

**The freeness clause is over the classes of `V^{ℵ₀}(R)`** — the countably generated projectives —
rather than over all projective modules, for which it is false.  Beyond that the statement is the
paper's: unlike parts (1) and (3) it names no condition on the decompositions of projective
modules, and needs none.  Its proof of (ii) ⇒ (i) invokes Theorem 5.3's forward direction, which
does need the projectives of `R` to be direct sums of finitely generated ones — but that follows
from the freeness clause, by `everyProjectiveIsSumOfFG_of_free` (Kaplansky's theorem: a projective
is a direct sum of countably generated projectives, and each of those is here either finitely
generated or free).  This is exactly why Theorem 5.3's forward direction is stated for
`EveryProjectiveIsSumOfFG` rather than for a hereditary ring as the paper states it: hereditariness
does *not* follow here.

(i) ⇒ (ii): each generator lies in `add` of the other, so conditions (i) and (ii) of Theorem 5.3
hold — the first because `ℵ₀ x_j` absorbs `ℵ₀ x_i`, the second vacuously — and (iii) is assumed;
Theorem 5.3 then realises `H`, and `[P₂] ≼ ℵ₀ [P₁]` in both directions makes both trace ideals `R`,
so Proposition 5.4's hereditary half gives freeness.  (ii) ⇒ (i): freeness makes `ℵ₀ [P₁]` and
`ℵ₀ [P₂]` both equal to `ℵ₀ [R]`, which is the hypothesis of Theorem 5.3(i) with `n = 0`. -/
theorem corollary_5_5_two (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (add(x₁) = add(x₂) ∧ NoMixedForms x₁ x₂) ↔
      IsRealizableAsVFree H := by
  classical
  constructor
  · rintro ⟨heq, hmix⟩
    have hx₁ : x₁ ∈ add(x₂) := by
      rw [← heq]; exact KMonoid.self_mem_addOf x₁
    have hx₂ : x₂ ∈ add(x₁) := by
      rw [heq]; exact KMonoid.self_mem_addOf x₂
    -- the conditions of Theorem 5.3
    have hc1 : Cond1 x₁ x₂ := by
      intro n _
      refine ⟨?_, hx₁⟩
      have habs := cmul_top_absorb x₁ x₂ hx₁ ⊤
      rw [ecmul_top] at habs
      exact habs.symm.trans (add_comm _ _)
    have hc1' : Cond1 x₂ x₁ := by
      intro n _
      refine ⟨?_, hx₂⟩
      have habs := cmul_top_absorb x₂ x₁ hx₂ ⊤
      rw [ecmul_top] at habs
      exact habs.symm.trans (add_comm _ _)
    obtain ⟨R, hring, -, hher, e, hhom, hbij⟩ :=
      theorem_5_3_backward x₁ x₂ (ULift.{u} ℚ) hgen hc1 hc1'
        (fun hnot => absurd hx₁ hnot) (fun hnot => absurd hx₂ hnot) hmix
    refine ⟨R, hring, ?_, e, hhom, hbij⟩
    -- transport the generators back along the isomorphism
    obtain ⟨e', hleft, hright, he', hgenp, hncp⟩ :=
      exists_inv_generators x₁ x₂ hgen hnoncyclic R e hhom hbij
    -- both trace ideals are `R`
    have hkey : ∀ a b : H, b ∈ add(a) →
        e' b ≼ ℵ₀∙(e' a) := by
      intro a b hab
      obtain ⟨z, n, hzn⟩ := hab
      obtain ⟨w, hw⟩ : b ≼ ℵ₀∙a :=
        AddLe.trans ⟨z, hzn⟩ (KMonoid.cmul_le_cmul _ _
          (le_of_lt Cardinal.natCast_lt_aleph0) a)
      refine ⟨e' w, ?_⟩
      rw [← KMonoid.IsKHom.map_add he', hw, he'.map_cmul]
    have ht₁ : traceIdeal R (V(R).rep (e' x₁)) = ⊤ :=
      traceIdeal_eq_top_of_addLe R (e' x₁) (e' x₂) hgenp hncp (hkey x₁ x₂ hx₂)
    have ht₂ : traceIdeal R (V(R).rep (e' x₂)) = ⊤ :=
      traceIdeal_eq_top_of_addLe R (e' x₂) (e' x₁) (by rwa [Set.pair_comm]) hncp
        (hkey x₂ x₁ hx₁)
    exact (prop_5_4_hereditary R Albrecht.exists_directSum_fg (e' x₁) (e' x₂) hgenp hncp).mp
      (ht₁.trans ht₂.symm)
  · rintro ⟨R, hring, hfree, e, hhom, hbij⟩
    -- Theorem 5.3's forward direction needs `EveryProjectiveIsSumOfFG`; freeness supplies it
    have hfg : EveryProjectiveIsSumOfFG R := everyProjectiveIsSumOfFG_of_free R hfree
    obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
    obtain ⟨e', hleft, hright, he', hgenp, hncp⟩ :=
      exists_inv_generators x₁ x₂ hgen hnoncyclic R e hhom hbij
    obtain ⟨hne₁, hne₂⟩ := ne_zero_of_not_cyclic (e' x₁) (e' x₂) hgenp hncp
    -- both `ℵ₀ [P_i]` are `ℵ₀ [R]`, hence equal
    have hcm : ℵ₀∙x₁ = ℵ₀∙x₂ := by
      have h₁ := cmul_top_eq_unitClass_of_free R k (e' x₁) hne₁ hfree
      have h₂ := cmul_top_eq_unitClass_of_free R k (e' x₂) hne₂ hfree
      have hstep : ℵ₀∙(e' x₁)
          = ℵ₀∙(e' x₂) := h₁.trans h₂.symm
      have := congrArg e hstep
      rwa [hhom.map_cmul, hhom.map_cmul, hright x₁, hright x₂] at this
    -- Theorem 5.3(i) with `n = 0`
    obtain ⟨hc1, hc1', -, -, hmix⟩ :=
      theorem_5_3_forward x₁ x₂ R hfg hgen hnoncyclic e hhom hbij
    have habs : ∀ a b : H, ℵ₀∙a
        = ℵ₀∙b → (0 : ℕ) • a + ℵ₀∙b = ℵ₀∙a + ℵ₀∙b := by
      intro a b hab
      rw [zero_nsmul, zero_add, hab, cmul_top_add_self]
    refine ⟨le_antisymm (addOf_subset_of_mem ((hc1 0 (habs x₁ x₂ hcm)).2))
      (addOf_subset_of_mem ((hc1' 0 (habs x₂ x₁ hcm.symm)).2)), hmix⟩

/-! ### Part (3): `add x₁ ⊊ add x₂` -/

/-- **Corollary 5.5(3)**, first claim: `x₁ ∈ add x₂` forces `ℵ₀ x₂ + β x₁ = ℵ₀ x₂` for every `β`.
Generation is not needed — this is `cmul_top_absorb`. -/
theorem corollary_5_5_three_absorb (h : x₁ ∈ add(x₂))
    (_hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H)) (β : ℕ∞) :
    ℵ₀∙x₂ + ecmul β x₁ = ℵ₀∙x₂ :=
  cmul_top_absorb x₁ x₂ h β

/-- **Corollary 5.5(3)**, equivalence: for `add x₁ ⊊ add x₂`, realizability is equivalent to an
explicit relation condition.

`EveryProjectiveIsSumOfFG R` is the paper's own condition here, as in part (1): "a ring `R` over
which projective modules are direct sums of finitely generated modules".  The paper's part (3) also
records two further reformulations of realizability — that `R` may be taken with a finitely
generated projective `P` whose `P^{(ℵ₀)}` is not free, and that this is the same as
`Tr(P₁) ⊊ Tr(P₂)`.  Those are `corollary_5_5_three_nonfree` and `corollary_5_5_three_trace`.

(i) ⇒ (ii): condition (i) of Theorem 5.3 for the ordered pair `(x₂, x₁)` gives `β` finite — an
infinite `β` would put `x₂` in `add x₁` — and condition (ii) for that pair is the relation.
(ii) ⇒ (i): Theorem 5.3(i) holds for `(x₁, x₂)` because `x₁ ∈ add x₂` and `ℵ₀ x₂` absorbs `ℵ₀ x₁`,
and vacuously for `(x₂, x₁)`; (ii) holds vacuously for `(x₁, x₂)` and is the assumption for
`(x₂, x₁)`. -/
theorem corollary_5_5_three (h₁ : x₁ ∈ add(x₂))
    (h₂ : x₂ ∉ add(x₁))
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    Relations3 x₁ x₂ ∧ NoMixedForms x₁ x₂ ↔
      IsRealizableAsV H := by
  classical
  -- the two readings of `ℵ₀ x₁ + a x₂`
  have hev : ∀ a : ℕ, eval x₁ x₂ ((⊤ : ℕ∞), ((a : ℕ) : ℕ∞)) = a • x₂ + ℵ₀∙x₁ := by
    intro a
    rw [eval, ecmul_top, ecmul_natCast, add_comm]
  have hevtop : eval x₁ x₂ ((⊤ : ℕ∞), (⊤ : ℕ∞))
      = ℵ₀∙x₂ + ℵ₀∙x₁ := by
    rw [eval, ecmul_top, ecmul_top, add_comm]
  constructor
  · rintro ⟨hrel, hmix⟩
    -- Theorem 5.3(i) for `(x₁, x₂)`
    have hc1 : Cond1 x₁ x₂ := by
      intro n _
      refine ⟨?_, h₁⟩
      have habs := cmul_top_absorb x₁ x₂ h₁ ⊤
      rw [ecmul_top] at habs
      exact habs.symm.trans (add_comm _ _)
    -- and vacuously for `(x₂, x₁)`
    have hc1' : Cond1 x₂ x₁ := by
      intro n hn
      exact absurd ((hrel n ⊤ (by rw [hev n, hevtop]; exact hn)).1) (fun h => h rfl)
    refine (theorem_5_3 x₁ x₂ (ULift.{u} ℚ) hgen hnoncyclic).mpr
      ⟨hc1, hc1', fun hnot => absurd h₁ hnot, fun _ m n hmn => ?_, hmix⟩
      |>.imp fun R hR => ?_
    · -- Theorem 5.3(ii) for `(x₂, x₁)` is the relation condition
      obtain ⟨-, a, a', ha⟩ := hrel n ((m : ℕ) : ℕ∞)
        (by rw [eval_swap x₂ x₁, eval_swap x₂ x₁] at hmn; exact hmn.symm)
      exact ⟨a, a', by rw [eval_swap x₂ x₁, eval_swap x₂ x₁]; exact ha⟩
    · obtain ⟨hring, -, hher, he⟩ := hR
      exact ⟨hring, Albrecht.exists_directSum_fg, he⟩
  · rintro ⟨R, hring, hfg, e, hhom, hbij⟩
    obtain ⟨-, hc1', -, hc2', hmix⟩ :=
      theorem_5_3_forward x₁ x₂ R hfg hgen hnoncyclic e hhom hbij
    refine ⟨fun n β hβ => ?_, hmix⟩
    have hne : β ≠ ⊤ := by
      rintro rfl
      exact h₂ (hc1' n (by rw [← hev n, ← hevtop]; exact hβ)).2
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, β = (b : ℕ∞) := ⟨β.toNat, (ENat.natCast_toNat hne).symm⟩
    refine ⟨hne, ?_⟩
    obtain ⟨k, k', hkk'⟩ := hc2' h₂ b n
      (by rw [eval_swap x₂ x₁, eval_swap x₂ x₁]; exact hβ.symm)
    exact ⟨k, k', by rw [eval_swap x₂ x₁, eval_swap x₂ x₁] at hkk'; exact hkk'⟩

/-! ### The other two clauses of Corollary 5.5(3)

The paper states part (3) as a *three*-way equivalence: besides the relation condition it records
that the realizing ring may be taken with a finitely generated projective `P` whose `P^{(ℵ₀)}` is
not free, and that this is the same as having two finitely generated projective generators with
`Tr(P₁) ⊊ Tr(P₂)`.  Both extra clauses come from `cor_5_5_three_data` below.

The step the paper's proof makes module-theoretically — "since `P₂` is finitely generated, this
means `[P₂] ∈ add([P₁])`" — is not needed: what has to be excluded is `[P₂] ≼ ℵ₀ [P₁]`, and that
already contradicts `x₂ ∉ add x₁` through condition (i) of Theorem 5.3 for the ordered pair
`(x₂, x₁)`, since `ℵ₀ x₁ + ℵ₀ x₂ = ℵ₀ x₁` then holds. -/

/-- **The module-side data behind Corollary 5.5(3)**.  A realization of `H` by `V^{ℵ₀}(R)`, in the
situation `x₁ ∈ add x₂` and `x₂ ∉ add x₁`, carries two finitely generated projective generators
`P₁`, `P₂` with `Tr(P₁) ⊊ Tr(P₂)` and with `P₁^{(ℵ₀)}` not free.

`Tr(P₂) = R` because `[P₁] ≼ ℵ₀ [P₂]`.  Both of the other two claims reduce to the same thing:
`Tr(P₁) = R` would put `[R]`, hence `[P₂]`, below `ℵ₀ [P₁]`, and a free `P₁^{(ℵ₀)}` would force
`Tr(P₁) = R` (`traceIdeal_eq_top_of_iso_free`).  And `[P₂] ≼ ℵ₀ [P₁]` is impossible: transported to
`H` it gives `ℵ₀ x₁ + ℵ₀ x₂ = ℵ₀ x₁`, which is condition (i) of Theorem 5.3 for `(x₂, x₁)` at
`n = 0`, and that condition concludes `x₂ ∈ add x₁`. -/
theorem cor_5_5_three_data (h₁ : x₁ ∈ add(x₂))
    (h₂ : x₂ ∉ add(x₁))
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H))
    (R : Type u) [Ring R] (hfg : EveryProjectiveIsSumOfFG R)
    (e : V(R).carrier → H)
    (hhom : letI := V(R).instKMonoid le_rfl; KMonoid.IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) :
    ∃ p₁ p₂ : V(R).carrier,
      Module.Finite R (V(R).rep p₁) ∧
        Module.Finite R (V(R).rep p₂) ∧
        KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set V(R).carrier) ∧
        traceIdeal R (V(R).rep p₁)
          < traceIdeal R (V(R).rep p₂) ∧
        ¬ ∃ ι : Type u, Nonempty (DirectSum ℕ (fun _ => V(R).rep p₁)
            ≃ₗ[R] DirectSum ι (fun _ => R)) := by
  classical
  let := IsLSubset.lmonoid Cardinal.isRegular_aleph0
    (V(R).lambdaSmallPart_isLSubset le_rfl ℵ₀ Cardinal.isRegular_aleph0 (Order.le_succ ℵ₀))
  obtain ⟨k⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
  obtain ⟨e', hleft, hright, he', hgenp, hncp⟩ :=
    exists_inv_generators x₁ x₂ hgen hnoncyclic R e hhom hbij
  obtain ⟨hne₁, hne₂⟩ := ne_zero_of_not_cyclic (e' x₁) (e' x₂) hgenp hncp
  -- Theorem 5.3(i) for the ordered pair `(x₂, x₁)`
  obtain ⟨-, hc1', -, -, -⟩ := theorem_5_3_forward x₁ x₂ R hfg hgen hnoncyclic e hhom hbij
  -- `x₂ ≼ ℵ₀ x₁` is impossible
  have hkeyH : ¬ (x₂ ≼ ℵ₀∙x₁) := by
    rintro ⟨c, hc⟩
    have habs : ℵ₀∙x₂ + ℵ₀∙c
        = ℵ₀∙x₁ := by
      rw [← KMonoid.cmul_top_distrib, hc, KMonoid.cmul_top_idem]
    refine h₂ (hc1' 0 ?_).2
    rw [zero_nsmul, zero_add, KMonoid.add_cmul_top_eq habs]
  -- transporting `≼ ℵ₀ ·` in both directions along the isomorphism
  have hdown : ∀ a b : H, b ∈ add(a) →
      e' b ≼ ℵ₀∙(e' a) := by
    intro a b hab
    obtain ⟨z, n, hzn⟩ := hab
    obtain ⟨w, hw⟩ : b ≼ ℵ₀∙a :=
      AddLe.trans ⟨z, hzn⟩ (KMonoid.cmul_le_cmul _ _
        (le_of_lt Cardinal.natCast_lt_aleph0) a)
    exact ⟨e' w, by rw [← KMonoid.IsKHom.map_add he', hw, he'.map_cmul]⟩
  have hup : ∀ a b : V(R).carrier,
      b ≼ ℵ₀∙a → e b ≼ ℵ₀∙(e a) := by
    rintro a b ⟨c, hc⟩
    exact ⟨e c, by rw [← KMonoid.IsKHom.map_add hhom, hc, hhom.map_cmul]⟩
  -- both generators are finitely generated
  have hWsub := V(R).lambdaSmallPart_isLSubset le_rfl ℵ₀
    Cardinal.isRegular_aleph0 (Order.le_succ ℵ₀)
  have hWsat : ∀ a ∈ V(R).lambdaSmallPart ℵ₀,
      ∀ b c : V(R).carrier, a = b + c →
      b ∈ V(R).lambdaSmallPart ℵ₀ :=
    fun a ha b c habc =>
      V(R).lambdaSmallPart_summand le_rfl ℵ₀ a ha b ⟨c, habc.symm⟩
  obtain ⟨hp₁W, hp₂W⟩ := mem_of_divisorClosed_of_generates (e' x₁) (e' x₂) hWsat
    ((corollary_4_5_three.{u, u} R ℵ₀ le_rfl hfg).1.kGenerates_coe) hgenp hncp
  have hfin₁ : Module.Finite R (V(R).rep (e' x₁)) :=
    finite_of_isLambdaSmall_aleph0 R ℵ₀ (e' x₁).out
      (V(R).isLambdaSmall_of_mem hp₁W)
  have hfin₂ : Module.Finite R (V(R).rep (e' x₂)) :=
    finite_of_isLambdaSmall_aleph0 R ℵ₀ (e' x₂).out
      (V(R).isLambdaSmall_of_mem hp₂W)
  -- `Tr(P₂) = R`, because `[P₁] ≼ ℵ₀ [P₂]`
  have htop₂ : traceIdeal R (V(R).rep (e' x₂)) = ⊤ :=
    traceIdeal_eq_top_of_addLe R (e' x₂) (e' x₁) (by rwa [Set.pair_comm]) hncp
      (hdown x₂ x₁ h₁)
  -- `Tr(P₁) ≠ R`, because it would put `[P₂]` below `ℵ₀ [P₁]`
  have hnottop : traceIdeal R (V(R).rep (e' x₁)) ≠ ⊤ := by
    intro htop
    refine hkeyH ?_
    have h3 : e' x₂ ≼ ℵ₀∙(e' x₁) :=
      AddLe.trans (Projective.isOrderUnit_unitClass R ℵ₀ le_rfl k (e' x₂))
        (cmul_top_unitClass_addLe R (e' x₁) k htop)
    have := hup (e' x₁) (e' x₂) h3
    rwa [hright x₁, hright x₂] at this
  refine ⟨e' x₁, e' x₂, hfin₁, hfin₂, hgenp, htop₂ ▸ lt_top_iff_ne_top.mpr hnottop, ?_⟩
  -- a free `P₁^{(ℵ₀)}` would make `Tr(P₁) = R`
  rintro ⟨ι, ⟨eι⟩⟩
  exact hnottop (traceIdeal_eq_top_of_iso_free R (ι := ι) hne₁
    ⟨((rep_cmul_top_dsum R (e' x₁)).some.trans
      (DirectSum.lequivCongrLeft R (idxEquivNats.{u}.trans Equiv.ulift))).trans eι⟩)

/-- **Corollary 5.5(3)**, the clause the paper states first: the relation condition is equivalent
to realizability by a ring which, in addition, carries a finitely generated projective module `P`
with `P^{(ℵ₀)}` not free. -/
theorem corollary_5_5_three_nonfree (h₁ : x₁ ∈ add(x₂))
    (h₂ : x₂ ∉ add(x₁))
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    Relations3 x₁ x₂ ∧ NoMixedForms x₁ x₂ ↔
      IsRealizableAsVNonfree H := by
  refine ⟨fun h => ?_, fun h => (corollary_5_5_three x₁ x₂ h₁ h₂ hgen hnoncyclic).mpr ?_⟩
  · obtain ⟨R, hring, hfg, e, hhom, hbij⟩ :=
      (corollary_5_5_three x₁ x₂ h₁ h₂ hgen hnoncyclic).mp h
    obtain ⟨p₁, -, hfin₁, -, -, -, hnofree⟩ :=
      cor_5_5_three_data x₁ x₂ h₁ h₂ hgen hnoncyclic R hfg e hhom hbij
    exact ⟨R, hring, hfg, ⟨p₁, hfin₁, hnofree⟩, e, hhom, hbij⟩
  · obtain ⟨R, hring, hfg, -, e, hhom, hbij⟩ := h
    exact ⟨R, hring, hfg, e, hhom, hbij⟩

/-- **Corollary 5.5(3)**, the trace-ideal clause: the relation condition is equivalent to
realizability by a ring with two finitely generated projective generators `P₁`, `P₂` of
`V^{ℵ₀}(R)` satisfying `Tr(P₁) ⊊ Tr(P₂)`.

No condition on the decompositions of projective modules is needed here: generation by finitely
generated classes supplies it (`everyProjectiveIsSumOfFG_of_kGenerates_finite`). -/
theorem corollary_5_5_three_trace (h₁ : x₁ ∈ add(x₂))
    (h₂ : x₂ ∉ add(x₁))
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    Relations3 x₁ x₂ ∧ NoMixedForms x₁ x₂ ↔
      IsRealizableAsVTracePair H := by
  refine ⟨fun h => ?_, fun h => (corollary_5_5_three x₁ x₂ h₁ h₂ hgen hnoncyclic).mpr ?_⟩
  · obtain ⟨R, hring, hfg, e, hhom, hbij⟩ :=
      (corollary_5_5_three x₁ x₂ h₁ h₂ hgen hnoncyclic).mp h
    obtain ⟨p₁, p₂, hfin₁, hfin₂, hgenp, hlt, -⟩ :=
      cor_5_5_three_data x₁ x₂ h₁ h₂ hgen hnoncyclic R hfg e hhom hbij
    exact ⟨R, hring, p₁, p₂, hfin₁, hfin₂, hgenp, hlt, e, hhom, hbij⟩
  · obtain ⟨R, hring, p₁, p₂, hfin₁, hfin₂, hgenp, -, e, hhom, hbij⟩ := h
    refine ⟨R, hring, ?_, e, hhom, hbij⟩
    refine everyProjectiveIsSumOfFG_of_kGenerates_finite R {p₁, p₂} ?_ hgenp
    rintro p (rfl | rfl)
    · exact hfin₁
    · exact hfin₂

end Cor55

end TwoGen

end KappaMonoid
