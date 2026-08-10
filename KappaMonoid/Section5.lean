/-
**Scaffolding for Section 5** of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*:

*Realization to hereditary rings for two-generated `ℵ₀`-monoids.*

Every proof here is `sorry`.  The file is deliberately **not** imported by `KappaMonoid.lean`, so
`lake build` continues to check a `sorry`-free development; build it on its own with

    lake build KappaMonoid.Section5

Section 5 classifies the non-cyclic `ℵ₀`-monoids on two generators that arise as `V^{ℵ₀}(R)` for
a hereditary ring.  It is written throughout in terms of *forms* `α X₁ + β X₂` with coefficients
in `{0, 1, 2, …, ℵ₀}`, encoded here as `ℕ∞` and pushed into `Cardinal` by `Cardinal.ofENat`.

Two things to know before starting:

* Lemma 5.1 and both directions of Theorem 5.3 go through Corollary 4.7(1), which is still `sorry`
  in `KappaMonoid/Section4.lean` and rests on axiom A5.  Nothing downstream of them closes first.
* Proposition 5.4 needs trace ideals, which Mathlib does not have.  They are developed here from
  scratch rather than assumed — the two facts involved are elementary.

See `SECTION5-PLAN.md`.
-/
import KappaMonoid.Section4

universe u

open Cardinal Function Set

namespace KappaMonoid

namespace TwoGen

/-! ## Forms

A *form* `α X₁ + β X₂` records how many copies of each generator a family uses.  `ℕ∞` is exactly
`{0, 1, 2, …, ℵ₀}`, and it makes "is this coefficient finite?" decidable, which every proof in the
section branches on. -/

variable {H : Type u} [KMonoid ℵ₀ H]

/-- A **form** `α X₁ + β X₂`: a pair of coefficients in `{0, 1, 2, …, ℵ₀}`. -/
abbrev Form : Type := ℕ∞ × ℕ∞

/-- `a` copies of `x`, where `a = ⊤` means `ℵ₀` copies. -/
noncomputable def ecmul (a : ℕ∞) (x : H) : H :=
  KMonoid.cmul (κ := ℵ₀) (Cardinal.ofENat a) (Cardinal.ofENat_le_aleph0 a) x

@[simp] theorem ecmul_top (x : H) : ecmul (⊤ : ℕ∞) x = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x := by
  simp [ecmul]

/-- The element of `H` represented by a form. -/
noncomputable def eval (x₁ x₂ : H) (F : Form) : H := ecmul F.1 x₁ + ecmul F.2 x₂

/-- A form is *infinite* if at least one coefficient is. -/
def Form.IsInfinite (F : Form) : Prop := F.1 = ⊤ ∨ F.2 = ⊤

/-- A form is *finite* otherwise. -/
def Form.IsFinite (F : Form) : Prop := F.1 ≠ ⊤ ∧ F.2 ≠ ⊤

theorem Form.not_isInfinite_iff (F : Form) : ¬ F.IsInfinite ↔ F.IsFinite := by
  simp [Form.IsInfinite, Form.IsFinite, not_or]

/-- The index type of a family in an `ℵ₀`-monoid: `ℕ`, lifted into `Type u` because `BraidingData`
indexes by a type in the cardinal's universe. -/
abbrev Nats : Type u := ULift.{u} ℕ

/-- The family `(y_k)_{k ∈ ℕ}` realising a form: the first `α` slots hold `x₁`, the next `β` hold
`x₂`, and the rest are `0`. -/
noncomputable def familyOfForm (x₁ x₂ : H) (F : Form) : Nats.{u} → H :=
  fun n => if (n.down : ℕ∞) < F.1 then x₁ else if (n.down : ℕ∞) < F.1 + F.2 then x₂ else 0

theorem mk_nats_le_aleph0 : #(Nats.{u}) ≤ (ℵ₀ : Cardinal.{u}) := by
  simp [Nats]

/-- The family of a form sums to the element the form represents. -/
theorem sumOf_familyOfForm (x₁ x₂ : H) (F : Form) :
    KMonoid.sumOf (κ := ℵ₀) mk_nats_le_aleph0 (familyOfForm x₁ x₂ F) = eval x₁ x₂ F := by
  sorry

/-- `y` **has a finite form**. -/
def HasFiniteForm (x₁ x₂ y : H) : Prop := ∃ F : Form, F.IsFinite ∧ eval x₁ x₂ F = y

/-- `y` **has an infinite form**. -/
def HasInfiniteForm (x₁ x₂ y : H) : Prop := ∃ F : Form, F.IsInfinite ∧ eval x₁ x₂ F = y

/-- The condition (iii) of Theorem 5.3: no element of `H` has both a finite and an infinite form.
This is the hypothesis that most of Lemma 5.2 runs on. -/
def NoMixedForms (x₁ x₂ : H) : Prop :=
  ∀ y : H, ¬ (HasFiniteForm x₁ x₂ y ∧ HasInfiniteForm x₁ x₂ y)

/-- Two forms are **braided over `add (x₁ + x₂)`** when their families are.

The families take values in `H`; braiding is a statement about the `ℵ₀⁻`-monoid `add (x₁ + x₂)`,
so the members must be produced there.  `hmem` is that side condition, discharged in practice by
`KMonoid.addOf_isSaturated` from `Section4.lean`. -/
def BraidedForms (x₁ x₂ : H) (F G : Form)
    (hF : ∀ n, familyOfForm x₁ x₂ F n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hG : ∀ n, familyOfForm x₁ x₂ G n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) : Prop :=
  letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
  IsBraided ℵ₀ (ι := Nats.{u})
    (fun n => (⟨familyOfForm x₁ x₂ F n, hF n⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))
    (fun n => (⟨familyOfForm x₁ x₂ G n, hG n⟩ : ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))))

/-! ## Lemma 5.1

If `H ≅ V^{ℵ₀}(R)` for a ring whose projectives are direct sums of finitely generated modules,
then `x₁` and `x₂` are classes of finitely generated modules, `H` is braided over `add (x₁ + x₂)`,
and `V(R) ≅ add (x₁ + x₂) = ⟨x₁, x₂⟩`. -/

section Lemma51

variable (R : Type u) [Ring R]

/-- **Lemma 5.1**: two generators of `V^{ℵ₀}(R)` force braidedness over `add (x₁ + x₂)`.

Follows from `corollary_4_5_three` and `corollary_4_7_one_backward`.  The step needing care is
that *both* `x₁` and `x₂` must arise from finitely generated modules: otherwise `V(R)` would be
cyclic, hence so would `V^{ℵ₀}(R)`, contradicting non-cyclicity.  That is where the non-cyclicity
hypothesis first bites. -/
theorem lemma_5_1 (hfg : EveryProjectiveIsSumOfFG R) (x₁ x₂ : H)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H))
    (e : H → (projClass R ℵ₀ le_rfl).carrier)
    (hhom : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl; KMonoid.IsKHom ℵ₀ e)
    (hbij : Function.Bijective e) :
    letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
    IsBraidedOver ℵ₀ ℵ₀ ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) H le_rfl (fun y => (y : H)) := by
  sorry

end Lemma51

/-! ## Lemma 5.2 (`easyfactlemma1`)

Five basic facts about forms and braiding.  Parts (1), (2) and (5) are cheap; (3) is the longest
proof in the section and (4) is its counterpart for incomparable generators. -/

section Lemma52

variable (x₁ x₂ : H)

/-- **Lemma 5.2(1)**: an infinite and a finite form cannot be braided.

In a braiding, the finite form's family is zero cofinitely often, so cofinitely many blocks
contribute `0`; reducedness (`KMonoid.isConical`, proved) then kills the infinite side. -/
theorem lemma_5_2_one (F G : Form) (hF : F.IsInfinite) (hG : G.IsFinite)
    (hFm : ∀ n, familyOfForm x₁ x₂ F n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ n, familyOfForm x₁ x₂ G n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    ¬ BraidedForms x₁ x₂ F G hFm hGm := by
  sorry

/-- **Lemma 5.2(2)**: two finite forms of the same element are braided over `add (x₁ + x₂)`.

Both sums lie in `add (x₁ + x₂)` by construction, so a single block suffices. -/
theorem lemma_5_2_two (F G : Form) (hF : F.IsFinite) (hG : G.IsFinite)
    (heq : eval x₁ x₂ F = eval x₁ x₂ G)
    (hFm : ∀ n, familyOfForm x₁ x₂ F n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ n, familyOfForm x₁ x₂ G n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ F G hFm hGm := by
  sorry

/-- **Lemma 5.2(3)**: if `x₁ ∈ add x₂` and no element has both a finite and an infinite form, then
`α X₁ + ℵ₀ X₂` and `β X₁ + ℵ₀ X₂` are braided, for all `α, β ≤ ℵ₀`.

The paper gives the partitions outright.  With `n x₂ = t + α x₁`:

    I₀ = {0, …, α-1},   I_k = {α + n(k-1), …, α + n(k-1) + n - 1}  (k ≥ 1),
    J_k = {nk, …, nk + n - 1}  (k ≥ 0),   u_k = α x₁,   v_0 = 0,  v_k = t  (k ≥ 1).

Build the `BraidingData` with `BraidingData.mk_finsum` (Braiding.lean), which takes finite
partitions and `finsum` equations.  The proof splits on `α` finite versus `α = ⊤`; the second case
first re-derives `m x₂ = (m'+1) x₁ + n' x₂` and then builds its own partitions.

Expect this to be the longest proof in the section. -/
theorem lemma_5_2_three (hmem : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂) (hmix : NoMixedForms x₁ x₂)
    (α β : ℕ∞)
    (hFm : ∀ n, familyOfForm x₁ x₂ (α, ⊤) n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ n, familyOfForm x₁ x₂ (β, ⊤) n ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) :
    BraidedForms x₁ x₂ (α, ⊤) (β, ⊤) hFm hGm := by
  sorry

/-- **Lemma 5.2(4)**: for incomparable generators, a braiding of `m X₁ + ℵ₀ X₂` with
`n X₁ + ℵ₀ X₂` forces a finite relation `m x₁ + k x₂ = n x₁ + k' x₂`. -/
theorem lemma_5_2_four (hmem : x₁ ∉ KMonoid.addOf (κ := ℵ₀) x₂) (hmix : NoMixedForms x₁ x₂)
    (m n : ℕ)
    (hFm : ∀ i, familyOfForm x₁ x₂ ((m : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hGm : ∀ i, familyOfForm x₁ x₂ ((n : ℕ∞), ⊤) i ∈ KMonoid.addOf (κ := ℵ₀) (x₁ + x₂))
    (hbr : BraidedForms x₁ x₂ ((m : ℕ∞), ⊤) ((n : ℕ∞), ⊤) hFm hGm) :
    ∃ k k' : ℕ, eval x₁ x₂ ((m : ℕ∞), (k : ℕ∞)) = eval x₁ x₂ ((n : ℕ∞), (k' : ℕ∞)) := by
  sorry

/-- **Lemma 5.2(5)**: if `H` is braided over `add (x₁ + x₂)`, then `x₁ ∈ add x₂` exactly when
`ℵ₀ (x₁ + x₂) = ℵ₀ x₂`.

Uses Lemma 2.14, `eq_cmul_top_of_add` in `OrderUnit.lean`, which is proved. -/
theorem lemma_5_2_five
    (hbr : letI := IsLSubset.lmonoid Cardinal.isRegular_aleph0 (KMonoid.addOf_isLSubset (κ := ℵ₀) le_rfl (x₁ + x₂))
      IsBraidedOver ℵ₀ ℵ₀ ↥(KMonoid.addOf (κ := ℵ₀) (x₁ + x₂)) H le_rfl (fun y => (y : H))) :
    x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂ ↔
      KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl (x₁ + x₂) = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ := by
  sorry

end Lemma52

/-! ## Theorem 5.3 (`hereditarycasecor`)

The main result of the section. -/

section Theorem53

variable (x₁ x₂ : H)

/-- Condition (i) of Theorem 5.3, for the ordered pair `(a, b)` of generators. -/
def Cond1 (a b : H) : Prop :=
  ∀ n : ℕ, KMonoid.cmul (κ := ℵ₀) (n : Cardinal.{u})
        (le_trans (le_of_lt Cardinal.natCast_lt_aleph0) le_rfl) a
      + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b
    = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl a + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b →
      KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b
          = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl a + KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl b
        ∧ a ∈ KMonoid.addOf (κ := ℵ₀) b

/-- Condition (ii) of Theorem 5.3, for the ordered pair `(a, b)` of generators. -/
def Cond2 (a b : H) : Prop :=
  a ∉ KMonoid.addOf (κ := ℵ₀) b →
    ∀ m n : ℕ, eval a b ((m : ℕ∞), ⊤) = eval a b ((n : ℕ∞), ⊤) →
      ∃ k k' : ℕ, eval a b ((m : ℕ∞), (k : ℕ∞)) = eval a b ((n : ℕ∞), (k' : ℕ∞))

/-- **Theorem 5.3**: a non-cyclic `ℵ₀`-monoid on two generators is `V^{ℵ₀}(R)` for a hereditary
ring exactly when conditions (i), (ii) and (iii) hold for both orderings of the generators.

The paper's `1 ≤ i ≠ j ≤ 2` is rendered as a conjunction over the two orderings rather than as
`Fin 2` bookkeeping, which would cost more than it saves.

Forward: Lemma 5.1 gives braidedness, then (iii) is 5.2(1), (ii) is 5.2(4), and (i) is the
counting argument — cofinitely many blocks sum to `|I_μ| x_j`, so `x_i ∈ add x_j`, then 5.2(3).

Backward: verify braidedness over `add (x₁ + x₂)` by the four-case split of the paper
(`fin/fin`; `m,ℵ₀` vs `m',ℵ₀`; `ℵ₀,n` vs `m,ℵ₀`; `m,ℵ₀` vs `ℵ₀,ℵ₀`), then apply Corollary 4.7(1)
— `corollary_4_7_one_forward`, which is where axiom A5 enters. -/
theorem theorem_5_3 (k : Type u) [Field k]
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (∃ (R : Type u) (_ : Ring R) (_ : Algebra k R) (_ : ∀ I : Ideal R, Module.Projective R I),
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) ↔
      (Cond1 x₁ x₂ ∧ Cond1 x₂ x₁ ∧ Cond2 x₁ x₂ ∧ Cond2 x₂ x₁ ∧ NoMixedForms x₁ x₂) := by
  sorry

end Theorem53

/-! ## Trace ideals and Proposition 5.4

Mathlib has no trace ideal — `Module.trace` is the trace of an endomorphism, unrelated — so the
definition and the two facts Proposition 5.4 rests on are developed here.  Both are elementary,
which is why they are proved rather than assumed. -/

section Trace

variable (R : Type u) [Ring R] (P : Type u) [AddCommGroup P] [Module R P]

/-- The **trace ideal** `Tr(P) = Σ_{f ∈ Hom(P,R)} im f`. -/
noncomputable def traceIdeal : Ideal R := ⨆ f : P →ₗ[R] R, LinearMap.range f

theorem le_traceIdeal (f : P →ₗ[R] R) : LinearMap.range f ≤ traceIdeal R P :=
  le_iSup (fun f : P →ₗ[R] R => LinearMap.range f) f

/-- `P = Tr(P) · P` for projective `P`.

Proof: `Module.projective_def` gives `s : P →ₗ[R] P →₀ R` splitting `linearCombination R id`, so
`x = Σ_{p ∈ supp (s x)} (s x) p • p`.  Each coefficient map `x ↦ (s x) p` is the linear functional
`Finsupp.lapply p ∘ₗ s`, hence lands in `Tr(P)`; so `x ∈ Tr(P) • ⊤`. -/
theorem smul_traceIdeal_eq [Module.Projective R P] :
    traceIdeal R P • (⊤ : Submodule R P) = ⊤ := by
  sorry

/-- `Tr(P)` is the least ideal `I` with `P = I · P`.

Proof: if `I • ⊤ = ⊤` then for any `f : P →ₗ[R] R`, `im f = f (I • ⊤) = I * im f ⊆ I`. -/
theorem traceIdeal_le_of_smul_eq {I : Ideal R} (h : I • (⊤ : Submodule R P) = ⊤) :
    traceIdeal R P ≤ I := by
  sorry

/-- `Tr(P)` is idempotent.

Proof: `Tr(P) • ⊤ = ⊤` gives `im f = f (Tr(P) • ⊤) = Tr(P) * im f ⊆ Tr(P) * Tr(P)` for every `f`,
so `Tr(P) ≤ Tr(P) * Tr(P)`; the reverse inclusion is `Ideal.mul_le_left`. -/
theorem traceIdeal_mul_self [Module.Projective R P] :
    traceIdeal R P * traceIdeal R P = traceIdeal R P := by
  sorry

end Trace

section Prop54

variable (R : Type u) [Ring R]

/-- **Proposition 5.4**: for a ring with non-cyclic `V^{ℵ₀}(R)` generated by `[P₁]` and `[P₂]`,
the four conditions `Tr(P₂) ⊆ Tr(P₁)`, `Tr(P₁) = R`, `P₂ | P₁^{(ℵ₀)}` and `P₁^{(ℵ₀)}` free are
equivalent.

The two classes are given as carrier elements `p₁ p₂` and their modules as `rep p₁`, `rep p₂` —
`ModuleClass` has no constructor taking a module to its class, only `rep` going the other way.

(i) ⇒ (ii) is `P₂ · Tr(P₁) = P₂`; (ii) ⇒ (iii) writes `1 ∈ im f₁ + ⋯ + im f_k` to split `R` off
`P₁^k`; (iii) ⇒ (iv) is Lemma 2.14 (`eq_cmul_top_of_add`, proved); (iv) ⇒ (i) is immediate. -/
theorem prop_5_4 (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier))
    (hnoncyclic : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      ∀ x : (projClass R ℵ₀ le_rfl).carrier,
        ¬ KMonoid.KGenerates ℵ₀ ({x} : Set (projClass R ℵ₀ le_rfl).carrier)) :
    (traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) ≤ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁)
        ↔ traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤) ∧
      (traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁) = ⊤ ↔
        ∃ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q),
          Nonempty (DirectSum ℕ (fun _ => (projClass R ℵ₀ le_rfl).rep p₁) ≃ₗ[R]
            (projClass R ℵ₀ le_rfl).rep p₂ × Q)) := by
  sorry

/-- **Proposition 5.4**, final statement: over a hereditary ring, `Tr(P₁) = Tr(P₂)` exactly when
every countably (non finitely) generated projective is free. -/
theorem prop_5_4_hereditary (hR : ∀ I : Ideal R, Module.Projective R I)
    (p₁ p₂ : (projClass R ℵ₀ le_rfl).carrier)
    (hgen : letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
      KMonoid.KGenerates ℵ₀ ({p₁, p₂} : Set (projClass R ℵ₀ le_rfl).carrier)) :
    traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₁)
        = traceIdeal R ((projClass R ℵ₀ le_rfl).rep p₂) ↔
      ∀ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q), Module.Projective R Q →
        ¬ Module.Finite R Q →
          (∃ ι : Type u, #ι ≤ ℵ₀ ∧ Nonempty (Q ≃ₗ[R] DirectSum ι (fun _ => R))) := by
  sorry

end Prop54

/-! ## Corollary 5.5 (`hereditarycase`)

Case analysis on how `add x₁` and `add x₂` compare.  All three parts are bookkeeping on top of
Theorem 5.3, with Proposition 5.4 for part (3)'s trace formulation. -/

section Cor55

variable (x₁ x₂ : H)

/-- **Corollary 5.5(1)**: for incomparable generators, realizability is equivalent to an explicit
condition on the relations of `H`.

(i) ⇒ (ii) adds `ℵ₀ x_j` to reduce to Theorem 5.3(i); (ii) ⇒ (i) verifies the three conditions of
Theorem 5.3, of which (i) holds vacuously. -/
theorem corollary_5_5_one (h₁ : x₁ ∉ KMonoid.addOf (κ := ℵ₀) x₂)
    (h₂ : x₂ ∉ KMonoid.addOf (κ := ℵ₀) x₁)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (∃ (R : Type u) (_ : Ring R), EveryProjectiveIsSumOfFG R ∧
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) ↔
      (∀ F G : Form, eval x₁ x₂ F = eval x₁ x₂ G → (F.1 = ⊤ ↔ G.1 = ⊤)) ∧
        (∀ F G : Form, F.1 = ⊤ → G.1 = ⊤ → eval x₁ x₂ F = eval x₁ x₂ G →
          ∃ m₁ m₂ : ℕ, eval x₁ x₂ ((m₁ : ℕ∞), F.2) = eval x₁ x₂ ((m₂ : ℕ∞), G.2)) := by
  sorry

/-- **Corollary 5.5(2)**, first claim: if `add x₁ = add x₂` then `H` has exactly one element with
an infinite form.

Proof: `x := x₁ + x₂` is an order-unit; from `x_i ∈ add x_j` one gets `ℵ₀ x_j = ℵ₀ x` by Lemma
2.14, so every infinite form represents `ℵ₀ x`. -/
theorem corollary_5_5_two_unique (h : KMonoid.addOf (κ := ℵ₀) x₁ = KMonoid.addOf (κ := ℵ₀) x₂)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H)) :
    ∀ F G : Form, F.IsInfinite → G.IsInfinite → eval x₁ x₂ F = eval x₁ x₂ G := by
  sorry

/-- **Corollary 5.5(2)**, equivalence: `add x₁ = add x₂` with no mixed forms is exactly
realizability by a ring whose countably (non finitely) generated projectives are all free. -/
theorem corollary_5_5_two (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (KMonoid.addOf (κ := ℵ₀) x₁ = KMonoid.addOf (κ := ℵ₀) x₂ ∧ NoMixedForms x₁ x₂) ↔
      (∃ (R : Type u) (_ : Ring R),
        (∀ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q), Module.Projective R Q →
          ¬ Module.Finite R Q → (∃ ι : Type u, #ι ≤ ℵ₀ ∧ Nonempty (Q ≃ₗ[R] DirectSum ι (fun _ => R)))) ∧
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) := by
  sorry

/-- **Corollary 5.5(3)**, first claim: `x₁ ∈ add x₂` forces `ℵ₀ x₂ + β x₁ = ℵ₀ x₂` for every `β`. -/
theorem corollary_5_5_three_absorb (h : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H)) (β : ℕ∞) :
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ + ecmul β x₁ = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl x₂ := by
  sorry

/-- **Corollary 5.5(3)**, equivalence: for `add x₁ ⊊ add x₂`, realizability with a non-free
`P^{(ℵ₀)}` is equivalent to an explicit relation condition, and to a strict trace inclusion. -/
theorem corollary_5_5_three (h₁ : x₁ ∈ KMonoid.addOf (κ := ℵ₀) x₂)
    (h₂ : x₂ ∉ KMonoid.addOf (κ := ℵ₀) x₁)
    (hgen : KMonoid.KGenerates ℵ₀ ({x₁, x₂} : Set H))
    (hnoncyclic : ∀ x : H, ¬ KMonoid.KGenerates ℵ₀ ({x} : Set H)) :
    (∀ (n : ℕ) (β : ℕ∞), eval x₁ x₂ (⊤, (n : ℕ∞)) = eval x₁ x₂ (⊤, β) →
        β ≠ ⊤ ∧ ∃ m m' : ℕ, eval x₁ x₂ ((m : ℕ∞), β) = eval x₁ x₂ ((m' : ℕ∞), (n : ℕ∞)))
      ∧ NoMixedForms x₁ x₂ ↔
      (∃ (R : Type u) (_ : Ring R), EveryProjectiveIsSumOfFG R ∧
        letI := (projClass R ℵ₀ le_rfl).instKMonoid le_rfl
        ∃ e : (projClass R ℵ₀ le_rfl).carrier → H,
          KMonoid.IsKHom ℵ₀ e ∧ Function.Bijective e) := by
  sorry

end Cor55

/-! ## The counterexample `ℕ₀² ∪ {∞}`

Corollary 5.5(2) and 5.5(3) each assert "the converse is not true", both witnessed by the trivial
`ℵ₀`-extension of `ℕ₀²` with `x₁ = (1,0)`, `x₂ = (0,1)`.  That is Example 2.3(1), already
formalised in `KappaMonoid/Examples.lean`, so both are cheap — and worth doing early as a check on
the encoding above. -/

section Counterexample

/-- The underlying monoid `ℕ₀²` of the counterexample, lifted into `Type u`. -/
abbrev NatSq : Type u := ULift.{u} (ℕ × ℕ)

theorem isConical_natSq : IsConical NatSq.{u} := by
  sorry

/-- The counterexample `H := ℕ₀² ∪ {∞}`, the trivial `ℵ₀`-extension of `ℕ₀²`. -/
noncomputable instance : KMonoid ℵ₀ (WithTop NatSq.{u}) :=
  TrivExt.instKMonoid isConical_natSq le_rfl

/-- `x₁ = (1,0)`. -/
def cex₁ : WithTop NatSq.{u} := ((⟨(1, 0)⟩ : NatSq.{u}) : WithTop NatSq.{u})

/-- `x₂ = (0,1)`. -/
def cex₂ : WithTop NatSq.{u} := ((⟨(0, 1)⟩ : NatSq.{u}) : WithTop NatSq.{u})

/-- In `ℕ₀² ∪ {∞}` the two generators have incomparable `add` sets. -/
theorem cex_incomparable :
    cex₁.{u} ∉ KMonoid.addOf (κ := ℵ₀) cex₂.{u} ∧
      cex₂.{u} ∉ KMonoid.addOf (κ := ℵ₀) cex₁.{u} := by
  sorry

/-- Yet `ℵ₀ x₂ + β x₁ = ℵ₀ x₂` for every `β`, both sides being `∞`.  With `cex_incomparable`
this refutes the converse asserted in Corollary 5.5(3). -/
theorem cex_absorb (β : ℕ∞) :
    KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} + ecmul β cex₁.{u}
      = KMonoid.cmul (κ := ℵ₀) ℵ₀ le_rfl cex₂.{u} := by
  sorry

/-- And `∞` is the only element with an infinite form, although `add x₁ ≠ add x₂`.  With
`cex_incomparable` this refutes the converse asserted in Corollary 5.5(2). -/
theorem cex_unique_infinite :
    (∀ F G : Form, F.IsInfinite → G.IsInfinite →
        eval cex₁.{u} cex₂.{u} F = eval cex₁.{u} cex₂.{u} G) ∧
      KMonoid.addOf (κ := ℵ₀) cex₁.{u} ≠ KMonoid.addOf (κ := ℵ₀) cex₂.{u} := by
  sorry

end Counterexample

end TwoGen

end KappaMonoid
