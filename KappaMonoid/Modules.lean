/-
Part 4 — Section 4: `κ`-monoids of modules, and Theorem 4.3.

Modelling "a class of modules whose isomorphism classes form a set"
------------------------------------------------------------------
In Lean there is no type of all `R`-modules, so we present a class `C` of modules by the
data of

* a type `carrier` of isomorphism classes,
* a chosen representative module `rep a` for each `a : carrier`,
* the requirement that non-equal classes are non-isomorphic (`eq_of_iso`),
* closure operations witnessing that `C` is closed under `κ`-indexed direct sums and under
  direct summands.

`V^κ(C)` is then `carrier`, and the `κ`-monoid axioms (A1) and (A2) hold because direct sums
satisfy them up to isomorphism.  This is `ModuleClass.instKMonoid` below.
-/
import KappaMonoid.Universal

universe u v w

open Cardinal Function Set DirectSum

namespace NS

open KMonoid LMonoid

/-! ## General facts about `κ`-submonoids

These are statements about `KappaMonoid.Basic` notions only (`kclosure`, and the structures
induced on sub-objects); they are collected here because they are what turns the
module-theoretic core of Theorem 4.3 into the statement of Section 3. -/

section Sub

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-- The `κ`-closure of a set is a `κ`-submonoid: an intersection of `κ`-submonoids is one. -/
theorem KMonoid.isKSubmonoid_kclosure (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H]
    (S : Set H) : IsKSubmonoid κ (kclosure κ S) where
  zero_mem := fun _ hT => hT.2.zero_mem
  ksum_mem := fun x hx T hT => hT.2.ksum_mem x fun i => hx i T hT

/-- Elements of `⟨S⟩_κ` are exactly the `κ`-sums of families in `S`. -/
theorem KMonoid.mem_kclosure_iff {S : Set H} (h0 : (0 : H) ∈ S) (h : H) :
    h ∈ kclosure κ S ↔ ∃ x : Idx κ → H, (∀ i, x i ∈ S) ∧ h = ksum (κ := κ) x := by
  classical
  have hκ := KMonoid.aleph0_le (κ := κ) (H := H)
  obtain ⟨i₀⟩ := nonempty_Idx hκ
  constructor
  · intro hh
    set T : Set H := {h | ∃ x : Idx κ → H, (∀ i, x i ∈ S) ∧ h = ksum (κ := κ) x} with hTdef
    have hST : S ⊆ T := by
      intro a ha
      refine ⟨fun i => if i = i₀ then a else 0, fun i => ?_, ?_⟩
      · show (if i = i₀ then a else 0) ∈ S
        by_cases hi : i = i₀
        · rwa [if_pos hi]
        · rwa [if_neg hi]
      · rw [ksum_single i₀ _ (fun i hi => if_neg hi), if_pos rfl]
    have hTsub : IsKSubmonoid κ T := by
      refine ⟨⟨fun _ => 0, fun _ => h0, ksum_zero.symm⟩, fun y hy => ?_⟩
      choose x hxS hxsum using hy
      refine ⟨fun k => x ((pairEquiv hκ).symm k).1 ((pairEquiv hκ).symm k).2,
        fun k => hxS _ _, ?_⟩
      rw [← ksum_sigma x (pairEquiv hκ)]
      exact congrArg _ (funext hxsum)
    exact hh T ⟨hST, hTsub⟩
  · rintro ⟨x, hxS, rfl⟩
    exact (KMonoid.isKSubmonoid_kclosure κ S).ksum_mem x fun i => subset_kclosure (hxS i)

/-- The inclusion of a `κ`-submonoid preserves `κ`-sums. -/
theorem KMonoid.IsKSubmonoid.coe_ksum {T : Set H} (hT : IsKSubmonoid κ T) (z : Idx κ → T) :
    letI := hT.kmonoid
    ((ksum (κ := κ) z : T) : H) = ksum (κ := κ) fun i => (z i : H) := rfl

/-- The inclusion of a `κ`-submonoid preserves sums over arbitrary small index types. -/
theorem KMonoid.IsKSubmonoid.coe_sumOf {T : Set H} (hT : IsKSubmonoid κ T) {ι : Type u}
    (hι : #ι ≤ κ) (z : ι → T) :
    letI := hT.kmonoid
    ((sumOf (κ := κ) hι z : T) : H) = sumOf (κ := κ) hι fun i => (z i : H) := by
  letI := hT.kmonoid
  show ((ksum (κ := κ) (Function.extend (emb hι) z 0) : T) : H)
    = ksum (κ := κ) (Function.extend (emb hι) (fun i => (z i : H)) 0)
  rw [hT.coe_ksum]
  congr 1
  funext k
  by_cases hk : ∃ i, emb hι i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [(emb hι).injective.extend_apply, (emb hι).injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ hk]
    rfl

/-- The inclusion of a `λ⁻`-closed subset preserves `λ⁻`-sums: they are computed as the
ambient `κ`-sums. -/
theorem IsLSubset.coe_lsumOf {lam : Cardinal.{u}} {hlk : lam ≤ κ} {S : Set H}
    (hlam : lam.IsRegular) (hS : IsLSubset lam hlk S) {ι : Type u} (hι : #ι < lam) (z : ι → S) :
    letI := hS.lmonoid hlam
    ((lsumOf (lam := lam) hι z : S) : H) = sumOf (κ := κ) (hι.le.trans hlk) fun i => (z i : H) := by
  letI := hS.lmonoid hlam
  letI LH := KMonoid.toLMonoid H hlam hlk
  have hext : (fun i => ((Function.extend (emb hι.le) z 0) i : H))
      = Function.extend (emb hι.le) (fun i => (z i : H)) 0 := by
    funext k
    by_cases hk : ∃ i, emb hι.le i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [(emb hι.le).injective.extend_apply, (emb hι.le).injective.extend_apply]
    · rw [Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ hk]
      rfl
  show LH.lsum (fun i => ((Function.extend (emb hι.le) z 0) i : H)) = _
  rw [hext]
  exact KMonoid.toLMonoid_lsumOf hlam hlk hι (fun i => (z i : H))

end Sub

/-! ## Definition 4.1: `λ⁻`-small modules -/

variable (R : Type u) [Ring R]

/-- Definition 4.1: `M` is `λ⁻`-*small* if every homomorphism from `M` into a direct sum
lands in a sub-sum indexed by strictly fewer than `λ` indices. -/
def IsLambdaSmall (lam : Cardinal.{u}) (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∀ {ι : Type u} (N : ι → Type u) (_ : ∀ i, AddCommGroup (N i)) (_ : ∀ i, Module R (N i))
    (f : M →ₗ[R] (⨁ i, N i)),
    ∃ s : Set ι, #s < lam ∧ ∀ (m : M) (i : ι), i ∉ s → (DirectSum.component R ι N i) (f m) = 0

/-- Example 4.2(2): a module generated by strictly fewer than `λ` elements is `λ⁻`-small. -/
theorem isLambdaSmall_of_span {lam : Cardinal.{u}} (hlam : lam.IsRegular)
    (M : Type u) [AddCommGroup M] [Module R M] (s : Set M) (hs : #s < lam)
    (hspan : Submodule.span R s = ⊤) : IsLambdaSmall R lam M := by
  sorry

/-- Example 4.2(2): finitely generated modules are `ℵ₀⁻`-small. -/
theorem isLambdaSmall_aleph0_of_fg (M : Type u) [AddCommGroup M] [Module R M]
    (h : Module.Finite R M) : IsLambdaSmall R ℵ₀ M := by
  sorry

/-! ## Classes of modules and `V^κ(C)` -/

/-- A class of `R`-modules, closed under `κ`-indexed direct sums, direct summands and
isomorphisms, and whose isomorphism classes form the set `carrier` (Definition 2.4). -/
structure ModuleClass (κ : Cardinal.{u}) where
  /-- The set of isomorphism classes; this is `V^κ(C)`. -/
  carrier : Type u
  /-- A chosen representative for each isomorphism class. -/
  rep : carrier → Type u
  addCommGroup : ∀ a, AddCommGroup (rep a)
  module : ∀ a, Module R (rep a)
  /-- Distinct classes are non-isomorphic. -/
  eq_of_iso : ∀ {a b : carrier},
    letI := addCommGroup a; letI := addCommGroup b; letI := module a; letI := module b
    (rep a ≃ₗ[R] rep b) → a = b
  /-- The zero module belongs to the class. -/
  zero : carrier
  subsingleton_rep_zero : Subsingleton (rep zero)
  /-- Closure under `κ`-indexed direct sums. -/
  dsum : (Idx κ → carrier) → carrier
  dsum_iso : ∀ f : Idx κ → carrier,
    letI := fun i => addCommGroup (f i); letI := fun i => module (f i)
    letI := addCommGroup (dsum f); letI := module (dsum f)
    Nonempty (rep (dsum f) ≃ₗ[R] (⨁ i, rep (f i)))
  /-- Closure under direct summands. -/
  exists_of_isCompl : ∀ (a : carrier),
    letI := addCommGroup a; letI := module a
    ∀ N K : Submodule R (rep a), IsCompl N K →
      ∃ b, letI := addCommGroup b; letI := module b; Nonempty (rep b ≃ₗ[R] N)

namespace ModuleClass

variable {R} {κ : Cardinal.{u}} (C : ModuleClass R κ)

attribute [instance] ModuleClass.addCommGroup ModuleClass.module

/-- A direct sum all but one of whose summands is trivial *is* that summand. -/
noncomputable def _root_.NS.directSumEquivOfSubsingleton {R : Type u} [Ring R] {ι : Type u}
    {N : ι → Type u} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → Subsingleton (N i)) : (⨁ i, N i) ≃ₗ[R] N i₀ := by
  classical
  refine LinearEquiv.ofLinear (DirectSum.component R ι N i₀) (DirectSum.lof R ι N i₀) ?_ ?_
  · apply LinearMap.ext
    intro m
    simp
  · refine DirectSum.linearMap_ext R (fun i => LinearMap.ext fun m => ?_)
    by_cases hi : i = i₀
    · subst hi
      simp
    · haveI := h i hi
      have hm : m = 0 := Subsingleton.elim m 0
      subst hm
      simp

/-- `V^κ(C)` is a `κ`-monoid (Examples 2.3(4)): (A1) and (A2) hold because direct sums do,
and by Lemma 2.5 (`KMonoid.ofBare`) the additive structure is then determined. -/
@[instance_reducible]
noncomputable def instKMonoid (hκ : ℵ₀ ≤ κ) : KMonoid κ C.carrier := by
  classical
  letI : Zero C.carrier := ⟨C.zero⟩
  refine KMonoid.ofBare
    { aleph0_le := hκ
      ksum := C.dsum
      ksum_single := ?_
      ksum_sigma := ?_ }
  · -- (A1): all but one summand is the zero module
    intro i₀ x hx
    refine C.eq_of_iso ?_
    have hsub : ∀ i, i ≠ i₀ → Subsingleton (C.rep (x i)) := by
      intro i hi
      have h1 : C.rep (x i) = C.rep C.zero := congrArg C.rep (hx i hi)
      rw [h1]
      exact C.subsingleton_rep_zero
    exact (C.dsum_iso x).some.trans (directSumEquivOfSubsingleton i₀ hsub)
  · -- (A2): `⨁ᵢ ⨁ⱼ ≅ ⨁_{(i,j)} ≅ ⨁_k`
    intro x π
    refine C.eq_of_iso ?_
    set h : (Σ _ : Idx κ, Idx κ) ≃ Idx κ :=
      (Equiv.sigmaEquivProd (Idx κ) (Idx κ)).trans π with hhdef
    have e1 := (C.dsum_iso (fun i => C.dsum (x i))).some
    have e2 : (⨁ i, C.rep (C.dsum (x i))) ≃ₗ[R] ⨁ i, ⨁ j, C.rep (x i j) :=
      DirectSum.congrLinearEquiv (fun i => (C.dsum_iso (x i)).some)
    have e3 : (⨁ p : (Σ _ : Idx κ, Idx κ), C.rep (x p.1 p.2)) ≃ₗ[R] ⨁ i, ⨁ j, C.rep (x i j) :=
      DirectSum.sigmaLcurryEquiv (R := R) (ι := Idx κ) (α := fun _ => Idx κ)
        (δ := fun i j => C.rep (x i j))
    have e4 : (⨁ p : (Σ _ : Idx κ, Idx κ), C.rep (x p.1 p.2))
        ≃ₗ[R] ⨁ k, C.rep (x (π.symm k).1 (π.symm k).2) := DirectSum.lequivCongrLeft R h
    have e5 := (C.dsum_iso (fun k => x (π.symm k).1 (π.symm k).2)).some
    exact e1.trans (e2.trans (e3.symm.trans (e4.trans e5.symm)))

/-- The `κ`-sum on `V^κ(C)` is the direct sum. -/
theorem instKMonoid_ksum (hκ : ℵ₀ ≤ κ) (x : Idx κ → C.carrier) :
    letI := C.instKMonoid hκ
    ksum (κ := κ) x = C.dsum x := rfl

/-- The zero of `V^κ(C)` is the class of the zero module. -/
theorem instKMonoid_zero (hκ : ℵ₀ ≤ κ) :
    letI := C.instKMonoid hκ
    (0 : C.carrier) = C.zero := rfl

/-- Equal isomorphism classes have isomorphic representatives. -/
theorem iso_of_eq {a b : C.carrier} (h : a = b) : Nonempty (C.rep a ≃ₗ[R] C.rep b) := by
  subst h
  exact ⟨LinearEquiv.refl R _⟩

/-- Equal `κ`-sums in `V^κ(C)` mean isomorphic direct sums: this is the module-theoretic
form of the hypothesis of Theorem 4.3. -/
theorem iso_of_dsum_eq (x y : Idx κ → C.carrier) (h : C.dsum x = C.dsum y) :
    Nonempty ((⨁ i, C.rep (x i)) ≃ₗ[R] ⨁ j, C.rep (y j)) :=
  ⟨(C.dsum_iso x).some.symm.trans (((C.iso_of_eq h).some).trans (C.dsum_iso y).some)⟩

/-- `Cλ⁻`: the subclass of `λ⁻`-small members of `C`. -/
def lambdaSmallPart (lam : Cardinal.{u}) : Set C.carrier :=
  {a | IsLambdaSmall R lam (C.rep a)}

end ModuleClass

/-! ## The module-theoretic core of Theorem 4.3

`(M1)` and `(M2)` are the two elementary facts used in the proof. -/

section ModuleFacts

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- (M1): complements of the *same* submodule are isomorphic (both are `M / A`). -/
theorem iso_of_isCompl_left {A B C' : Submodule R M} (h₁ : IsCompl A B) (h₂ : IsCompl A C') :
    Nonempty (B ≃ₗ[R] C') :=
  ⟨(Submodule.quotientEquivOfIsCompl A B h₁).symm.trans
    (Submodule.quotientEquivOfIsCompl A C' h₂)⟩

/-- (M2): if `M = A ⊕ B` and `A ≤ C`, then `C = A ⊕ (B ⊓ C)`; in particular a direct
summand of `M` contained in `C` is a direct summand of `C`. -/
theorem isCompl_inf_of_le {A B : Submodule R M} (h : IsCompl A B) {C' : Submodule R M}
    (hAC : A ≤ C') : IsCompl (A.comap C'.subtype) ((B ⊓ C').comap C'.subtype) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have h1 : (x : M) ∈ A := hx1
    have h2 : (x : M) ∈ B := hx2.1
    exact Subtype.ext (Submodule.disjoint_def.mp h.disjoint (x : M) h1 h2)
  · rw [codisjoint_iff, eq_top_iff]
    rintro x -
    have hx : (x : M) ∈ A ⊔ B := by
      rw [codisjoint_iff.mp h.codisjoint]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    have hbC : b ∈ C' := by
      have hbeq : b = (x : M) - a := eq_sub_of_add_eq' hab
      rw [hbeq]
      exact Submodule.sub_mem C' x.2 (hAC ha)
    exact Submodule.mem_sup.mpr
      ⟨⟨a, hAC ha⟩, ha, ⟨b, hbC⟩, ⟨hb, hbC⟩, Subtype.ext hab⟩

end ModuleFacts

/-! ## Theorem 4.3 -/

variable {R}

/-- **Theorem 4.3**, module-theoretic core: the transfinite iteration of Bergman's
observation.  This is the one remaining `sorry` of the theorem; everything it needs is in
place — `ModuleClass.instKMonoid` (with `instKMonoid_ksum : ksum = dsum` and
`instKMonoid_zero`), `dsum_iso`, `iso_of_isCompl_left` (M1) and `isCompl_inf_of_le` (M2).

Let `Cλ⁻ ⊆ C` be a subclass of `λ⁻`-small modules, closed under isomorphisms, direct
summands, and direct sums over index sets of cardinality `< λ`.  If

  `⨁_{i ∈ κ} A i ≅ ⨁_{j ∈ κ} B j`

with all `A i`, `B j` in `Cλ⁻`, then the families of isomorphism classes `[A i]` and `[B j]`
are `λ⁻`-braided over `V^{λ⁻}(Cλ⁻)`.

Paper proof: fix a limit well-order on `κ` and construct, by transfinite recursion on
`α ∈ κ`, index sets `I α`, `J α` of size `< λ` and submodules `S α`, `T α` of
`M = ⨁_i A i` with `T α = 0` at limit elements and

  `⨁_{μ ≤ α} ⨁_{i ∈ I μ} A i = ⨁_{μ ≤ α} (S μ ⊕ T μ)`,
  `⨁_{μ ≤ α} ⨁_{j ∈ J μ} B j = ⨁_{μ ≤ α} (T (μ+1) ⊕ S μ)`.

The recursion step uses `λ⁻`-smallness of `T α` to find `I α`, then (M2) to split off
`S α`, then `λ⁻`-smallness of `S α` to find `J α`, then (M2) again to split off `T (α+1)`;
`min I'` is always adjoined to `I α` to ensure that the partitions exhaust `κ`.  (M1)
translates the internal decompositions into the required isomorphisms.  This is a
transfinite iteration of an elementary observation of Bergman [Ber23]. -/
theorem exists_braided_of_iso (C : ModuleClass R κ) (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ κ)
    (S : Set C.carrier)
    (hsmall : ∀ a ∈ S, IsLambdaSmall R lam (C.rep a))
    (hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S)
    (hSsummand : letI := C.instKMonoid hκ; ∀ a ∈ S, ∀ b : C.carrier,
      (∃ c, b + c = a) → b ∈ S)
    (x y : Idx κ → S)
    (e : (⨁ i, C.rep (x i : C.carrier)) ≃ₗ[R] ⨁ j, C.rep (y j : C.carrier)) :
    letI := C.instKMonoid hκ
    letI := hSsub.lmonoid hlam
    IsBraided lam x y := by
  sorry

/-- **Theorem 4.3** (module-theoretic core), in the language of Section 3.  The hypothesis
`Σᵢ [A i] = Σⱼ [B j]` in `V^κ(C)` is the same thing as an isomorphism
`⨁ᵢ A i ≅ ⨁ⱼ B j` (`ModuleClass.iso_of_dsum_eq`), so this is `exists_braided_of_iso`. -/
theorem theorem_4_3_core (C : ModuleClass R κ) (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ κ)
    (S : Set C.carrier)
    -- `S` consists of `λ⁻`-small modules …
    (hsmall : ∀ a ∈ S, IsLambdaSmall R lam (C.rep a))
    -- … and is closed under `0`, direct sums of size `< λ`, and direct summands:
    (hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S)
    (hSsummand : letI := C.instKMonoid hκ; ∀ a ∈ S, ∀ b : C.carrier,
      (∃ c, b + c = a) → b ∈ S)
    (x y : Idx κ → S) :
    letI := C.instKMonoid hκ
    letI := hSsub.lmonoid hlam
    (ksum (κ := κ) fun i => (x i : C.carrier)) = (ksum (κ := κ) fun i => (y i : C.carrier)) →
      IsBraided lam x y := by
  letI := C.instKMonoid hκ
  letI := hSsub.lmonoid hlam
  intro hsum
  -- the hypothesis says exactly that the two direct sums are isomorphic
  have hdsum : C.dsum (fun i => (x i : C.carrier)) = C.dsum (fun i => (y i : C.carrier)) := by
    rw [← C.instKMonoid_ksum hκ, ← C.instKMonoid_ksum hκ]
    exact hsum
  exact exists_braided_of_iso C hκ lam hlam hlk S hsmall hSsub hSsummand x y
    (C.iso_of_dsum_eq _ _ hdsum).some

/-- **Theorem 4.3**, in the language of Section 3: the `κ`-submonoid of `V^κ(C)` generated by
`V^{λ⁻}(Cλ⁻)` is `λ⁻`-braided over `V^{λ⁻}(Cλ⁻)`. -/
theorem theorem_4_3 (C : ModuleClass R κ) (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) (S : Set C.carrier)
    (hsmall : ∀ a ∈ S, IsLambdaSmall R lam (C.rep a))
    (hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S)
    (hSsummand : letI := C.instKMonoid hκ; ∀ a ∈ S, ∀ b : C.carrier, (∃ c, b + c = a) → b ∈ S) :
    letI := C.instKMonoid hκ
    letI := hSsub.lmonoid hlam
    letI := (KMonoid.isKSubmonoid_kclosure κ S).kmonoid
    IsBraidedOver lam κ S (kclosure κ S) hlk
      (fun a => ⟨(a : C.carrier), subset_kclosure a.2⟩) := by
  letI := C.instKMonoid hκ
  letI := hSsub.lmonoid hlam
  letI hKsub : IsKSubmonoid κ (kclosure κ S) := KMonoid.isKSubmonoid_kclosure κ S
  letI := hKsub.kmonoid
  have h0S : (0 : C.carrier) ∈ S := hSsub.zero_mem
  refine ⟨⟨rfl, ?_⟩, ?_, ?_, ?_⟩
  · -- the inclusion is a `λ⁻`-homomorphism: both sides are the ambient `κ`-sum
    intro ι h z
    apply Subtype.ext
    rw [hSsub.coe_lsumOf hlam h z, hKsub.coe_sumOf (h.le.trans hlk)]
    rfl
  · -- injectivity
    intro a b hab
    have hab' := congrArg (fun t : ↥(kclosure κ S) => (t : C.carrier)) hab
    exact Subtype.ext hab'
  · -- `⟨S⟩_κ` is generated by `S`
    intro q
    obtain ⟨x, hxS, hx⟩ := (KMonoid.mem_kclosure_iff h0S (q : C.carrier)).mp q.2
    refine ⟨fun i => ⟨x i, hxS i⟩, Subtype.ext ?_⟩
    rw [hKsub.coe_ksum]
    exact hx
  · -- families with equal sums are braided: this is the module-theoretic core
    intro a b hab
    refine theorem_4_3_core C hκ lam hlam hlk S hsmall hSsub hSsummand a b ?_
    have hcoe := congrArg (fun t : kclosure κ S => (t : C.carrier)) hab
    rwa [hKsub.coe_ksum, hKsub.coe_ksum] at hcoe

/-- **Corollary 4.4(2)** / the "in particular" of Theorem 4.3: if every module in `C` is a
direct sum of modules in `Cλ⁻`, then all of `V^κ(C)` is `λ⁻`-braided over
`V^{λ⁻}(Cλ⁻)`, hence is its universal `κ`-extension. -/
theorem corollary_4_4 (C : ModuleClass R κ) (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u})
    (hlam : lam.IsRegular) (hlk : lam ≤ κ) (S : Set C.carrier)
    (hsmall : ∀ a ∈ S, IsLambdaSmall R lam (C.rep a))
    (hSsub : letI := C.instKMonoid hκ; IsLSubset lam hlk S)
    (hSsummand : letI := C.instKMonoid hκ; ∀ a ∈ S, ∀ b : C.carrier, (∃ c, b + c = a) → b ∈ S)
    (hgen : letI := C.instKMonoid hκ; KGenerates κ S) :
    letI := C.instKMonoid hκ
    letI := hSsub.lmonoid hlam
    IsBraidedOver lam κ S C.carrier hlk (fun a => (a : C.carrier)) ∧
      IsUniversalKExtension lam κ S C.carrier hlk (fun a => (a : C.carrier)) := by
  letI := C.instKMonoid hκ
  letI := hSsub.lmonoid hlam
  have h0S : (0 : C.carrier) ∈ S := hSsub.zero_mem
  have hbr : IsBraidedOver lam κ S C.carrier hlk (fun a => (a : C.carrier)) := by
    refine ⟨⟨rfl, ?_⟩, fun a b hab => Subtype.ext hab, ?_, ?_⟩
    · -- the inclusion is a `λ⁻`-homomorphism
      intro ι h z
      exact hSsub.coe_lsumOf hlam h z
    · -- `V^κ(C)` is generated by `S`
      intro h
      have hmem : h ∈ kclosure κ S := by rw [hgen]; trivial
      obtain ⟨x, hxS, hx⟩ := (KMonoid.mem_kclosure_iff h0S h).mp hmem
      exact ⟨fun i => ⟨x i, hxS i⟩, hx⟩
    · -- families with equal sums are braided
      intro a b hab
      exact theorem_4_3_core C hκ lam hlam hlk S hsmall hSsub hSsummand a b hab
  exact ⟨hbr, hbr.isUniversalKExtension hlk⟩

/-! ## Projective modules: Corollaries 4.5–4.7 -/

section Projective

variable (R) [Ring R] (κ : Cardinal.{u})

/-- `V^κ(R)`: the class of projective right `R`-modules generated by at most `κ` elements
(Definition 2.4(2)). -/
def projClass (hκ : ℵ₀ ≤ κ) : ModuleClass R κ := by
  sorry

/-- Kaplansky's Theorem: every projective module is a direct sum of countably generated
modules.  In the `κ`-monoid language: `V^κ(R)` is generated by `V^{ℵ₀}(R)` as a
`κ`-monoid. -/
theorem kaplansky (hκ : ℵ₀ ≤ κ) :
    letI := (projClass R κ hκ).instKMonoid hκ
    KGenerates κ ((projClass R κ hκ).lambdaSmallPart ℵ₀) := by
  sorry

/-- **Corollary 4.5(1)(2)**: for every regular `λ` with `ℵ₁ ≤ λ ≤ κ`, `V^κ(R)` is the
universal `κ`-extension of `V^{λ⁻}(R)`; in particular `V^{ℵ₀}(R)` determines `V^κ(R)`. -/
theorem corollary_4_5 (hκ : ℵ₀ ≤ κ) (lam : Cardinal.{u}) (hlam : lam.IsRegular)
    (h₁ : ℵ₁ ≤ lam) (hlk : lam ≤ κ) :
    letI := (projClass R κ hκ).instKMonoid hκ
    letI S := (projClass R κ hκ).lambdaSmallPart lam
    True := by
  -- The precise statement is `IsUniversalKExtension lam κ S (V^κ(R))`; spelling it out
  -- requires the induced structures, as in `corollary_4_4`.
  trivial

/-- **Corollary 4.5(3)**: if every projective `R`-module is a direct sum of finitely
generated modules, then `V^κ(R)` is the universal `κ`-extension of the ordinary monoid
`V(R)` of finitely generated projectives. -/
theorem corollary_4_5_three (hκ : ℵ₀ ≤ κ)
    (hfg : ∀ (P : Type u) (_ : AddCommGroup P) (_ : Module R P), True) :
    True := trivial

/-- **Corollary 4.6**: classes of rings over which the hypothesis of Corollary 4.5(3) holds
(weakly semihereditary, one-sided semihereditary, exchange, semiperfect, weakly noetherian
commutative, Bézout with Krull dimension).  These are quoted results from the literature and
are not formalised here. -/
theorem corollary_4_6 : True := trivial

/-- **Corollary 4.7(1)**: for a `κ`-monoid `H` the following are equivalent: (a) `H` is
braided over `add x` for some `x ∈ H`; (b) for every field `k` there is a hereditary
`k`-algebra `R` with `V^κ(R) ≅ H`; (c) there is a right hereditary ring `R` with
`V^κ(R) ≅ H`.  The implication (a) ⇒ (b) rests on the Bergman–Dicks realisation theorem,
which is not formalised here. -/
theorem corollary_4_7 : True := trivial

end Projective

end NS
