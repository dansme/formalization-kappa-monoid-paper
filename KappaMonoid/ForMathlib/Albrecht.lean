/-
**Albrecht's theorem**: over a hereditary ring every projective module is a direct sum of
*finitely generated* projective modules.
-/
import KappaMonoid.ForMathlib.Hereditary
import KappaMonoid.ForMathlib.Kaplansky
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Basic

universe u

open Cardinal DirectSum

namespace Albrecht

variable {R : Type u} [Ring R]

/-! ## Modules that embed in `Rⁿ`

Over a ring all of whose left ideals are projective, a module embedding in a finitely generated
free module is projective.  The induction peels off one coordinate: the image of `M` there is a
left ideal, projective by hypothesis, so the projection splits and the kernel embeds in one
coordinate fewer. -/

theorem projective_of_injective_fin [IsLeftHereditary R] :
    ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module R M] (f : M →ₗ[R] (Fin n → R)),
      Function.Injective f → Module.Projective R M := by
  intro n
  induction n with
  | zero =>
      intro M _ _ f hf
      have : Subsingleton M := ⟨fun a b => hf (Subsingleton.elim _ _)⟩
      exact Module.projective_def.2 ⟨0, fun _ => Subsingleton.elim _ _⟩
  | succ n ih =>
      intro M _ _ f hf
      set φ : M →ₗ[R] R := LinearMap.proj 0 ∘ₗ f with hφ
      have : Module.Projective R (LinearMap.range φ) := IsLeftHereditary.projective_ideal (LinearMap.range φ)
      obtain ⟨g, hg⟩ := Module.projective_lifting_property φ.rangeRestrict LinearMap.id
        (LinearMap.surjective_rangeRestrict φ)
      have hgapp : ∀ y, φ.rangeRestrict (g y) = y := fun y =>
        congrFun (congrArg DFunLike.coe hg) y
      have hker : Module.Projective R (LinearMap.ker φ) := by
        refine ih _ (LinearMap.funLeft R R Fin.succ ∘ₗ f ∘ₗ (LinearMap.ker φ).subtype) ?_
        intro x y hxy
        refine Subtype.ext (hf (funext fun i => ?_))
        refine Fin.cases ?_ (fun j => congrFun hxy j) i
        have hx : φ (x : M) = 0 := x.2
        have hy : φ (y : M) = 0 := y.2
        exact hx.trans hy.symm
      set e : M →ₗ[R] M := g ∘ₗ φ.rangeRestrict with he
      have hmem : ∀ x : M, ((LinearMap.id : M →ₗ[R] M) - e) x ∈ LinearMap.ker φ := by
        intro x
        have : (φ.rangeRestrict (e x) : R) = (φ.rangeRestrict x : R) := congrArg _ (hgapp _)
        simpa [LinearMap.mem_ker, sub_eq_zero] using this.symm
      exact Module.Projective.of_split
        ((LinearMap.codRestrict _ ((LinearMap.id : M →ₗ[R] M) - e) hmem).prod φ.rangeRestrict)
        ((LinearMap.ker φ).subtype.coprod g)
        (LinearMap.ext fun x => by simp [he])

/-- The submodule of `ℕ →₀ R` supported on the first `n` coordinates. -/
noncomputable def Fpart (R : Type u) [Ring R] (n : ℕ) : Submodule R (ℕ →₀ R) :=
  Finsupp.supported R R {k | k < n}

theorem Fpart_mono {m n : ℕ} (h : m ≤ n) : Fpart R m ≤ Fpart R n :=
  Finsupp.supported_mono fun _ hk => lt_of_lt_of_le hk h

theorem Fpart_zero : Fpart R 0 = ⊥ := by
  rw [Fpart, show {k : ℕ | k < 0} = (∅ : Set ℕ) by ext; simp, Finsupp.supported_empty]

theorem mem_Fpart_iff {n : ℕ} {x : ℕ →₀ R} : x ∈ Fpart R n ↔ ∀ k, n ≤ k → x k = 0 :=
  ⟨fun hx k hk => (Finsupp.mem_supported' _ _).1 hx k (not_lt.2 hk),
    fun h => (Finsupp.mem_supported' _ _).2 fun k hk => h k (not_lt.1 hk)⟩

theorem exists_mem_Fpart (x : ℕ →₀ R) : ∃ n, x ∈ Fpart R n :=
  ⟨x.support.sup id + 1, mem_Fpart_iff.2 fun k hk => by
    by_contra hne
    have hle : k ≤ x.support.sup id := Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 hne)
    omega⟩

theorem finite_Fpart (n : ℕ) : Module.Finite R (Fpart R n) := by
  rw [Module.Finite.iff_fg, Fpart, Finsupp.supported_eq_span_single]
  exact Submodule.fg_span ((Set.finite_Iio n).image _)

/-- A submodule supported on finitely many coordinates is projective. -/
theorem projective_of_le_Fpart [IsLeftHereditary R] {n : ℕ}
    {M : Submodule R (ℕ →₀ R)} (hM : M ≤ Fpart R n) : Module.Projective R M := by
  refine projective_of_injective_fin n ↥M
    (LinearMap.pi (fun i : Fin n => Finsupp.lapply (i : ℕ)) ∘ₗ M.subtype) ?_
  intro x y hxy
  refine Subtype.ext (Finsupp.ext fun k => ?_)
  by_cases hk : k < n
  · exact congrFun hxy ⟨k, hk⟩
  · rw [mem_Fpart_iff.1 (hM x.2) k (not_lt.1 hk), mem_Fpart_iff.1 (hM y.2) k (not_lt.1 hk)]

/-- Every finitely generated submodule of `ℕ →₀ R` is supported on finitely many coordinates. -/
theorem exists_le_Fpart {M : Submodule R (ℕ →₀ R)} (hM : M.FG) : ∃ n, M ≤ Fpart R n := by
  obtain ⟨t, ht⟩ := hM
  refine ⟨(t.sup fun x => x.support.sup id) + 1, ?_⟩
  rw [← ht, Submodule.span_le]
  intro x hx
  refine mem_Fpart_iff.2 fun k hk => ?_
  by_contra hne
  have h1 : k ≤ x.support.sup id := Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 hne)
  have h2 : x.support.sup id ≤ t.sup fun x => x.support.sup id :=
    Finset.le_sup (f := fun x : ℕ →₀ R => x.support.sup id) hx
  omega

theorem projective_of_fg [IsLeftHereditary R]
    {M : Submodule R (ℕ →₀ R)} (hM : M.FG) : Module.Projective R M := by
  obtain ⟨n, hn⟩ := exists_le_Fpart hM
  exact projective_of_le_Fpart hn

/-! ## The filtration of the image of an idempotent

`Npart π n` is the part of `π`'s image supported on the first `n` coordinates.  Two facts drive
the argument: `Fpart R n / Npart π n` embeds in `ℕ →₀ R` as a finitely generated submodule, hence
is projective, so `Npart π n` is a *finitely generated* direct summand of `Fpart R n`; and
`Npart π (n+1) / Npart π n` embeds in `R`, hence is a finitely generated left ideal, so that step
of the filtration splits off a finitely generated projective piece. -/

section Chain

variable (π : (ℕ →₀ R) →ₗ[R] (ℕ →₀ R))

/-- The part of the image of `π` supported on the first `n` coordinates. -/
noncomputable def Npart (n : ℕ) : Submodule R (ℕ →₀ R) := LinearMap.range π ⊓ Fpart R n

variable {π}

theorem mem_range_iff (hπ : ∀ x, π (π x) = π x) {x : ℕ →₀ R} :
    x ∈ LinearMap.range π ↔ π x = x := by
  refine ⟨?_, fun h => ⟨x, h⟩⟩
  rintro ⟨y, rfl⟩
  exact hπ y

variable (π)

theorem Npart_mono {m n : ℕ} (h : m ≤ n) : Npart π m ≤ Npart π n :=
  inf_le_inf_left _ (Fpart_mono h)

theorem Npart_le_range (n : ℕ) : Npart π n ≤ LinearMap.range π := inf_le_left

theorem Npart_le_Fpart (n : ℕ) : Npart π n ≤ Fpart R n := inf_le_right

theorem Npart_zero : Npart π 0 = ⊥ := by rw [Npart, Fpart_zero, inf_bot_eq]

theorem iSup_Npart : ⨆ n, Npart π n = LinearMap.range π := by
  refine le_antisymm (iSup_le (Npart_le_range π)) fun x hx => ?_
  obtain ⟨n, hn⟩ := exists_mem_Fpart (R := R) x
  exact le_iSup (Npart π) n ⟨hx, hn⟩

/-- `Npart π n` is a direct summand of `Fpart R n`, hence finitely generated: the quotient
`Fpart R n / Npart π n` is the image of `1 - π` there, a finitely generated submodule of a free
module and so projective. -/
theorem finite_Npart [IsLeftHereditary R] (hπ : ∀ x, π (π x) = π x)
    (n : ℕ) : Module.Finite R (Npart π n) := by
  have := finite_Fpart (R := R) n
  set ψ : (Fpart R n) →ₗ[R] (ℕ →₀ R) :=
    ((LinearMap.id : (ℕ →₀ R) →ₗ[R] (ℕ →₀ R)) - π) ∘ₗ (Fpart R n).subtype with hψ
  have hψapp : ∀ z : (Fpart R n), ψ z = (z : ℕ →₀ R) - π (z : ℕ →₀ R) := fun _ => rfl
  have : Module.Finite R (LinearMap.range ψ) :=
    Module.Finite.of_surjective ψ.rangeRestrict (LinearMap.surjective_rangeRestrict ψ)
  have : Module.Projective R (LinearMap.range ψ) :=
    projective_of_fg (Module.Finite.iff_fg.1 inferInstance)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property ψ.rangeRestrict LinearMap.id
    (LinearMap.surjective_rangeRestrict ψ)
  have hgapp : ∀ y, ψ.rangeRestrict (g y) = y := fun y => congrFun (congrArg DFunLike.coe hg) y
  -- `ρ z = z - g (ψ z)` lands in `Npart π n` and is the identity there
  set ρ : (Fpart R n) →ₗ[R] (ℕ →₀ R) :=
    (Fpart R n).subtype - (Fpart R n).subtype ∘ₗ g ∘ₗ ψ.rangeRestrict with hρ
  have hρapp : ∀ z : (Fpart R n), ρ z = (z : ℕ →₀ R) - ((g (ψ.rangeRestrict z) : Fpart R n) :
      ℕ →₀ R) := fun _ => rfl
  have hψeq : ∀ z : (Fpart R n), ψ (g (ψ.rangeRestrict z)) = ψ z := fun z =>
    congrArg Subtype.val (hgapp (ψ.rangeRestrict z))
  have hmem : ∀ z, ρ z ∈ Npart π n := by
    intro z
    have h := hψeq z
    rw [hψapp, hψapp] at h
    have hw : ρ z - π (ρ z) = 0 := by
      rw [hρapp, map_sub, sub_sub_sub_comm, h, sub_self]
    refine ⟨(mem_range_iff hπ).2 (sub_eq_zero.1 hw).symm, ?_⟩
    rw [hρapp]
    exact sub_mem z.2 (g (ψ.rangeRestrict z)).2
  refine Module.Finite.of_surjective (LinearMap.codRestrict (Npart π n) ρ hmem) ?_
  rintro ⟨y, hy⟩
  refine ⟨⟨y, hy.2⟩, Subtype.ext ?_⟩
  have h0 : ψ ⟨y, hy.2⟩ = 0 := by
    rw [hψapp]
    exact sub_eq_zero.2 ((mem_range_iff hπ).1 hy.1).symm
  have h1 : ψ.rangeRestrict ⟨y, hy.2⟩ = 0 := Subtype.ext h0
  show ρ ⟨y, hy.2⟩ = y
  rw [hρapp, h1, map_zero]
  simp

/-- The `n`-th step of the filtration splits off a finitely generated projective complement. -/
theorem exists_complement [IsLeftHereditary R]
    (hπ : ∀ x, π (π x) = π x) (n : ℕ) :
    ∃ C : Submodule R (ℕ →₀ R), C ≤ Npart π (n + 1) ∧ Disjoint (Npart π n) C ∧
      Npart π n ⊔ C = Npart π (n + 1) ∧ Module.Finite R C := by
  have := finite_Npart π hπ (n + 1)
  set χ : (Npart π (n + 1)) →ₗ[R] R := Finsupp.lapply n ∘ₗ (Npart π (n + 1)).subtype with hχ
  have : Module.Projective R (LinearMap.range χ) := IsLeftHereditary.projective_ideal (LinearMap.range χ)
  have : Module.Finite R (LinearMap.range χ) :=
    Module.Finite.of_surjective χ.rangeRestrict (LinearMap.surjective_rangeRestrict χ)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property χ.rangeRestrict LinearMap.id
    (LinearMap.surjective_rangeRestrict χ)
  have hgapp : ∀ y, χ.rangeRestrict (g y) = y := fun y => congrFun (congrArg DFunLike.coe hg) y
  refine ⟨Submodule.map (Npart π (n + 1)).subtype (LinearMap.range g), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact z.2
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨_, ⟨y, rfl⟩, rfl⟩
    have h1 : χ (g y) = 0 := mem_Fpart_iff.1 hx.2 n (le_refl n)
    have h2 : (y : R) = 0 := by rw [← congrArg Subtype.val (hgapp y)]; exact h1
    rw [show y = 0 from Subtype.ext h2, map_zero]
    rfl
  · refine le_antisymm (sup_le (Npart_mono π n.le_succ) ?_) fun x hx => ?_
    · rintro _ ⟨z, -, rfl⟩
      exact z.2
    · have hgz : ((g (χ.rangeRestrict ⟨x, hx⟩) : Npart π (n + 1)) : ℕ →₀ R) ∈
          Submodule.map (Npart π (n + 1)).subtype (LinearMap.range g) :=
        ⟨g (χ.rangeRestrict ⟨x, hx⟩), ⟨_, rfl⟩, rfl⟩
      have hsub : x - ((g (χ.rangeRestrict ⟨x, hx⟩) : Npart π (n + 1)) : ℕ →₀ R) ∈ Npart π n := by
        refine ⟨sub_mem hx.1 (g (χ.rangeRestrict ⟨x, hx⟩)).2.1, mem_Fpart_iff.2 fun k hk => ?_⟩
        rcases eq_or_lt_of_le hk with rfl | hk'
        · have e1 : ((g (χ.rangeRestrict ⟨x, hx⟩) : Npart π (n + 1)) : ℕ →₀ R) n
              = ((χ.rangeRestrict ⟨x, hx⟩ : LinearMap.range χ) : R) :=
            congrArg Subtype.val (hgapp _)
          have e2 : ((χ.rangeRestrict ⟨x, hx⟩ : LinearMap.range χ) : R) = x n := rfl
          rw [Finsupp.sub_apply, e1, e2, sub_self]
        · rw [Finsupp.sub_apply, mem_Fpart_iff.1 hx.2 k hk',
            mem_Fpart_iff.1 (g (χ.rangeRestrict ⟨x, hx⟩)).2.2 k hk', sub_zero]
      have hmem := add_mem (Submodule.mem_sup_left hsub) (Submodule.mem_sup_right hgz)
      simpa using hmem
  · refine Module.Finite.of_surjective
      (LinearMap.codRestrict (Submodule.map (Npart π (n + 1)).subtype (LinearMap.range g))
        ((Npart π (n + 1)).subtype ∘ₗ g) (fun y => ⟨g y, ⟨y, rfl⟩, rfl⟩)) ?_
    rintro ⟨_, ⟨z, ⟨y, rfl⟩, rfl⟩⟩
    exact ⟨y, rfl⟩

/-- The image of an idempotent endomorphism of `ℕ →₀ R` is a direct sum of finitely generated
projective submodules. -/
theorem exists_directSum_fg_of_idempotent [IsLeftHereditary R]
    (hπ : ∀ x, π (π x) = π x) :
    ∃ C : ℕ → Submodule R (ℕ →₀ R), (∀ n, Module.Projective R (C n)) ∧
      (∀ n, Module.Finite R (C n)) ∧
        Nonempty ((LinearMap.range π) ≃ₗ[R] ⨁ n, (C n)) := by
  classical
  choose C hle hdisj hsup hfin using exists_complement π hπ
  have hNle : ∀ n, Npart π n ≤ ⨆ m, C m := by
    intro n
    induction n with
    | zero => rw [Npart_zero]; exact bot_le
    | succ n ih => rw [← hsup n]; exact sup_le ih (le_iSup C n)
  have hCsup : ⨆ n, C n = LinearMap.range π := by
    refine le_antisymm (iSup_le fun n => (hle n).trans (Npart_le_range π (n + 1))) ?_
    rw [← iSup_Npart π]
    exact iSup_le hNle
  have hindep : iSupIndep C :=
    iSupIndep_of_disjoint_lt (A := Npart π) hdisj
      fun {c b} hcb => (hle c).trans (Npart_mono π hcb)
  have hinj : Function.Injective (DirectSum.coeLinearMap C) := hindep.dfinsupp_lsum_injective
  have hrange : LinearMap.range (DirectSum.coeLinearMap C) = LinearMap.range π := by
    rw [DirectSum.range_coeLinearMap, hCsup]
  exact ⟨C, fun n => projective_of_le_Fpart ((hle n).trans (Npart_le_Fpart π (n + 1))),
    hfin, ⟨(LinearEquiv.ofEq _ _ hrange.symm).trans (LinearEquiv.ofInjective _ hinj).symm⟩⟩

end Chain

/-! ## Albrecht's theorem -/

/-- A countably generated module is a quotient of `ℕ →₀ R`. -/
theorem exists_surjective_of_countable {Q : Type u} [AddCommGroup Q] [Module R Q]
    {s : Set Q} (hs : #s ≤ ℵ₀) (hsp : Submodule.span R s = ⊤) :
    ∃ h : ℕ → Q, Function.Surjective (Finsupp.linearCombination R h) := by
  have hc : (insert (0 : Q) s).Countable :=
    Set.Countable.insert 0 (Set.countable_coe_iff.1 (Cardinal.mk_le_aleph0_iff.1 hs))
  obtain ⟨h, hh⟩ := hc.exists_eq_range ⟨0, Set.mem_insert _ _⟩
  refine ⟨h, LinearMap.range_eq_top.1 ?_⟩
  rw [Finsupp.range_linearCombination, ← hh, Submodule.span_insert_zero, hsp]

/-- A countably generated projective module over a ring whose left ideals are projective is a
direct sum of finitely generated projective modules. -/
theorem exists_directSum_fg_of_countablyGenerated [IsLeftHereditary R]
    (Q : Type u) [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    {s : Set Q} (hs : #s ≤ ℵ₀) (hsp : Submodule.span R s = ⊤) :
    ∃ (S : ℕ → Type u) (_ : ∀ n, AddCommGroup (S n)) (_ : ∀ n, Module R (S n)),
      (∀ n, Module.Projective R (S n)) ∧ (∀ n, Module.Finite R (S n)) ∧
        Nonempty (Q ≃ₗ[R] ⨁ n, S n) := by
  obtain ⟨h, hsurj⟩ := exists_surjective_of_countable hs hsp
  obtain ⟨ι, hι⟩ := Module.projective_lifting_property (Finsupp.linearCombination R h)
    LinearMap.id hsurj
  set t := Finsupp.linearCombination R h with ht
  have hts : ∀ q, t (ι q) = q := fun q => congrFun (congrArg DFunLike.coe hι) q
  set π := ι ∘ₗ t with hπdef
  have hπ : ∀ x, π (π x) = π x := fun x => congrArg ι (hts (t x))
  have hrange : LinearMap.range π = LinearMap.range ι := by
    refine le_antisymm (LinearMap.range_comp_le_range _ _) ?_
    rintro _ ⟨q, rfl⟩
    exact ⟨ι q, congrArg ι (hts q)⟩
  obtain ⟨C, hprojC, hfinC, ⟨e⟩⟩ := exists_directSum_fg_of_idempotent π hπ
  have hιinj : Function.Injective ι := fun p q hpq => by rw [← hts p, ← hts q, hpq]
  exact ⟨fun n => C n, fun _ => inferInstance, fun _ => inferInstance, hprojC, hfinC,
    ⟨((LinearEquiv.ofInjective ι hιinj).trans (LinearEquiv.ofEq _ _ hrange.symm)).trans e⟩⟩

/-- **Albrecht's theorem** (Albrecht 1961; Bergman 1972): over a ring all of whose left ideals are
projective — a left hereditary ring — every projective module is a direct sum of *finitely
generated* projective modules.

Paper proof.  Kaplansky's theorem reduces the statement to a countably generated projective `Q`,
which is then the image of an idempotent `π` on the free module `ℕ →₀ R`.  Filter that image by
`Npart π n`, the part supported on the first `n` coordinates.  Each `Npart π n` is finitely
generated, because `Fpart R n / Npart π n` is the image of `1 - π` on `Fpart R n`, a finitely
generated submodule of a free module and so projective by the hypothesis on ideals — so the
quotient map splits.  And `Npart π (n+1) / Npart π n` embeds in `R` through the `n`-th coordinate,
so it is a finitely generated left ideal, projective again, and that step of the filtration splits
off a finitely generated projective complement.  These complements are independent and their sum
is the whole image. -/
theorem exists_directSum_fg [IsLeftHereditary R] :
    ∀ (Q : Type u) (_ : AddCommGroup Q) (_ : Module R Q), Module.Projective R Q →
      ∃ (ι : Type u) (S : ι → Type u) (_ : ∀ i, AddCommGroup (S i)) (_ : ∀ i, Module R (S i)),
        (∀ i, Module.Projective R (S i)) ∧ (∀ i, Module.Finite R (S i)) ∧
          Nonempty (Q ≃ₗ[R] ⨁ i, S i) := by
  classical
  intro Q _ _ hQ
  obtain ⟨ι, P, iAG, iMod, hprojP, hgen, ⟨e⟩⟩ :=
    Module.Projective.exists_directSum_countablyGenerated (R := R) Q
  have key : ∀ i, ∃ (S : ℕ → Type u) (_ : ∀ n, AddCommGroup (S n)) (_ : ∀ n, Module R (S n)),
      (∀ n, Module.Projective R (S n)) ∧ (∀ n, Module.Finite R (S n)) ∧
        Nonempty (P i ≃ₗ[R] ⨁ n, S n) := by
    intro i
    let := iAG i
    let := iMod i
    have := hprojP i
    obtain ⟨s, hs, hsp⟩ := hgen i
    exact exists_directSum_fg_of_countablyGenerated (P i) hs hsp
  choose S iS mS hprojS hfinS heS using key
  refine ⟨Σ _ : ι, ℕ, fun p => S p.1 p.2, fun p => iS p.1 p.2, fun p => mS p.1 p.2,
    fun p => hprojS p.1 p.2, fun p => hfinS p.1 p.2, ⟨?_⟩⟩
  exact e.trans ((DFinsupp.mapRange.linearEquiv fun i => (heS i).some).trans
    (DirectSum.sigmaLcurryEquiv R (α := fun _ : ι => ℕ) (δ := S)).symm)

end Albrecht
