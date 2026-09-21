/-
**Lemma 3.14**: the universal `κ`-extension of a free `λ⁻`-monoid (1), and of a saturated
`λ⁻`-submonoid of one (2).  General theory, not an example: §4's Examples 4.8(1) uses (1).
-/
import KappaMonoid.Braiding.UnivExt
import KappaMonoid.Core.Free

universe u v w t

open Cardinal Function Set

namespace KappaMonoid

/-! ## Lemma 3.14(1): free objects

`F_{λ⁻}(B)` sits inside `F_κ(B)` — a family of cardinals `< λ` with support of size `< λ` is in
particular a family of cardinals `≤ κ` with support of size `≤ κ` — and the universal property of
`F_κ(B)` (Proposition 2.9) is exactly the universal property required of the extension. -/

section Free

variable {lam κ : Cardinal.{u}} {B : Type u}

/-- The inclusion `F_{λ⁻}(B) ↪ F_κ(B)`. -/
def freeIncl (_hlam : lam.IsRegular) (_hκ : ℵ₀ ≤ κ) (hlk : lam ≤ Order.succ κ) (x : ↥(FreeL lam B)) :
    ↥(FreeK κ B) :=
  ⟨fun b => ⟨((x : B → LCard lam) b : Cardinal.{u}),
      lt_of_lt_of_le ((x : B → LCard lam) b).2 (hlk)⟩,
    lt_of_lt_of_le x.2 (hlk)⟩

@[simp] theorem val_freeIncl (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ Order.succ κ)
    (x : ↥(FreeL lam B)) (b : B) :
    (((freeIncl hlam hκ hlk x : ↥(FreeK κ B)) : B → Fcard κ) b : Cardinal.{u})
      = ((x : B → LCard lam) b : Cardinal.{u}) := rfl

/-- `freeIncl` carries the generator `ι(b)` of `F_{λ⁻}(B)` to the generator `ι(b)` of
`F_κ(B)`. -/
theorem freeIncl_iota (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ Order.succ κ) (b : B) :
    letI : Fact lam.IsRegular := ⟨hlam⟩
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    freeIncl hlam hκ hlk (iota (lam := lam) b) = iota (lam := Order.succ κ) b := by
  let : Fact lam.IsRegular := ⟨hlam⟩
  let : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  refine Subtype.ext (funext fun b' => Subtype.ext ?_)
  rw [val_freeIncl, coe_iota, coe_iota]
  by_cases h : b' = b
  · rw [h, val_iotaFun_self, val_iotaFun_self]
  · rw [val_iotaFun_of_ne (lam := lam) h, val_iotaFun_of_ne (lam := Order.succ κ) h]

/-- `freeIncl` is a `λ⁻`-homomorphism: on both sides a coordinate is the same cardinal sum. -/
theorem isLHom_freeIncl (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ Order.succ κ) :
    letI : Fact lam.IsRegular := ⟨hlam⟩
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    letI := instKMonoidFreeK κ hκ B
    LMonoid.IsLHom hlk (freeIncl (B := B) hlam hκ hlk) := by
  let : Fact lam.IsRegular := ⟨hlam⟩
  let : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  let := instKMonoidFreeK κ hκ B
  refine ⟨Subtype.ext (funext fun b => Subtype.ext ?_), fun {ι} h x => ?_⟩
  · rw [val_freeIncl]
    show ((0 : LCard lam) : Cardinal.{u}) = ((0 : Fcard κ) : Cardinal.{u})
    rw [LCard.val_zero hlam, LCard.val_zero (Cardinal.isRegular_succ hκ)]
  · exact Subtype.ext (funext fun b => Subtype.ext rfl)

/-- **Lemma 3.14(1)**: the free `κ`-monoid on `B` is the universal `κ`-extension of the free
`λ⁻`-monoid on `B`.

Both universal properties are Proposition 2.9, at `λ` and at `κ⁺` respectively; the extension of
`φ : F_{λ⁻}(B) → K` is `lift (φ ∘ ι)`, and both halves of the universal property are `hom_ext` —
at level `λ` for the extension identity, at level `κ⁺` for uniqueness. -/
theorem lemma_3_14_free (hlam : lam.IsRegular) (hκ : ℵ₀ ≤ κ) (hlk : lam ≤ Order.succ κ) :
    letI : Fact lam.IsRegular := ⟨hlam⟩
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    letI := instKMonoidFreeK κ hκ B
    IsUniversalKExtension.{u, u + 1, u + 1, t} lam κ ↥(FreeL lam B) ↥(FreeK κ B) hlk
      (freeIncl hlam hκ hlk) := by
  let : Fact lam.IsRegular := ⟨hlam⟩
  let : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  let := instKMonoidFreeK κ hκ B
  refine ⟨isLHom_freeIncl hlam hκ hlk, fun K _ φ hφ => ?_⟩
  -- the extension is the lift of `φ ∘ ι`, taken at level `κ⁺`
  set ψ : ↥(FreeK κ B) → K :=
    lift (lam := Order.succ κ) (X := K) (fun b => φ (iota (lam := lam) b)) with hψ
  have hψiota : ∀ b : B, ψ (iota (lam := Order.succ κ) b) = φ (iota (lam := lam) b) :=
    fun b => by rw [hψ, lift_iota]
  refine ⟨ψ, ⟨isKHom_of_isLMonoidHom hκ (isLMonoidHom_lift _), ?_⟩, ?_⟩
  · -- `ψ ∘ freeIncl = φ`: both are `λ⁻`-homomorphisms agreeing on the generators
    let := KMonoid.toLMonoidOfLE K hlam hlk
    have hcomp : IsLMonoidHom lam (fun x => ψ (freeIncl hlam hκ hlk x)) := by
      intro ι h x
      show ψ (freeIncl hlam hκ hlk (LMonoid.lsumOf (lam := lam) h x)) = _
      rw [(isLHom_freeIncl (B := B) hlam hκ hlk).2 h x]
      exact isLMonoidHom_lift _ (KMonoid.lt_succ (le_of_lt_of_le_succ hlk h)) _
    have key := hom_ext (lam := lam) (X := K)
      (g₁ := fun x => ψ (freeIncl hlam hκ hlk x)) (g₂ := φ) hcomp
      (isLMonoidHom_of_isLHom hlam hlk hφ)
      (fun b => by rw [freeIncl_iota hlam hκ hlk b, hψiota b])
    exact fun x => congrFun key x
  · -- uniqueness: a `κ`-homomorphism out of `F_κ(B)` is determined on the generators
    rintro ψ' ⟨hhom', hext'⟩
    refine hom_ext (lam := Order.succ κ) (X := K) (g₁ := ψ') (g₂ := ψ)
      (fun {ι} h x => KMonoid.IsKHom.map_sumOf hhom' (KMonoid.le_of_lt_succ h) x)
      (isLMonoidHom_lift _) fun b => ?_
    rw [hψiota b, ← freeIncl_iota hlam hκ hlk b, hext']

end Free

/-! ## Saturated submonoids and Lemma 3.14(2) -/

/-- A submonoid `S ⊆ X` is *saturated* if a summand in `X` of an element of `S` that itself lies
in `S` has its complement in `S`: from `s = t + h` with `s`, `t ∈ S` follows `h ∈ S`. -/
def IsSaturated {X : Type v} [AddCommMonoid X] (S : Set X) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, ∀ h : X, s = t + h → h ∈ S

section Sub

variable {lam κ : Cardinal.{u}} {X : Type v} {Hh : Type w}

/-- **Lemma 3.14(2)**, in the form actually used: if `Ĥ` is `λ⁻`-braided over `X` and `S ⊆ X` is a
`λ⁻`-submonoid which is either saturated or sits over an uncountable `λ`, then *any* `κ`-submonoid
`T` of `Ĥ` with `f(S) ⊆ T ⊆ ⟨f(S)⟩_κ` — that is, `T = ⟨S⟩_κ` described extensionally — is the
universal `κ`-extension of `S`.  Stating the conclusion for such a `T` rather than for
`⟨f(S)⟩_κ` on the nose avoids rewriting a set equality inside a type at the point of use.

Paper proof: it suffices to see that `⟨S⟩_κ` is `λ⁻`-braided over `S`, i.e. that the braiding
families `u`, `v` of a braiding in `Ĥ` may be taken inside `S`.  For `λ ≠ ℵ₀` that is
Lemma 3.4(4) — take `v ≡ 0`, so `u_μ` is a partial sum of elements of `S`.  For `λ = ℵ₀` it is a
transfinite induction along the blocks: at a limit `v_μ = 0` and `u_μ ∈ S`, and
`u_{μ+n} + v_{μ+n}` and `u_{μ+n} + v_{μ+n+1}` both lie in `S`, so saturatedness pushes `u` and
`v` into `S` one step at a time. -/
theorem isBraidedOver_of_isLSubmonoid [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ Order.succ κ) {f : X → Hh}
    (hbr : IsBraidedOver lam κ X Hh hlk f) (S : Set X) (hS : IsLSubmonoid lam S)
    (hsat : lam ≠ ℵ₀ ∨ IsSaturated S) {T : Set Hh} (hT : KMonoid.IsKSubmonoid κ T)
    (hfT : ∀ s ∈ S, f s ∈ T) (hTgen : T ⊆ KMonoid.kclosure κ (f '' S)) :
    letI := hS.lmonoid
    letI := hT.kmonoid
    IsBraidedOver lam κ ↥S ↥T hlk (fun s => ⟨f (s : X), hfT (s : X) s.2⟩) := by
  classical
  let := hS.lmonoid
  let := hT.kmonoid
  have hf0 : f 0 = 0 := hbr.isLHom.1
  have h0S : (0 : X) ∈ S := hS.zero_mem
  refine ⟨⟨Subtype.ext hf0, fun {ι} h x => ?_⟩,
    fun a b hab => Subtype.ext (hbr.injective (congrArg Subtype.val hab)), fun h => ?_,
    fun a b hab => ?_⟩
  · -- the inclusion is a `λ⁻`-homomorphism, because `f` is
    exact Subtype.ext (hbr.isLHom.2 h fun i => ((x i : X)))
  · -- `T` is generated by `S`: unfold the description of the `κ`-closure
    obtain ⟨x, hxS, hxsum⟩ :=
      (KMonoid.mem_kclosure_iff (S := f '' S) ⟨0, h0S, hf0⟩ (h : Hh)).mp (hTgen h.2)
    choose s hsS hsf using hxS
    refine ⟨fun i => ⟨s i, hsS i⟩, Subtype.ext ?_⟩
    show (h : Hh) = KMonoid.ksum (κ := κ) fun i => f (s i)
    rw [hxsum]
    exact congrArg _ (funext fun i => (hsf i).symm)
  · -- two families in `S` with equal `κ`-sum are `λ⁻`-braided *inside* `S`
    have hbraid := hbr.braided (fun i => (a i : X)) (fun i => (b i : X))
      (congrArg Subtype.val hab)
    rcases hsat with hne | hsatS
    · -- `λ ≠ ℵ₀`: Lemma 3.4(4) lets us take `v ≡ 0`, and then each `u` is a partial sum
      obtain ⟨I, J, hI, hJ, hIdisj, hJdisj, hIcov, hJcov, heq⟩ :=
        (isBraided_iff_of_ne_aleph0 hne _ _).mp hbraid
      exact IsBraided.of_partition I J hIdisj hJdisj hIcov hJcov hI hJ
        fun p => Subtype.ext (heq p)
    · -- `S` saturated: walk along each `ω`-block, moving `u` and `v` into `S` one step at a time
      obtain ⟨d⟩ := hbraid
      have hxS : ∀ p, d.v p + d.u p ∈ S := fun p =>
        d.hI p ▸ hS.lsumOf_mem (d.I_small p) _ fun i => (a (i : Idx κ)).2
      have hyS : ∀ p, d.v (bsucc p) + d.u p ∈ S := fun p =>
        d.hJ p ▸ hS.lsumOf_mem (d.J_small p) _ fun j => (b (j : Idx κ)).2
      have key : ∀ p : Idx κ × ℕ, d.u p ∈ S ∧ d.v p ∈ S := by
        rintro ⟨α, m⟩
        induction m with
        | zero =>
            have hv0 : d.v (α, 0) = 0 := d.v_limit α
            refine ⟨?_, hv0 ▸ h0S⟩
            have hsum := hxS (α, 0)
            rwa [hv0, zero_add] at hsum
        | succ m ih =>
            have hv : d.v (α, m + 1) ∈ S :=
              hsatS _ (hyS (α, m)) _ ih.1 _ (add_comm (d.v (α, m + 1)) (d.u (α, m)))
            exact ⟨hsatS _ (hxS (α, m + 1)) _ hv _ rfl, hv⟩
      exact ⟨{ I := d.I, J := d.J
               I_disjoint := d.I_disjoint, J_disjoint := d.J_disjoint
               I_cover := d.I_cover, J_cover := d.J_cover
               I_small := d.I_small, J_small := d.J_small
               u := fun p => ⟨d.u p, (key p).1⟩
               v := fun p => ⟨d.v p, (key p).2⟩
               v_limit := fun α => Subtype.ext (d.v_limit α)
               hI := fun p => Subtype.ext (d.hI p)
               hJ := fun p => Subtype.ext (d.hJ p) }⟩

/-- **Lemma 3.14(2)**, in the form used: any `κ`-submonoid `T` with `f(S) ⊆ T ⊆ ⟨f(S)⟩_κ` is the
universal `κ`-extension of `S`. -/
theorem lemma_3_14_sub_of_subset [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ Order.succ κ) {f : X → Hh}
    (hbr : IsBraidedOver lam κ X Hh hlk f) (S : Set X) (hS : IsLSubmonoid lam S)
    (hsat : lam ≠ ℵ₀ ∨ IsSaturated S) {T : Set Hh} (hT : KMonoid.IsKSubmonoid κ T)
    (hfT : ∀ s ∈ S, f s ∈ T) (hTgen : T ⊆ KMonoid.kclosure κ (f '' S)) :
    letI := hS.lmonoid
    letI := hT.kmonoid
    IsUniversalKExtension.{u, v, w, t} lam κ ↥S ↥T hlk (fun s => ⟨f (s : X), hfT (s : X) s.2⟩) := by
  let := hS.lmonoid
  let := hT.kmonoid
  exact (isBraidedOver_of_isLSubmonoid hlk hbr S hS hsat hT hfT hTgen).isUniversalKExtension hlk

/-- **Lemma 3.14(2)** as printed: `⟨S⟩_κ ⊆ Ĥ` is the universal `κ`-extension of `S`. -/
theorem lemma_3_14_sub [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ Order.succ κ) {f : X → Hh}
    (hbr : IsBraidedOver lam κ X Hh hlk f) (S : Set X) (hS : IsLSubmonoid lam S)
    (hsat : lam ≠ ℵ₀ ∨ IsSaturated S) :
    letI := hS.lmonoid
    letI := (KMonoid.isKSubmonoid_kclosure κ (f '' S)).kmonoid
    IsUniversalKExtension.{u, v, w, t} lam κ ↥S ↥(KMonoid.kclosure κ (f '' S)) hlk
      (fun s => ⟨f (s : X), KMonoid.subset_kclosure ⟨(s : X), s.2, rfl⟩⟩) :=
  lemma_3_14_sub_of_subset hlk hbr S hS hsat (KMonoid.isKSubmonoid_kclosure κ (f '' S))
    (fun s hs => KMonoid.subset_kclosure ⟨s, hs, rfl⟩) subset_rfl

end Sub

end KappaMonoid
