/-
**Proposition 3.10** (extension of a `λ⁻`-homomorphism along a braiding) and **Definition 3.11**
(`IsUniversalKExtension`), with its transports.
-/
import KappaMonoid.Braiding.UnivAux

universe u v w z t

open Cardinal Function Set

namespace KappaMonoid

open KMonoid LMonoid

variable {lam κ : Cardinal.{u}}

/-! ## Proposition 3.10 -/

variable {lam κ : Cardinal.{u}}

/-- Proposition 3.10: if the `κ`-monoid `H` is `λ⁻`-braided over `X`, then every
`λ⁻`-homomorphism from `X` to a `κ`-monoid `K` extends uniquely to a `κ`-homomorphism on
`H`.

Paper proof: uniqueness is clear since `X` generates `H`.  For existence, well-definedness
of `φ̄ (Σᵢ xᵢ) := Σᵢ φ (xᵢ)` follows by telescoping along a braiding of two representations
`Σᵢ xᵢ = Σⱼ yⱼ`. -/
theorem extend_lhom {X : Type v} {H : Type w} [LMonoid lam X] [KMonoid κ H]
    (hlk : lam ≤ κ) (f : X → H) (hbr : IsBraidedOver lam κ X H hlk f)
    {K : Type t} [KMonoid κ K] (φ : X → K) (hφ : IsLHom hlk φ) :
    ∃! ψ : H → K, IsKHom κ ψ ∧ ∀ x, ψ (f x) = φ x := by
  classical
  have hκ : ℵ₀ ≤ κ := KMonoid.aleph0_le (κ := κ) (H := H)
  have hIdx : #(Idx κ) ≤ κ := le_of_eq (mk_Idx κ)
  choose rep hrep using hbr.generates
  set ψ : H → K := fun h => ksum (κ := κ) (fun i => φ (rep h i)) with hψdef
  -- `ψ` may be computed from an arbitrary representation.
  have key : ∀ (h : H) (x : Idx κ → X), h = ksum (κ := κ) (fun i => f (x i)) →
      ψ h = ksum (κ := κ) (fun i => φ (x i)) := by
    intro h x hx
    have hb : IsBraided lam (rep h) x := hbr.braided _ _ (by rw [← hrep h, ← hx])
    have := sumOf_map_eq_of_isBraided (H := K) hlk hφ hIdx hb
    rwa [sumOf_Idx, sumOf_Idx] at this
  -- `ψ` extends `φ`
  have hext : ∀ a : X, ψ (f a) = φ a := by
    intro a
    obtain ⟨i₀⟩ := nonempty_Idx hκ
    have hrepr : f a = ksum (κ := κ) (fun i => f (if i = i₀ then a else 0)) := by
      have : (fun i => f (if i = i₀ then a else 0)) = fun i => if i = i₀ then f a else 0 := by
        funext i
        by_cases hi : i = i₀ <;> simp [hi, hbr.isLHom.1]
      rw [this, ksum_single i₀ _ (fun i hi => if_neg hi), if_pos rfl]
    rw [key (f a) _ hrepr]
    have : (fun i => φ (if i = i₀ then a else 0)) = fun i => if i = i₀ then φ a else 0 := by
      funext i
      by_cases hi : i = i₀ <;> simp [hi, hφ.1]
    rw [this, ksum_single i₀ _ (fun i hi => if_neg hi), if_pos rfl]
  refine ⟨ψ, ⟨⟨?_, ?_⟩, hext⟩, ?_⟩
  · -- `ψ 0 = 0`
    have h0 : (0 : H) = ksum (κ := κ) (fun _ : Idx κ => f 0) := by
      simp [hbr.isLHom.1, ksum_zero]
    rw [key 0 _ h0]
    simp [hφ.1, ksum_zero]
  · -- `ψ` commutes with `κ`-sums
    intro h
    set x : Idx κ → Idx κ → X := fun i => rep (h i) with hxdef
    set π : Idx κ × Idx κ ≃ Idx κ := pairEquiv hκ with hπdef
    have hflat : ksum (κ := κ) h
        = ksum (κ := κ) (fun k => f (x (π.symm k).1 (π.symm k).2)) := by
      have h1 : (fun i => h i) = fun i => ksum (κ := κ) (fun j => f (x i j)) := by
        funext i; exact hrep (h i)
      calc ksum (κ := κ) h = ksum (κ := κ) (fun i => ksum (κ := κ) (fun j => f (x i j))) := by
            rw [← h1]
        _ = ksum (κ := κ) (fun k => f (x (π.symm k).1 (π.symm k).2)) :=
            ksum_sigma (fun i j => f (x i j)) π
    rw [key _ _ hflat]
    have h2 : (ψ ∘ h) = fun i => ksum (κ := κ) (fun j => φ (x i j)) := by
      funext i
      exact key (h i) (x i) (hrep (h i))
    rw [h2]
    exact (ksum_sigma (fun i j => φ (x i j)) π).symm
  · -- uniqueness
    rintro ψ' ⟨hhom', hext'⟩
    funext h
    have hr := hrep h
    calc ψ' h = ψ' (ksum (κ := κ) (fun i => f (rep h i))) := by rw [← hr]
      _ = ksum (κ := κ) (fun i => ψ' (f (rep h i))) := hhom'.2 _
      _ = ksum (κ := κ) (fun i => φ (rep h i)) := by
          congr 1; funext i; exact hext' _
      _ = ψ h := rfl


/-! ## Definition 3.11 -/

/-- Definition 3.11: `Ĥ` (with structure map `f`) is a *universal `κ`-extension* of the
`λ⁻`-monoid `X`.

The universe `z` of the test objects is a **parameter**, independent of `Ĥ`'s own universe `w`.
Lean cannot quantify over universes inside a term, so this is the only way to say "for every
`κ`-monoid `K`" without silently meaning "for every `K` in `Ĥ`'s universe", which would not be
enough for Examples 4.8(1): there `V^κ(C) ≅ F_κ(B)` compares a `Type u` with a `Type (u+1)`, since
`F_κ(B)` is built from cardinals.  The construction costs nothing: `extend_lhom` extends into a
`K` in any universe. -/
structure IsUniversalKExtension (lam κ : Cardinal.{u}) (X : Type v) (Hh : Type w)
    [LMonoid lam X] [KMonoid κ Hh] (hlk : lam ≤ κ) (f : X → Hh) : Prop where
  isLHom : IsLHom hlk f
  universal : ∀ (K : Type t) [KMonoid κ K] (φ : X → K), IsLHom hlk φ →
    ∃! ψ : Hh → K, IsKHom κ ψ ∧ ∀ x, ψ (f x) = φ x

/-- Being a universal `κ`-extension transports along an isomorphism of the base — a purely formal
consequence of the universal property, needing no reducedness. -/
theorem IsUniversalKExtension.of_base_iso {X₁ : Type v} {X₂ : Type z} {Hh : Type w}
    [LMonoid lam X₁] [LMonoid lam X₂] [KMonoid κ Hh] (hlk : lam ≤ κ) {f : X₁ → Hh}
    (h : IsUniversalKExtension.{u, v, w, t} lam κ X₁ Hh hlk f) (g : X₂ → X₁) (g' : X₁ → X₂)
    (hg : IsLMonoidHom lam g) (hg' : IsLMonoidHom lam g')
    (hgg' : ∀ x, g' (g x) = x) (hg'g : ∀ x, g (g' x) = x) :
    IsUniversalKExtension.{u, z, w, t} lam κ X₂ Hh hlk (fun x => f (g x)) where
  isLHom := by
    refine ⟨show f (g 0) = 0 by rw [hg.map_zero, h.isLHom.1], fun {ι} hι x => ?_⟩
    show f (g (lsumOf (lam := lam) hι x)) = _
    rw [hg hι x, h.isLHom.2 hι (g ∘ x)]
    rfl
  universal := by
    intro K _ φ hφ
    -- transport `φ` to the isomorphic base and use the universal property there
    have hφ' : IsLHom hlk (fun x₁ => φ (g' x₁)) := by
      refine ⟨show φ (g' 0) = 0 by rw [hg'.map_zero, hφ.1], fun {ι} hι x => ?_⟩
      show φ (g' (lsumOf (lam := lam) hι x)) = _
      rw [hg' hι x, hφ.2 hι (g' ∘ x)]
      rfl
    obtain ⟨ψ, ⟨hψhom, hψ⟩, hψu⟩ := h.universal K (fun x₁ => φ (g' x₁)) hφ'
    refine ⟨ψ, ⟨hψhom, fun x => ?_⟩, fun ψ' ⟨hψ'hom, hψ'⟩ => ?_⟩
    · rw [hψ (g x), hgg' x]
    · refine hψu ψ' ⟨hψ'hom, fun x₁ => ?_⟩
      have hx := hψ' (g' x₁)
      rw [hg'g x₁] at hx
      exact hx

/-- A universal `κ`-extension is unique up to a unique isomorphism, as for any object
defined by a universal property. -/
theorem isUniversalKExtension_unique {X : Type v} {H₁ H₂ : Type w}
    [LMonoid lam X] [KMonoid κ H₁] [KMonoid κ H₂] (hlk : lam ≤ κ)
    {f₁ : X → H₁} {f₂ : X → H₂}
    (h₁ : IsUniversalKExtension.{u, v, w, w} lam κ X H₁ hlk f₁)
    (h₂ : IsUniversalKExtension.{u, v, w, w} lam κ X H₂ hlk f₂) :
    ∃! e : H₁ → H₂, IsKHom κ e ∧ (∀ x, e (f₁ x) = f₂ x) ∧ Function.Bijective e := by
  have hcomp : ∀ {A B C : Type w} [KMonoid κ A] [KMonoid κ B] [KMonoid κ C] (g : A → B) (h : B → C),
      IsKHom κ g → IsKHom κ h → IsKHom κ (fun a => h (g a)) := by
    intro A B C _ _ _ g h hg hh
    refine ⟨by show h (g 0) = 0; rw [hg.1, hh.1], fun x => ?_⟩
    show h (g (ksum (κ := κ) x)) = ksum (κ := κ) (fun i => h (g (x i)))
    rw [hg.2 x, hh.2 (g ∘ x)]
    rfl
  have hid : ∀ {A : Type w} [KMonoid κ A], IsKHom κ (fun a : A => a) :=
    fun {A} _ => ⟨rfl, fun _ => rfl⟩
  obtain ⟨e12, ⟨he12hom, he12⟩, hu12⟩ := h₁.universal H₂ f₂ h₂.isLHom
  obtain ⟨e21, ⟨he21hom, he21⟩, _⟩ := h₂.universal H₁ f₁ h₁.isLHom
  obtain ⟨w₁, _, hw₁⟩ := h₁.universal H₁ f₁ h₁.isLHom
  obtain ⟨w₂, _, hw₂⟩ := h₂.universal H₂ f₂ h₂.isLHom
  have hleft : ∀ a, e21 (e12 a) = a := by
    have hA : (fun a => e21 (e12 a)) = w₁ :=
      hw₁ _ ⟨he12hom.comp he21hom, fun x => by
        show e21 (e12 (f₁ x)) = f₁ x
        rw [he12 x, he21 x]⟩
    have hB : (fun a : H₁ => a) = w₁ := hw₁ _ ⟨IsKHom.id', fun _ => rfl⟩
    exact fun a => congrFun (hA.trans hB.symm) a
  have hright : ∀ b, e12 (e21 b) = b := by
    have hA : (fun b => e12 (e21 b)) = w₂ :=
      hw₂ _ ⟨he21hom.comp he12hom, fun x => by
        show e12 (e21 (f₂ x)) = f₂ x
        rw [he21 x, he12 x]⟩
    have hB : (fun b : H₂ => b) = w₂ := hw₂ _ ⟨IsKHom.id', fun _ => rfl⟩
    exact fun b => congrFun (hA.trans hB.symm) b
  refine ⟨e12, ⟨he12hom, he12, Function.bijective_iff_has_inverse.mpr ⟨e21, hleft, hright⟩⟩, ?_⟩
  rintro e ⟨hehom, hecomm, -⟩
  exact hu12 e ⟨hehom, hecomm⟩

/-- **Uniqueness across universes.**  Two universal `κ`-extensions of the same base are uniquely
isomorphic even when they live in *different* universes — which is what the old definition, with
its test objects fixed to the extension's own universe, could not express.

Each extension is needed twice over: `h₁` extends into `H₂` and `h₂` into `H₁`, while `h₁'` and
`h₂'` supply the two identity-uniqueness steps.  Both are available in practice, because the
constructions that produce universal extensions — `IsBraidedOver.isUniversalKExtension` and hence
`theorem_3_12`, `lemma_3_14_free`, `krsa_ascent` — are polymorphic in the test universe. -/
theorem isUniversalKExtension_unique' {X : Type v} {H₁ : Type w} {H₂ : Type t}
    [LMonoid lam X] [KMonoid κ H₁] [KMonoid κ H₂] (hlk : lam ≤ κ)
    {f₁ : X → H₁} {f₂ : X → H₂}
    (h₁ : IsUniversalKExtension.{u, v, w, t} lam κ X H₁ hlk f₁)
    (h₁' : IsUniversalKExtension.{u, v, w, w} lam κ X H₁ hlk f₁)
    (h₂ : IsUniversalKExtension.{u, v, t, w} lam κ X H₂ hlk f₂)
    (h₂' : IsUniversalKExtension.{u, v, t, t} lam κ X H₂ hlk f₂) :
    ∃! e : H₁ → H₂, IsKHom κ e ∧ (∀ x, e (f₁ x) = f₂ x) ∧ Function.Bijective e := by
  obtain ⟨e12, ⟨he12hom, he12⟩, hu12⟩ := h₁.universal H₂ f₂ h₂.isLHom
  obtain ⟨e21, ⟨he21hom, he21⟩, _⟩ := h₂.universal H₁ f₁ h₁.isLHom
  obtain ⟨w₁, _, hw₁⟩ := h₁'.universal H₁ f₁ h₁.isLHom
  obtain ⟨w₂, _, hw₂⟩ := h₂'.universal H₂ f₂ h₂.isLHom
  have hleft : ∀ a, e21 (e12 a) = a := by
    have hA : (fun a => e21 (e12 a)) = w₁ :=
      hw₁ _ ⟨he12hom.comp he21hom, fun x => by
        show e21 (e12 (f₁ x)) = f₁ x
        rw [he12 x, he21 x]⟩
    have hB : (fun a : H₁ => a) = w₁ := hw₁ _ ⟨IsKHom.id', fun _ => rfl⟩
    exact fun a => congrFun (hA.trans hB.symm) a
  have hright : ∀ b, e12 (e21 b) = b := by
    have hA : (fun b => e12 (e21 b)) = w₂ :=
      hw₂ _ ⟨he21hom.comp he12hom, fun x => by
        show e12 (e21 (f₂ x)) = f₂ x
        rw [he21 x, he12 x]⟩
    have hB : (fun b : H₂ => b) = w₂ := hw₂ _ ⟨IsKHom.id', fun _ => rfl⟩
    exact fun b => congrFun (hA.trans hB.symm) b
  refine ⟨e12, ⟨he12hom, he12, Function.bijective_iff_has_inverse.mpr ⟨e21, hleft, hright⟩⟩, ?_⟩
  rintro e ⟨hehom, hecomm, -⟩
  exact hu12 e ⟨hehom, hecomm⟩

/-- A homomorphism of `λ⁻`-monoids carries braided families to braided families: keep the
partitions and push `u` and `v` forward. -/
theorem IsBraided.map_lmonoidHom {X : Type v} {Y : Type w} [LMonoid lam X] [LMonoid lam Y]
    {g : X → Y} (hg : IsLMonoidHom lam g) {ι : Type u} {x y : ι → X}
    (h : IsBraided lam x y) : IsBraided lam (fun i => g (x i)) (fun i => g (y i)) := by
  obtain ⟨d⟩ := h
  exact ⟨{ I := d.I
           J := d.J
           I_disjoint := d.I_disjoint
           J_disjoint := d.J_disjoint
           I_cover := d.I_cover
           J_cover := d.J_cover
           I_small := d.I_small
           J_small := d.J_small
           u := fun p => g (d.u p)
           v := fun p => g (d.v p)
           v_limit := fun a => by rw [d.v_limit a, hg.map_zero]
           hI := fun p => by
             rw [← hg.map_add, ← d.hI p, hg (d.I_small p) fun i : d.I p => x i]
             rfl
           hJ := fun p => by
             rw [← hg.map_add, ← d.hJ p, hg (d.J_small p) fun j : d.J p => y j]
             rfl }⟩

/-- For `λ = ℵ₀` a homomorphism of `λ⁻`-monoids is nothing but an additive map: every `λ⁻`-sum is
a finite sum, and additive maps preserve those.  (In particular the two `ℵ₀⁻`-monoid structures
that a commutative monoid can carry — the canonical one and one induced from a `κ`-monoid — have
the same homomorphisms.) -/
theorem isLMonoidHom_aleph0_of_add {X : Type v} {Y : Type w} [LMonoid (ℵ₀ : Cardinal.{u}) X]
    [LMonoid (ℵ₀ : Cardinal.{u}) Y] {g : X → Y} (h0 : g 0 = 0)
    (hadd : ∀ a b, g (a + b) = g a + g b) : IsLMonoidHom ℵ₀ g := by
  intro ι h x
  have : Finite ι := Cardinal.lt_aleph0_iff_finite.mp h
  have : Fintype ι := Fintype.ofFinite ι
  rw [LMonoid.lsumOf_aleph0_eq_finsum h x, LMonoid.lsumOf_aleph0_eq_finsum h (g ∘ x)]
  exact map_sum ({ toFun := g, map_zero' := h0, map_add' := hadd } : X →+ Y) x Finset.univ

/-- Braidedness over the base transports along an isomorphism of the base: if `H` is
`λ⁻`-braided over `X₁` and `g : X₂ → X₁` is an isomorphism of `λ⁻`-monoids, then `H` is
`λ⁻`-braided over `X₂` along `f ∘ g`. -/
theorem IsBraidedOver.of_base_iso {X₁ : Type v} {X₂ : Type z} {H : Type w} [LMonoid lam X₁]
    [LMonoid lam X₂] [KMonoid κ H] (hlk : lam ≤ κ) {f : X₁ → H}
    (hbr : IsBraidedOver lam κ X₁ H hlk f) {g : X₂ → X₁} {g' : X₁ → X₂}
    (hg : IsLMonoidHom lam g) (hg' : IsLMonoidHom lam g')
    (hgg' : ∀ x, g' (g x) = x) (hg'g : ∀ x, g (g' x) = x) :
    IsBraidedOver lam κ X₂ H hlk (fun x => f (g x)) where
  isLHom := by
    refine ⟨show f (g 0) = 0 by rw [hg.map_zero, hbr.isLHom.1], fun {ι} h x => ?_⟩
    show f (g (lsumOf (lam := lam) h x)) = _
    rw [hg h x, hbr.isLHom.2 h (g ∘ x)]
    rfl
  injective := fun a b hab => by
    rw [← hgg' a, ← hgg' b, hbr.injective hab]
  generates := fun h => by
    obtain ⟨x, hx⟩ := hbr.generates h
    refine ⟨fun i => g' (x i), ?_⟩
    rw [hx]
    exact congrArg _ (funext fun i => by rw [hg'g (x i)])
  braided := fun x y hxy => by
    have h := (hbr.braided (fun i => g (x i)) (fun i => g (y i)) hxy).map_lmonoidHom hg'
    simpa only [hgg'] using h

/-- Braidedness transports along an isomorphism of extensions: if `H₁` is `λ⁻`-braided over `X`
and `e : H₁ → H₂` is a bijective `κ`-homomorphism commuting with the two structure maps, then
`H₂` is `λ⁻`-braided over `X` as well. -/
theorem IsBraidedOver.of_iso {X : Type v} {H₁ H₂ : Type w} [LMonoid lam X] [KMonoid κ H₁]
    [KMonoid κ H₂] (hlk : lam ≤ κ) {f₁ : X → H₁} {f₂ : X → H₂}
    (hbr : IsBraidedOver lam κ X H₁ hlk f₁) {e : H₁ → H₂} (he : IsKHom κ e)
    (hbij : Function.Bijective e) (hcomm : ∀ x, e (f₁ x) = f₂ x) :
    IsBraidedOver lam κ X H₂ hlk f₂ where
  isLHom := by
    refine ⟨by rw [← hcomm 0, hbr.isLHom.1, he.1], fun {ι} h x => ?_⟩
    rw [← hcomm (lsumOf (lam := lam) h x), hbr.isLHom.2 h x,
      he.map_sumOf (h.le.trans hlk) (f₁ ∘ x)]
    exact congrArg _ (funext fun i => hcomm (x i))
  injective := fun a b hab => hbr.injective (hbij.1 (by rw [hcomm a, hcomm b]; exact hab))
  generates := fun h => by
    obtain ⟨h₁, rfl⟩ := hbij.2 h
    obtain ⟨x, hx⟩ := hbr.generates h₁
    refine ⟨x, ?_⟩
    rw [hx, he.2 (fun i => f₁ (x i))]
    exact congrArg _ (funext fun i => hcomm (x i))
  braided := fun x y hxy => by
    refine hbr.braided x y (hbij.1 ?_)
    rw [he.2 (fun i => f₁ (x i)), he.2 (fun i => f₁ (y i)),
      show (e ∘ fun i => f₁ (x i)) = (fun i => f₂ (x i)) from funext fun i => hcomm (x i),
      show (e ∘ fun i => f₁ (y i)) = (fun i => f₂ (y i)) from funext fun i => hcomm (y i)]
    exact hxy

/-- A `κ`-monoid braided over a subset `S` is generated by `S` as a `κ`-monoid: that is the
`generates` field, read as a statement about the `κ`-closure. -/
theorem IsBraidedOver.kGenerates_coe {H : Type v} [KMonoid κ H] {S : Set H} [LMonoid lam ↥S]
    {hlk : lam ≤ κ} (hbr : IsBraidedOver lam κ ↥S H hlk (fun y => (y : H))) :
    KGenerates κ S := by
  refine kGenerates_iff.mpr fun h => ?_
  obtain ⟨x, hx⟩ := hbr.generates h
  rw [hx]
  exact (isKSubmonoid_kclosure κ S).ksum_mem _ fun i => subset_kclosure (x i).2

/-- Braidedness over a `λ⁻`-closed *subset* depends only on the subset, not on the proof that it
is closed: two such proofs are proofs of the same proposition, so the induced `λ⁻`-monoid
structures are definitionally equal.  This is what lets a braiding be moved along an equality of
subsets, such as `V(R) = add [R]` in Corollary 4.7(1). -/
theorem IsBraidedOver.of_set_eq {H : Type v} [KMonoid κ H] (hlam : lam.IsRegular)
    {hlk : lam ≤ κ} {S T : Set H} (hS : IsLSubset lam hlk S) (hT : IsLSubset lam hlk T)
    (hST : S = T)
    (hbr : letI := hT.lmonoid hlam
      IsBraidedOver lam κ ↥T H hlk (fun y => (y : H))) :
    letI := hS.lmonoid hlam
    IsBraidedOver lam κ ↥S H hlk (fun y => (y : H)) := by
  subst hST
  exact hbr

/-- **Braidedness transported along a `κ`-isomorphism and cut down to a smaller base.**

Suppose `H₂` is `λ⁻`-braided over a subset `S`, that `e : H₁ → H₂` is an isomorphism of
`κ`-monoids, and that `T ⊆ H₁` is a `λ⁻`-closed subset which

* maps into `S`,
* is *divisor-closed* in `H₁` (`hsat`), and
* still generates `H₁` as a `κ`-monoid.

Then `H₁` is `λ⁻`-braided over `T`.

Only `braided` has content.  Two `T`-families with equal `κ`-sum are carried by `e` to two
`S`-families with equal `κ`-sum, hence are braided in `S`; the braiding families `u_μ`, `v_μ` are
then pulled back through `e` and land in `T` because each block sum `Σ_{I_μ} x i` lies in `T` and
`u_μ`, `v_μ` are summands of it.  This is how Lemma 5.1 replaces the base `V(R)` — where the
braiding of Corollary 4.5(3) lives — by the smaller base `add (x₁ + x₂)`. -/
theorem IsBraidedOver.of_kIso_subset {H₁ H₂ : Type w} [KMonoid κ H₁] [KMonoid κ H₂]
    (hlam : lam.IsRegular) {hlk : lam ≤ κ} {S : Set H₂} {T : Set H₁}
    (hS : IsLSubset lam hlk S) (hT : IsLSubset lam hlk T)
    (hbr : letI := hS.lmonoid hlam
      IsBraidedOver lam κ ↥S H₂ hlk (fun y => (y : H₂)))
    {e : H₁ → H₂} (he : IsKHom κ e) (hbij : Function.Bijective e)
    (hmaps : ∀ a ∈ T, e a ∈ S)
    (hsat : ∀ a ∈ T, ∀ b c : H₁, a = b + c → b ∈ T)
    (hgen : KGenerates κ T) :
    letI := hT.lmonoid hlam
    IsBraidedOver lam κ ↥T H₁ hlk (fun y => (y : H₁)) := by
  let := hS.lmonoid hlam
  let := hT.lmonoid hlam
  -- the inverse isomorphism
  obtain ⟨einv, hli, hri⟩ : ∃ g : H₂ → H₁, Function.LeftInverse g e ∧ Function.RightInverse g e :=
    ⟨(Equiv.ofBijective e hbij).symm, (Equiv.ofBijective e hbij).left_inv,
      (Equiv.ofBijective e hbij).right_inv⟩
  refine ⟨⟨rfl, fun {ι} h x => rfl⟩, Subtype.val_injective, fun h => ?_, fun x y hxy => ?_⟩
  · -- generation is `hgen`, read through `mem_kclosure_iff`
    obtain ⟨z, hzT, rfl⟩ := (mem_kclosure_iff hT.zero_mem h).mp (kGenerates_iff.mp hgen h)
    exact ⟨fun i => ⟨z i, hzT i⟩, rfl⟩
  -- the two `T`-families, carried into `S`
  have himg : ∀ z : ↥T, e (z : H₁) ∈ S := fun z => hmaps z z.2
  have hksum : ∀ z : Idx κ → ↥T,
      e (ksum (κ := κ) fun i => (z i : H₁)) = ksum (κ := κ) fun i => e (z i : H₁) :=
    fun z => he.2 _
  obtain ⟨D⟩ := hbr.braided (fun i => ⟨e (x i : H₁), himg (x i)⟩)
    (fun i => ⟨e (y i : H₁), himg (y i)⟩) (by rw [← hksum x, ← hksum y, hxy])
  -- every `u`, `v` of the braiding pulls back into `T`
  have hpull : ∀ (z : Idx κ → ↥T) (p : Idx κ × ℕ) (P : Set (Idx κ)) (hP : #P < lam)
      (a b : ↥S), KMonoid.sumOf (κ := κ) (hP.le.trans hlk) (fun i : P => e (z i : H₁))
        = ((a : H₂) + (b : H₂)) →
      einv (a : H₂) ∈ T ∧ einv (b : H₂) ∈ T ∧
        KMonoid.sumOf (κ := κ) (hP.le.trans hlk) (fun i : P => (z i : H₁))
          = einv (a : H₂) + einv (b : H₂) := by
    intro z p P hP a b hab
    have hblock : KMonoid.sumOf (κ := κ) (hP.le.trans hlk) (fun i : P => (z i : H₁)) ∈ T :=
      hT.sumOf_mem hP _ fun i => (z i).2
    have hsplit : KMonoid.sumOf (κ := κ) (hP.le.trans hlk) (fun i : P => (z i : H₁))
        = einv (a : H₂) + einv (b : H₂) := by
      refine hbij.1 ?_
      rw [he.map_add, hri (a : H₂), hri (b : H₂), ← hab]
      exact he.map_sumOf (hP.le.trans hlk) (fun i : P => (z i : H₁))
    exact ⟨hsat _ hblock _ _ hsplit, hsat _ hblock _ _ (hsplit.trans (add_comm _ _)), hsplit⟩
  have huv : ∀ p : Idx κ × ℕ, einv (D.v p : H₂) ∈ T ∧ einv (D.u p : H₂) ∈ T := by
    intro p
    obtain ⟨h₁, h₂, -⟩ := hpull x p (D.I p) (D.I_small p) (D.v p) (D.u p)
      (congrArg Subtype.val (D.hI p))
    exact ⟨h₁, h₂⟩
  refine ⟨{ I := D.I, J := D.J, I_disjoint := D.I_disjoint, J_disjoint := D.J_disjoint
            I_cover := D.I_cover, J_cover := D.J_cover
            I_small := D.I_small, J_small := D.J_small
            u := fun p => ⟨einv (D.u p : H₂), (huv p).2⟩
            v := fun p => ⟨einv (D.v p : H₂), (huv p).1⟩
            v_limit := fun a => Subtype.ext ?_
            hI := fun p => Subtype.ext ?_
            hJ := fun p => Subtype.ext ?_ }⟩
  · show einv (D.v (a, 0) : H₂) = (0 : H₁)
    rw [D.v_limit a]
    exact hbij.1 (by rw [hri, he.1]; rfl)
  · exact (hpull x p (D.I p) (D.I_small p) (D.v p) (D.u p)
      (congrArg Subtype.val (D.hI p))).2.2
  · exact (hpull y p (D.J p) (D.J_small p) (D.v (bsucc p)) (D.u p)
      (congrArg Subtype.val (D.hJ p))).2.2

/-- Being `λ⁻`-braided over `X` implies being the universal `κ`-extension of `X`
(the second half of Theorem 3.12(2)); it is immediate from Proposition 3.10. -/
theorem IsBraidedOver.isUniversalKExtension {X : Type v} {H : Type w}
    [LMonoid lam X] [KMonoid κ H] (hlk : lam ≤ κ) {f : X → H}
    (hbr : IsBraidedOver lam κ X H hlk f) :
    IsUniversalKExtension lam κ X H hlk f :=
  { isLHom := hbr.isLHom
    universal := fun _K _ φ hφ => extend_lhom hlk f hbr φ hφ }

end KappaMonoid
