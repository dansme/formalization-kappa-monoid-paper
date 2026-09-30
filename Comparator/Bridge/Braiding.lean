import Comparator.Bridge.Monoid

/-!
# Bridge, part 2: braidings and universal extensions

The challenge's Definition 3.1 indexes the braiding partitions by `Idx κ` itself, with its
well-order; the library's `IsBraided` uses the normal form `ι × ℕ`, and Lemma 3.5
(`isBraidedOn_ofWellOrder_iff`) says the two agree.  The challenge takes the base `X` to be a
subset of `H` with the ambient sums; the library takes a `λ⁻`-monoid with a map into `H`.
-/

universe u v w t

open Cardinal Function Set
open scoped KappaMonoid

namespace KappaChallenge

attribute [-instance] KMonoid.instAdd KMonoid.instSMul LMonoid.instAdd KMonoid.toZero LMonoid.toZero

variable {κ : Cardinal.{u}} {H : Type w}
variable {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] [NoMaxOrder ι] [SuccOrder ι]

theorem wsucc_eq (a : ι) : KappaMonoid.wsucc a = Order.succ a :=
  le_antisymm (KappaMonoid.wsucc_le (Order.lt_succ a)) (Order.succ_le_of_lt (KappaMonoid.lt_wsucc a))

section

variable [L : KappaMonoid.KMonoid κ H] {C : KMonoid κ H} (hc : KMonoid.Compat C L)
  {lam : Cardinal.{u}} (hlk : lam ≤ Order.succ κ)
include hc

/-- A library braiding of families in `X` maps to a challenge braiding in the image of a
`λ⁻`-homomorphism `f : X → H`. -/
theorem isBraided_of_lib {X : Type v} [KappaMonoid.LMonoid lam X] {f : X → H}
    (hf : KappaMonoid.LMonoid.IsLHom hlk f) {x y : ι → X} (h : KappaMonoid.IsBraided lam x y) :
    IsBraided lam (range f) (f ∘ x) (f ∘ y) := by
  obtain ⟨d⟩ := (KappaMonoid.isBraidedOn_ofWellOrder_iff x y).mpr h
  have hle : ∀ {S : Set ι}, #S < lam → #S ≤ κ := fun h => Order.le_of_lt_succ (h.trans_le hlk)
  have hsum : ∀ (S : Set ι) (hS : #S < lam) (z : ι → X) (a b : X),
      KappaMonoid.LMonoid.lsumOf hS (fun i : S => z i) = a + b →
      @KMonoid.sumOf κ H C S (fun i : S => (f ∘ z) i) = f a +[C] f b := by
    intro S hS z a b hab
    calc @KMonoid.sumOf κ H C S (fun i : S => (f ∘ z) i)
        = ∑[≤ κ] i : S, (f ∘ fun i : S => z i) i := (hc.sumOf' (hle hS) _).symm
      _ = f (KappaMonoid.LMonoid.lsumOf hS fun i : S => z i) := (hf.2 hS _).symm
      _ = f a + f b := by rw [hab, KappaMonoid.IsLHom.map_add hlk hf]
      _ = f a +[C] f b := hc.add _ _
  refine ⟨d.I, d.J, f ∘ d.u, f ∘ d.v, ⟨d.I_disjoint, d.I_cover, d.I_lt⟩,
    ⟨d.J_disjoint, d.J_cover, d.J_lt⟩, fun μ => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, fun μ hμ => ?_,
    fun μ => ⟨hsum _ (d.I_lt μ) x _ _ (d.hI μ), ?_⟩⟩
  · show f (d.v μ) = 𝟎[C]
    rw [d.v_limit μ fun ν hν =>
      Order.isSuccPrelimit_iff_succ_ne.mp hμ ν (by rw [← wsucc_eq]; exact hν), hf.1, hc.zero]
  · have := hsum _ (d.J_lt μ) y _ _ (d.hJ μ)
    rwa [show (KappaMonoid.LimitSucc.ofWellOrder ι).succ μ = Order.succ μ from wsucc_eq μ] at this

omit [LinearOrder ι] [WellFoundedLT ι] [NoMaxOrder ι] [SuccOrder ι] in
/-- A sum over `ι` is the `κ`-sum along a bijection `ι ≃ κ`. -/
theorem KMonoid.Compat.sumOf_eq_ksum (e : ι ≃ Idx κ) (z : ι → H) :
    @KMonoid.sumOf κ H C ι z = KappaMonoid.KMonoid.ksum (κ := κ) (z ∘ e.symm) := by
  have := KappaMonoid.CardLE.mk' (le_of_eq ((Cardinal.mk_congr e).trans (KappaMonoid.mk_Idx κ)))
  have := KappaMonoid.CardLE.mk' (KappaMonoid.mk_Idx κ).le
  rw [← hc.sumOf, KappaMonoid.KMonoid.sumOf_equiv e.symm z]
  rfl

/-- Library braidings of the `κ`-indexed families in the image of `f` give challenge braidings of
the `ι`-indexed ones, for any limit well-order `ι` on `κ`. -/
theorem isBraided_of_lib_idx (hι : #ι = κ) {X : Type v} [KappaMonoid.LMonoid lam X] {f : X → H}
    (hf : KappaMonoid.LMonoid.IsLHom hlk f)
    (hbr : ∀ x y : Idx κ → X, KappaMonoid.KMonoid.ksum (κ := κ) (fun i => f (x i)) =
      KappaMonoid.KMonoid.ksum (κ := κ) (fun i => f (y i)) → KappaMonoid.IsBraided lam x y)
    (x y : ι → H) (hx : ∀ i, x i ∈ range f) (hy : ∀ i, y i ∈ range f)
    (hxy : @KMonoid.sumOf κ H C ι x = @KMonoid.sumOf κ H C ι y) :
    IsBraided lam (range f) x y := by
  obtain ⟨e⟩ : Nonempty (ι ≃ Idx κ) := Cardinal.eq.mp (hι.trans (KappaMonoid.mk_Idx κ).symm)
  choose x' hx' using hx
  choose y' hy' using hy
  obtain rfl : f ∘ x' = x := funext hx'
  obtain rfl : f ∘ y' = y := funext hy'
  rw [hc.sumOf_eq_ksum e, hc.sumOf_eq_ksum e] at hxy
  have hb := KappaMonoid.IsBraided.comp_equiv e (hbr (x' ∘ e.symm) (y' ∘ e.symm) hxy)
  simp only [comp_apply, Equiv.symm_apply_apply] at hb
  exact isBraided_of_lib hc hlk hf hb

/-- The image of a `λ⁻`-homomorphism is `λ⁻`-closed. -/
theorem isLSubmonoid_range {X : Type v} [KappaMonoid.LMonoid lam X] {f : X → H}
    (hf : KappaMonoid.LMonoid.IsLHom hlk f) : @KMonoid.IsLSubmonoid κ H C lam (range f) := by
  refine (hc.isLSubmonoid hlk _).mpr ⟨⟨0, hf.1⟩, fun {ι} hι z hz => ?_⟩
  choose z' hz' using hz
  refine ⟨KappaMonoid.LMonoid.lsumOf hι z', ?_⟩
  rw [hf.2 hι z']
  exact congrArg _ (funext hz')

omit [LinearOrder ι] [WellFoundedLT ι] [NoMaxOrder ι] [SuccOrder ι] in
/-- **Definition 3.1(2)**: a library braiding over `X` via `f` is a challenge braiding over
`range f`, for any limit well-order `ι` on `κ`. -/
theorem isBraidedOver_of_lib (ι : Type u) [LinearOrder ι] [WellFoundedLT ι] [NoMaxOrder ι]
    [SuccOrder ι] (hι : #ι = κ) {X : Type v} [KappaMonoid.LMonoid lam X] {f : X → H}
    (h : KappaMonoid.IsBraidedOver lam κ X H hlk f) : IsBraidedOver ι lam (range f) := by
  refine ⟨isLSubmonoid_range hc hlk h.isLHom, fun a => ?_,
    isBraided_of_lib_idx hc hlk hι h.isLHom h.braided⟩
  obtain ⟨z, rfl⟩ := h.generates a
  exact ⟨_, fun i => Or.inl ⟨z i, rfl⟩, hc.sum _⟩

/-- **Definition 3.11**: a library universal `κ`-extension via `f` is a challenge universal
`κ`-extension of `range f`. -/
theorem isUniversalOver_of_lib {X : Type v} [KappaMonoid.LMonoid lam X] {f : X → H}
    (h : KappaMonoid.IsUniversalKExtension.{u, v, w, t} lam κ X H hlk f) :
    @IsUniversalOver.{u, w, t} κ H C lam (range f) := by
  refine ⟨isLSubmonoid_range hc hlk h.isLHom, fun K CK φ hφ0 hφ => ?_⟩
  let LK := CK.toLib
  have hcK := KMonoid.compat_toLib CK
  have hφ' : KappaMonoid.LMonoid.IsLHom hlk (φ ∘ f) := by
    refine ⟨?_, fun {ι} hι z => ?_⟩
    · show φ (f 0) = 0
      rw [h.isLHom.1, ← hcK.zero, ← hc.zero]
      exact hφ0
    · have hle := Order.le_of_lt_succ (hι.trans_le hlk)
      show φ (f (KappaMonoid.LMonoid.lsumOf hι z)) = _
      rw [h.isLHom.2 hι z, hc.sumOf' hle, hφ ι (f ∘ z) hι fun i => ⟨z i, rfl⟩, ← hcK.sumOf' hle]
      rfl
  obtain ⟨ψ, ⟨hψ, hψf⟩, huniq⟩ := h.universal K (φ ∘ f) hφ'
  refine ⟨ψ, ⟨(hc.isHom hcK ψ).mpr hψ, ?_⟩, fun ψ' ⟨hψ', hψ'f⟩ => ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact hψf a
  · exact huniq ψ' ⟨(hc.isHom hcK ψ').mp hψ', fun a => hψ'f _ ⟨a, rfl⟩⟩

end

end KappaChallenge
