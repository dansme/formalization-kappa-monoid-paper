/-
Homomorphisms and sub-objects at the `λ⁻`-level, and the structures they induce:
`IsLMonoidHom`, `IsLSubmonoid`, `IsLSubset` and the `LMonoid` instance on a `λ⁻`-closed subset.
-/
import KappaMonoid.Core.KMonoid
import Mathlib.Algebra.Group.Submonoid.Basic

universe u v w

open Cardinal Function Set

namespace KappaMonoid

/-! ## Induced structures on sub-objects -/

/-- The commutative monoid structure on a subset containing `0` and closed under `+`. -/
@[instance_reducible]
def addCommMonoidOfClosed {H : Type v} [AddCommMonoid H] {S : Set H} (h0 : (0 : H) ∈ S)
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) : AddCommMonoid ↥S :=
  inferInstanceAs (AddCommMonoid
    ↥({ carrier := S, add_mem' := fun {a b} ha hb => hadd a ha b hb, zero_mem' := h0 } :
      AddSubmonoid H))

/-- A homomorphism of `λ⁻`-monoids: a map commuting with all `λ⁻`-sums.  It automatically
preserves `0`, the empty sum (`IsLMonoidHom.map_zero`). -/
def IsLMonoidHom (lam : Cardinal.{u}) {X : Type v} {Y : Type w} [LMonoid lam X] [LMonoid lam Y]
    (f : X → Y) : Prop :=
  ∀ {ι : Type u} (h : #ι < lam) (x : ι → X),
    f (LMonoid.lsumOf (lam := lam) h x) = LMonoid.lsumOf (lam := lam) h (f ∘ x)

namespace IsLMonoidHom

variable {lam : Cardinal.{u}} {X : Type v} {Y : Type w} [LMonoid lam X] [LMonoid lam Y]
  {f : X → Y}

/-- A homomorphism preserves `0`, being the empty sum. -/
theorem map_zero (hf : IsLMonoidHom lam f) : f 0 = 0 := by
  have := LMonoid.factRegular (lam := lam) (X := X)
  have h := hf CardLT.lt (PEmpty.elim : PEmpty.{u + 1} → X)
  rwa [LMonoid.lsumOf_isEmpty, LMonoid.lsumOf_isEmpty] at h

/-- A homomorphism preserves `+`, a two-term sum. -/
theorem map_add (hf : IsLMonoidHom lam f) (a b : X) : f (a + b) = f a + f b := by
  have hUB : #(ULift.{u} Bool) < lam := LMonoid.mk_uLift_bool_lt (X := X)
  have h := hf hUB (fun p : ULift.{u} Bool => if p.down then a else b)
  rw [LMonoid.lsumOf_two a b] at h
  rw [h, show (f ∘ fun p : ULift.{u} Bool => if p.down then a else b)
      = fun p : ULift.{u} Bool => if p.down then f a else f b from
    funext fun p => by obtain ⟨(_ | _)⟩ := p <;> rfl]
  exact LMonoid.lsumOf_two (f a) (f b)

/-- The inverse of a bijective homomorphism is a homomorphism: apply the original one to both
sides and use its injectivity. -/
theorem inv {g : X → Y} (hg : IsLMonoidHom lam g) {g' : Y → X}
    (hgg' : ∀ x, g' (g x) = x) (hg'g : ∀ y, g (g' y) = y) : IsLMonoidHom lam g' := by
  have hinj : Function.Injective g := fun a b hab => by rw [← hgg' a, hab, hgg' b]
  intro ι h y
  refine hinj ?_
  rw [hg'g, hg h (g' ∘ y)]
  exact congrArg _ (funext fun i => (hg'g (y i)).symm)

/-- A homomorphism preserves cardinal scalar multiplication, which is a sum. -/
theorem map_lcmul (hf : IsLMonoidHom lam f) {α : Cardinal.{u}} (hα : α < lam) (x : X) :
    f (LMonoid.lcmul (lam := lam) α hα x) = LMonoid.lcmul (lam := lam) α hα (f x) :=
  hf _ (fun _ : Idx α => x)

end IsLMonoidHom

/-- A `λ⁻`-submonoid of a `λ⁻`-monoid: a subset containing `0` and closed under `λ⁻`-sums. -/
structure IsLSubmonoid (lam : Cardinal.{u}) {X : Type v} [LMonoid lam X] (S : Set X) : Prop where
  /-- A `λ⁻`-submonoid contains `0`. -/
  zero_mem : (0 : X) ∈ S
  /-- A `λ⁻`-submonoid is closed under `λ⁻`-sums. -/
  lsumOf_mem : ∀ {ι : Type u} (h : #ι < lam) (x : ι → X), (∀ i, x i ∈ S) →
    LMonoid.lsumOf (lam := lam) h x ∈ S

namespace IsLSubmonoid

variable {lam : Cardinal.{u}} {X : Type v} [LMonoid lam X] {S : Set X}

/-- A `λ⁻`-submonoid is closed under `+`, being closed under two-term sums. -/
theorem add_mem (hS : IsLSubmonoid lam S) {a b : X} (ha : a ∈ S) (hb : b ∈ S) : a + b ∈ S := by
  have hUB : #(ULift.{u} Bool) < lam := LMonoid.mk_uLift_bool_lt (X := X)
  have hmem := hS.lsumOf_mem hUB (fun p : ULift.{u} Bool => if p.down then a else b)
    (by rintro ⟨(_ | _)⟩ <;> simpa)
  rwa [LMonoid.lsumOf_two a b] at hmem

/-- A `λ⁻`-submonoid of a `λ⁻`-monoid is itself a `λ⁻`-monoid. -/
@[instance_reducible]
noncomputable def lmonoid (hS : IsLSubmonoid lam S) : LMonoid lam ↥S :=
  letI acm : AddCommMonoid ↥S :=
    addCommMonoidOfClosed hS.zero_mem fun _ ha _ hb => hS.add_mem ha hb
  { toAddCommMonoid := acm
    isRegular := LMonoid.isRegular' (X := X)
    sum := fun {ι} h x =>
      ⟨LMonoid.lsumOf (lam := lam) h fun i => (x i : X), hS.lsumOf_mem h _ fun i => (x i).2⟩
    sum_congr := fun h h' e x =>
      Subtype.ext (LMonoid.lsumOf_congr h h' e fun i => (x i : X))
    sum_unique := fun h x => Subtype.ext (LMonoid.lsumOf_unique (h := ⟨h⟩) fun i => (x i : X))
    sum_sigma := fun h hρ x hσ =>
      Subtype.ext
        (LMonoid.lsumOf_sigma (h := ⟨h⟩) (hρ := fun i => ⟨hρ i⟩) (fun i j => (x i j : X)))
    add_eq_sum := fun h a b => Subtype.ext (by
      show (a : X) + (b : X) = LMonoid.lsumOf (lam := lam) h _
      rw [LMonoid.add_eq_lsumOf (lam := lam) h (a : X) (b : X)]
      exact congrArg _ (funext fun p => by rcases p with p | p <;> rfl)) }

/-- The inclusion of a `λ⁻`-submonoid preserves `λ⁻`-sums. -/
theorem coe_lsumOf (hS : IsLSubmonoid lam S) {ι : Type u} (h : #ι < lam) (x : ι → S) :
    letI := hS.lmonoid
    ((LMonoid.lsumOf (lam := lam) h x : S) : X)
      = LMonoid.lsumOf (lam := lam) h fun i => (x i : X) := rfl

end IsLSubmonoid

/-- A subset of a `κ`-monoid closed under `λ⁻`-sums. -/
structure IsLSubset (lam : Cardinal.{u}) {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]
    (hlk : lam ≤ Order.succ κ) (S : Set H) : Prop where
  zero_mem : (0 : H) ∈ S
  sumOf_mem : ∀ {ι : Type u} (h : #ι < lam) (x : ι → H), (∀ i, x i ∈ S) →
    ∑[≤ κ] i, x i ∈ S

/-- A `λ⁻`-closed subset is closed under binary sums: `a + b` is a sum indexed by `Bool`, and
`#(ULift Bool) < ℵ₀ ≤ lam`. -/
theorem IsLSubset.add_mem {lam κ : Cardinal.{u}} {H : Type v} [KMonoid κ H] {hlk : lam ≤ Order.succ κ}
    {S : Set H} (hS : IsLSubset lam hlk S) (hlam : ℵ₀ ≤ lam) {a b : H} (ha : a ∈ S)
    (hb : b ∈ S) : a + b ∈ S := by
  classical
  have hUB : #(ULift.{u} Bool) < lam :=
    lt_of_lt_of_le (Cardinal.lt_aleph0_iff_finite.mpr inferInstance) hlam
  have hmem := hS.sumOf_mem hUB (fun p : ULift.{u} Bool => if p.down then a else b)
    (by rintro ⟨(_ | _)⟩ <;> simpa)
  rwa [KMonoid.sumOf_two a b] at hmem

/-- A `λ⁻`-closed subset is closed under finite multiples. -/
theorem IsLSubset.nsmul_mem {lam κ : Cardinal.{u}} {H : Type v} [KMonoid κ H] {hlk : lam ≤ Order.succ κ}
    {S : Set H} (hS : IsLSubset lam hlk S) (hlam : ℵ₀ ≤ lam) {a : H} (ha : a ∈ S) (n : ℕ) :
    n • a ∈ S := by
  induction n with
  | zero => rw [zero_nsmul]; exact hS.zero_mem
  | succ p hp => rw [succ_nsmul]; exact hS.add_mem hlam hp ha

namespace KMonoid

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-- A `κ`-submonoid of a `κ`-monoid is itself a `κ`-monoid. -/
@[instance_reducible]
noncomputable def IsKSubmonoid.kmonoid {S : Set H} (hS : IsKSubmonoid κ S) : KMonoid κ ↥S :=
  letI acm : AddCommMonoid ↥S :=
    addCommMonoidOfClosed hS.zero_mem fun _ ha _ hb => hS.add_mem ha hb
  { toAddCommMonoid := acm
    aleph0_le := aleph0_le (κ := κ) (H := H)
    isRegular := isRegular_succ' (H := H)
    sum := fun {ι} h x =>
      ⟨∑[≤ κ] i, (x i : H),
        hS.sumOf_mem (h := ⟨h⟩) _ fun i => (x i).2⟩
    sum_congr := fun h h' e x =>
      Subtype.ext (sumOf_equiv (h := CardLE.mk' (le_of_lt_succ h')) (h' := CardLE.mk' (le_of_lt_succ h)) e fun i => (x i : H)).symm
    sum_unique := fun h x =>
      Subtype.ext (sumOf_unique (h := CardLE.mk' (le_of_lt_succ h)) fun i => (x i : H))
    sum_sigma := fun h hρ x hσ =>
      Subtype.ext (sumOf_sigma (h := CardLE.mk' (le_of_lt_succ h)) (hρ := fun p => CardLE.mk' ((fun i => le_of_lt_succ (hρ i)) p)) fun i j => (x i j : H))
    add_eq_sum := fun h a b => Subtype.ext (by
      show (a : H) + (b : H) = LMonoid.lsumOf (lam := Order.succ κ) _ _
      rw [LMonoid.add_eq_lsumOf (lam := Order.succ κ) (le_of_lt_succ h |> lt_succ) (a : H) (b : H)]
      exact congrArg _ (funext fun p => by rcases p with p | p <;> rfl)) }

/-- A `λ⁻`-closed subset of a `κ`-monoid is a `λ⁻`-monoid. -/
@[instance_reducible]
noncomputable def _root_.KappaMonoid.IsLSubset.lmonoid {lam : Cardinal.{u}} {hlk : lam ≤ Order.succ κ} {S : Set H}
    (hlam : lam.IsRegular) (hS : IsLSubset lam hlk S) : LMonoid lam ↥S :=
  letI hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := by
    intro a ha b hb
    have hUB : #(ULift.{u} Bool) < lam :=
      lt_of_lt_of_le (Cardinal.lt_aleph0_iff_finite.mpr inferInstance) hlam.aleph0_le
    have hmem := hS.sumOf_mem hUB (fun p : ULift.{u} Bool => if p.down then a else b)
      (by rintro ⟨(_ | _)⟩ <;> simpa)
    rwa [sumOf_two a b] at hmem
  letI acm : AddCommMonoid ↥S := addCommMonoidOfClosed hS.zero_mem hadd
  { toAddCommMonoid := acm
    isRegular := hlam
    sum := fun {ι} h x =>
      ⟨∑[≤ κ] i, (x i : H), hS.sumOf_mem h _ fun i => (x i).2⟩
    sum_congr := fun h h' e x =>
      Subtype.ext (sumOf_equiv (h := CardLE.mk' (le_of_lt_of_le_succ hlk h')) (h' := CardLE.mk' (le_of_lt_of_le_succ hlk h)) e fun i => (x i : H)).symm
    sum_unique := fun h x =>
      Subtype.ext (sumOf_unique (h := CardLE.mk' (le_of_lt_of_le_succ hlk h)) fun i => (x i : H))
    sum_sigma := fun h hρ x hσ =>
      Subtype.ext (sumOf_sigma (h := CardLE.mk' (le_of_lt_of_le_succ hlk h)) (hρ := fun p => CardLE.mk' ((fun i => le_of_lt_of_le_succ hlk (hρ i)) p)) fun i j => (x i j : H))
    add_eq_sum := fun h a b => Subtype.ext (by
      show (a : H) + (b : H) = LMonoid.lsumOf (lam := Order.succ κ) _ _
      rw [LMonoid.add_eq_lsumOf (lam := Order.succ κ) (lt_succ (le_of_lt_of_le_succ hlk h)) (a : H) (b : H)]
      exact congrArg _ (funext fun p => by rcases p with p | p <;> rfl)) }

/-- The inclusion of a `κ`-submonoid preserves sums over arbitrary small index types. -/
theorem IsKSubmonoid.coe_sumOf {T : Set H} (hT : IsKSubmonoid κ T) {ι : Type u} (hι : #ι ≤ κ)
    (z : ι → T) :
    letI := hT.kmonoid
    ((∑[≤ κ] i, z i : T) : H) = ∑[≤ κ] i, (z i : H) := rfl

/-- The inclusion of a `κ`-submonoid preserves `κ`-sums. -/
theorem IsKSubmonoid.coe_ksum {T : Set H} (hT : IsKSubmonoid κ T) (z : Idx κ → T) :
    letI := hT.kmonoid
    ((ksum (κ := κ) z : T) : H) = ksum (κ := κ) fun i => (z i : H) := rfl

/-- `⟨S⟩_κ` is a `κ`-monoid.  `IsKSubmonoid` is a `Prop`, so this is definitionally the structure
`(isKSubmonoid_kclosure κ S).kmonoid`, and promoting it costs nothing (trap 13). -/
noncomputable instance instKMonoidKclosure (S : Set H) : KMonoid κ ↥(kclosure κ S) :=
  (isKSubmonoid_kclosure κ S).kmonoid

/-- The inclusion of `⟨S⟩_κ` preserves sums over arbitrary small index types. -/
theorem coe_sumOf_kclosure (S : Set H) {ι : Type u} [CardLE ι κ] (z : ι → kclosure κ S) :
    ((∑[≤ κ] i, z i : kclosure κ S) : H) = ∑[≤ κ] i, (z i : H) := rfl

/-- The inclusion of `⟨S⟩_κ` preserves `κ`-sums. -/
theorem coe_ksum_kclosure (S : Set H) (z : Idx κ → kclosure κ S) :
    ((ksum (κ := κ) z : kclosure κ S) : H) = ksum (κ := κ) fun i => (z i : H) := rfl

/-- The inclusion of a `λ⁻`-closed subset preserves `λ⁻`-sums: they are computed as the
ambient `κ`-sums. -/
theorem _root_.KappaMonoid.IsLSubset.coe_lsumOf {lam : Cardinal.{u}} {hlk : lam ≤ Order.succ κ} {S : Set H}
    (hlam : lam.IsRegular) (hS : IsLSubset lam hlk S) {ι : Type u} (hι : #ι < lam) (z : ι → S) :
    letI := hS.lmonoid hlam
    ((LMonoid.lsumOf (lam := lam) hι z : S) : H)
      = ∑[≤ κ] i, (z i : H) := rfl

/-- **A `κ`-homomorphism restricts to a homomorphism of `λ⁻`-monoids** between `λ⁻`-closed
subsets it maps into one another: `λ⁻`-sums in a `λ⁻`-closed subset are the ambient `κ`-sums
(`IsLSubset.coe_lsumOf`), which the `κ`-homomorphism preserves. -/
theorem IsKHom.restrict_isLMonoidHom {K : Type v} [KMonoid κ K] {lam : Cardinal.{u}}
    {hlk : lam ≤ Order.succ κ} {S : Set H} {T : Set K} (hlam : lam.IsRegular)
    (hS : IsLSubset lam hlk S) (hT : IsLSubset lam hlk T) {e : H → K} (he : IsKHom κ e)
    (hmaps : ∀ a ∈ S, e a ∈ T) :
    letI := hS.lmonoid hlam
    letI := hT.lmonoid hlam
    IsLMonoidHom lam (fun a : ↥S => (⟨e a, hmaps a a.2⟩ : ↥T)) := by
  let := hS.lmonoid hlam
  let := hT.lmonoid hlam
  intro ι h x
  refine Subtype.ext ?_
  show e ((LMonoid.lsumOf (lam := lam) h x : S) : H) = _
  rw [hS.coe_lsumOf hlam h x, he.map_sumOf (h := CardLE.mk' (le_of_lt_of_le_succ hlk h)) (fun i => (x i : H))]
  rfl

/-- A `κ`-monoid is a `λ⁻`-monoid for every regular `λ ≤ κ⁺` (Remark 2.19). -/
@[instance_reducible]
noncomputable def toLMonoidOfLE (H : Type v) [KMonoid κ H] {lam : Cardinal.{u}}
    (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ) : LMonoid lam H :=
  LMonoid.ofLE (lam₂ := Order.succ κ) hlam (hlk)

/-- The `λ⁻`-sums induced on a `κ`-monoid by `toLMonoidOfLE` are its `κ`-sums. -/
theorem toLMonoidOfLE_lsumOf {lam : Cardinal.{u}} (hlam : lam.IsRegular) (hlk : lam ≤ Order.succ κ)
    {ι : Type u} (h : #ι < lam) (x : ι → H) :
    letI := toLMonoidOfLE H hlam hlk
    LMonoid.lsumOf (lam := lam) h x = ∑[≤ κ] i, x i := rfl

/-- The first bullet after Lemma 2.5: restricting `Σ` to families indexed by a type of
cardinality `≤ α` makes a `κ`-monoid an `α`-monoid, for every infinite `α ≤ κ`. -/
@[instance_reducible]
noncomputable def ofLE (H : Type v) [KMonoid κ H] {α : Cardinal.{u}} (hα0 : ℵ₀ ≤ α)
    (hακ : α ≤ κ) : KMonoid α H where
  toLMonoid :=
    LMonoid.ofLE (lam₂ := Order.succ κ) (Cardinal.isRegular_succ hα0) (Order.succ_le_succ hακ)
  aleph0_le := hα0

/-- The `α`-sums induced on a `κ`-monoid by `ofLE` are its `κ`-sums. -/
@[simp] theorem ofLE_sumOf (H : Type v) [KMonoid κ H] {α : Cardinal.{u}} (hα0 : ℵ₀ ≤ α)
    (hακ : α ≤ κ) {ι : Type u} (h : #ι ≤ α) (x : ι → H) :
    letI := ofLE H hα0 hακ
    ∑[≤ α] i, x i = ∑[≤ κ] i, x i := rfl

/-- A product of `κ`-monoids is a `κ`-monoid, with coordinatewise summation.  This is the
`κ`-monoid `F_κ^B` of §2.1 when each factor is `F_κ`. -/
@[instance_reducible]
noncomputable def pi (κ : Cardinal.{u}) {B : Type w} (Y : B → Type v) [∀ b, KMonoid κ (Y b)]
    (hκ : ℵ₀ ≤ κ) : KMonoid κ (∀ b, Y b) where
  toLMonoid := LMonoid.pi (Order.succ κ) Y (Cardinal.isRegular_succ hκ)
  aleph0_le := hκ

/-- A product of `ℵ₀`-monoids is an `ℵ₀`-monoid.  This is `pi` at the distinguished cardinal,
promoted to an instance: the products `F_{ℵ₀}^n` of §5 are named in almost every statement there,
and their `ℵ₀`-monoid structure is not worth repeating. -/
noncomputable instance instPiAleph0 {B : Type w} (Y : B → Type v)
    [∀ b, KMonoid (ℵ₀ : Cardinal.{u}) (Y b)] : KMonoid (ℵ₀ : Cardinal.{u}) (∀ b, Y b) :=
  pi ℵ₀ Y le_rfl

/-- Sums in a product of `κ`-monoids are computed coordinatewise. -/
@[simp] theorem pi_sumOf (κ : Cardinal.{u}) {B : Type w} (Y : B → Type v) [∀ b, KMonoid κ (Y b)]
    (hκ : ℵ₀ ≤ κ) {ι : Type u} (h : #ι ≤ κ) (x : ι → ∀ b, Y b) (b : B) :
    letI := pi κ Y hκ
    (∑[≤ κ] i, x i) b = ∑[≤ κ] i, x i b := rfl

end KMonoid

end KappaMonoid
