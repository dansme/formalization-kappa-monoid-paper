/-
`KMonoid` (Definition 2.1) as a `λ⁻`-monoid for `λ = κ⁺`: summation, the canonical index type,
cardinal scalar multiplication, reducedness (**Lemma 2.8**), homomorphisms, submonoids and
generation.
-/
import KappaMonoid.Core.LMonoid

universe u v w t

open Cardinal Function Set

namespace KappaMonoid

/-! ## `κ`-monoids (Definition 2.1)

A `κ`-monoid is a `λ⁻`-monoid for `λ = κ⁺` (Remark 2.19): the families that may be summed
are those indexed by a type of cardinality `< κ⁺`, i.e. of cardinality `≤ κ`. -/

/-- A `κ`-monoid: a commutative monoid with a summation operation for families indexed by a
type of cardinality `≤ κ`, subject to (A1) and (A2) of Definition 2.1. -/
class KMonoid (κ : Cardinal.{u}) (H : Type v) extends LMonoid (Order.succ κ) H where
  /-- `κ` is an infinite cardinal. -/
  aleph0_le : ℵ₀ ≤ κ

namespace KMonoid

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

theorem lt_succ {ι : Type u} {κ : Cardinal.{u}} (h : #ι ≤ κ) : #ι < Order.succ κ :=
  Order.lt_succ_iff.mpr h

theorem le_of_lt_succ {ι : Type u} {κ : Cardinal.{u}} (h : #ι < Order.succ κ) : #ι ≤ κ :=
  Order.lt_succ_iff.mp h

theorem isRegular_succ' {H : Type v} [KMonoid κ H] : (Order.succ κ).IsRegular :=
  Cardinal.isRegular_succ (aleph0_le (κ := κ) (H := H))

/-! ### Cardinal bookkeeping at the `κ`-level -/

theorem mk_le_of_finite {H : Type v} [KMonoid κ H] (ι : Type u) [Finite ι] : #ι ≤ κ :=
  le_of_lt_succ (mk_lt_of_finite (isRegular_succ' (H := H)) ι)

theorem mk_uLift_bool_le (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] : #(ULift.{u} Bool) ≤ κ :=
  mk_le_of_finite (H := H) _

theorem mk_sigma_le {H : Type v} [KMonoid κ H] {ι : Type u} {ρ : ι → Type u} (h : #ι ≤ κ)
    (hρ : ∀ i, #(ρ i) ≤ κ) : #((i : ι) × ρ i) ≤ κ :=
  le_of_lt_succ
    (mk_sigma_lt (isRegular_succ' (H := H)) (lt_succ h) fun i => lt_succ (hρ i))

theorem mk_prod_le {H : Type v} [KMonoid κ H] {α β : Type u} (hα : #α ≤ κ) (hβ : #β ≤ κ) :
    #(α × β) ≤ κ :=
  le_of_lt_succ
    (mk_prod_lt (isRegular_succ' (H := H)) (lt_succ hα) (lt_succ hβ))

theorem mk_sum_le {H : Type v} [KMonoid κ H] {α β : Type u} (hα : #α ≤ κ) (hβ : #β ≤ κ) :
    #(α ⊕ β) ≤ κ :=
  le_of_lt_succ
    (mk_sum_lt (isRegular_succ' (H := H)) (lt_succ hα) (lt_succ hβ))

/-! ### Summation -/

/-- The sum of a family indexed by an arbitrary type of cardinality `≤ κ`. -/
noncomputable def sumOf {ι : Type u} (h : #ι ≤ κ) (x : ι → H) : H :=
  LMonoid.lsumOf (lam := Order.succ κ) (lt_succ h) x

theorem sumOf_equiv {ι ι' : Type u} (h : #ι ≤ κ) (h' : #ι' ≤ κ) (e : ι' ≃ ι) (x : ι → H) :
    sumOf (κ := κ) h x = sumOf (κ := κ) h' (x ∘ e) :=
  LMonoid.lsumOf_equiv _ _ e x

@[simp] theorem sumOf_unique {ι : Type u} [Unique ι] (h : #ι ≤ κ) (x : ι → H) :
    sumOf (κ := κ) h x = x default :=
  LMonoid.lsumOf_unique _ x

@[simp] theorem sumOf_of_isEmpty {ι : Type u} [IsEmpty ι] (h : #ι ≤ κ) (x : ι → H) :
    sumOf (κ := κ) h x = 0 :=
  LMonoid.lsumOf_isEmpty _ x

@[simp] theorem sumOf_zero {ι : Type u} (h : #ι ≤ κ) :
    sumOf (κ := κ) (H := H) h (fun _ => 0) = 0 :=
  LMonoid.lsumOf_zero _

/-- The general associativity law: a `κ`-sum may be computed by first summing over the fibres
of a partition. -/
theorem sumOf_sigma {ι : Type u} {ρ : ι → Type u} (h : #ι ≤ κ) (hρ : ∀ i, #(ρ i) ≤ κ)
    (hσ : #((i : ι) × ρ i) ≤ κ) (x : ∀ i, ρ i → H) :
    sumOf (κ := κ) h (fun i => sumOf (κ := κ) (hρ i) (x i))
      = sumOf (κ := κ) hσ (fun p => x p.1 p.2) :=
  LMonoid.lsumOf_sigma _ (fun i => lt_succ (hρ i)) x _

/-- Zero-padding along an embedding does not change a `κ`-sum. -/
theorem sumOf_extend {ι ι' : Type u} (h : #ι ≤ κ) (h' : #ι' ≤ κ) (e : ι ↪ ι') (x : ι → H) :
    sumOf (κ := κ) h' (Function.extend e x 0) = sumOf (κ := κ) h x :=
  LMonoid.lsumOf_extend _ _ e x

/-- A `κ`-sum indexed by (a universe-lifted) `Bool` recovers the binary operation `+`. -/
theorem sumOf_two (a b : H) (hUB : #(ULift.{u} Bool) ≤ κ) :
    sumOf (κ := κ) hUB (fun p : ULift.{u} Bool => if p.down then a else b) = a + b :=
  LMonoid.lsumOf_two a b _

/-- `κ`-sums are additive. -/
theorem sumOf_add {ι : Type u} (h : #ι ≤ κ) (f g : ι → H) :
    sumOf (κ := κ) h (fun i => f i + g i) = sumOf (κ := κ) h f + sumOf (κ := κ) h g :=
  LMonoid.lsumOf_add _ f g

/-- Terms with value `0` may be discarded. -/
theorem sumOf_subtype_support {ι : Type u} (h : #ι ≤ κ) (x : ι → H)
    (h' : #(Function.support x) ≤ κ) :
    sumOf (κ := κ) h x = sumOf (κ := κ) h' (fun i : Function.support x => x i) := by
  classical
  set e : Function.support x ↪ ι := Function.Embedding.subtype _ with hedef
  have hfun : x = Function.extend (⇑e) (fun i : Function.support x => x i) 0 := by
    funext i
    by_cases hi : i ∈ Function.support x
    · have hval : e ⟨i, hi⟩ = i := rfl
      rw [← hval, e.injective.extend_apply]
      rfl
    · rw [Function.extend_apply' (fun i : Function.support x => x i) (0 : ι → H) i ?_]
      · exact not_not.mp hi
      · rintro ⟨t, ht⟩
        exact hi (ht ▸ t.2)
  conv_lhs => rw [hfun]
  exact sumOf_extend h' h e _

/-- A sum over `α ⊕ β` splits as a binary sum. -/
theorem sumOf_sumType {α β : Type u} (hα : #α ≤ κ) (hβ : #β ≤ κ) (hαβ : #(α ⊕ β) ≤ κ)
    (f : α → H) (g : β → H) :
    sumOf (κ := κ) hαβ (Sum.elim f g) = sumOf (κ := κ) hα f + sumOf (κ := κ) hβ g :=
  LMonoid.lsumOf_sumType (lt_succ hα) (lt_succ hβ) (lt_succ hαβ) f g

/-- The special case of `sumOf_sigma` for a partition of the index set into subsets. -/
theorem sumOf_biUnion {ι J : Type u} (I : J → Set ι) (hdisj : ∀ p q, p ≠ q → Disjoint (I p) (I q))
    (hcover : (⋃ p, I p) = Set.univ) (hJ : #J ≤ κ) (hι : #ι ≤ κ) (hI : ∀ p, #(I p) ≤ κ)
    (x : ι → H) :
    sumOf (κ := κ) hJ (fun p => sumOf (κ := κ) (hI p) (fun i : I p => x i))
      = sumOf (κ := κ) hι x := by
  have huniv : #(↥(Set.univ : Set ι)) ≤ κ := (Cardinal.mk_congr (Equiv.Set.univ ι)).trans_le hι
  have hkey := LMonoid.lsumOf_biUnion_subset (X := H) (Set.univ : Set ι) I
    (fun p => Set.subset_univ _) hdisj hcover (lt_succ hJ) (lt_succ huniv)
    (fun p => lt_succ (hI p)) x
  calc sumOf (κ := κ) hJ (fun p => sumOf (κ := κ) (hI p) (fun i : I p => x i))
      = sumOf (κ := κ) huniv (fun i : (Set.univ : Set ι) => x i) := hkey
    _ = sumOf (κ := κ) hι x := (sumOf_equiv hι huniv (Equiv.Set.univ ι) x).symm

/-! ### Summation over the canonical index type `Idx κ` -/

/-- The `κ`-indexed summation `Σ : H^κ → H` of the paper. -/
noncomputable def ksum (x : Idx κ → H) : H := sumOf (κ := κ) (le_of_eq (mk_Idx κ)) x

theorem sumOf_Idx (x : Idx κ → H) : sumOf (κ := κ) (le_of_eq (mk_Idx κ)) x = ksum (κ := κ) x := rfl

/-- A `κ`-sum may be computed by padding with zeros along *any* embedding into `Idx κ`. -/
theorem sumOf_eq_extend {ι : Type u} (h : #ι ≤ κ) (e : ι ↪ Idx κ) (x : ι → H) :
    sumOf (κ := κ) h x = ksum (κ := κ) (Function.extend e x 0) :=
  (sumOf_extend h (le_of_eq (mk_Idx κ)) e x).symm

@[simp] theorem ksum_zero : ksum (κ := κ) (fun _ : Idx κ => (0 : H)) = 0 := sumOf_zero _

/-- (A1): a family concentrated in one index sums to its unique possibly nonzero entry. -/
theorem ksum_single (i₀ : Idx κ) (x : Idx κ → H) (hx : ∀ i, i ≠ i₀ → x i = 0) :
    ksum (κ := κ) x = x i₀ := by
  classical
  have hpt : #PUnit.{u + 1} ≤ κ := mk_le_of_finite (H := H) _
  set e : PUnit.{u + 1} ↪ Idx κ := ⟨fun _ => i₀, fun _ _ _ => rfl⟩ with hedef
  have hfun : x = Function.extend (⇑e) (fun _ : PUnit.{u + 1} => x i₀) 0 := by
    funext i
    by_cases hi : i = i₀
    · have hval : e PUnit.unit = i₀ := rfl
      rw [hi, ← hval, e.injective.extend_apply]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨p, hp⟩; exact hi hp.symm)]
      exact hx i hi
  show sumOf (κ := κ) (le_of_eq (mk_Idx κ)) x = x i₀
  conv_lhs => rw [hfun]
  rw [sumOf_extend hpt (le_of_eq (mk_Idx κ)) e, sumOf_unique]

/-- (A2): the associativity law modelled on `⨁ᵢ ⨁ⱼ Mᵢⱼ ≅ ⨁_{(i,j)} Mᵢⱼ`. -/
theorem ksum_sigma (x : Idx κ → Idx κ → H) (π : Idx κ × Idx κ ≃ Idx κ) :
    ksum (κ := κ) (fun i => ksum (κ := κ) (x i))
      = ksum (κ := κ) fun k => x (π.symm k).1 (π.symm k).2 := by
  have hidx : #(Idx κ) ≤ κ := le_of_eq (mk_Idx κ)
  have hσ : #((_ : Idx κ) × Idx κ) ≤ κ := mk_sigma_le (H := H) hidx fun _ => hidx
  have h1 : ksum (κ := κ) (fun i => ksum (κ := κ) (x i))
      = sumOf (κ := κ) hσ (fun p => x p.1 p.2) := sumOf_sigma hidx (fun _ => hidx) hσ x
  have h2 : sumOf (κ := κ) hσ (fun p => x p.1 p.2)
      = ksum (κ := κ) (fun k => x (π.symm k).1 (π.symm k).2) :=
    sumOf_equiv hσ hidx (π.symm.trans (Equiv.sigmaEquivProd (Idx κ) (Idx κ)).symm) _
  exact h1.trans h2

/-- Compatibility of `+` with `Σ`. -/
theorem ksum_two (a b : H) (i₀ i₁ : Idx κ) (hne : i₀ ≠ i₁) :
    ksum (κ := κ) (fun i => if i = i₀ then a else if i = i₁ then b else 0) = a + b := by
  classical
  have hUB : #(ULift.{u} Bool) ≤ κ := mk_uLift_bool_le κ H
  set e : ULift.{u} Bool ↪ Idx κ := ⟨fun p => if p.down then i₀ else i₁, by
    rintro ⟨(_ | _)⟩ ⟨(_ | _)⟩ h
    · rfl
    · exact absurd h.symm hne
    · exact absurd h hne
    · rfl⟩ with hedef
  have he0 : e ⟨true⟩ = i₀ := rfl
  have he1 : e ⟨false⟩ = i₁ := rfl
  set F : ULift.{u} Bool → H := fun p => if p.down then a else b with hFdef
  have hfun : (fun i => if i = i₀ then a else if i = i₁ then b else 0)
      = Function.extend (⇑e) F 0 := by
    funext i
    by_cases h0 : i = i₀
    · have hval : Function.extend (⇑e) F 0 i = a := by
        rw [h0, ← he0, e.injective.extend_apply]
        simp [hFdef]
      rw [hval, if_pos h0]
    · by_cases h1 : i = i₁
      · have hval : Function.extend (⇑e) F 0 i = b := by
          rw [h1, ← he1, e.injective.extend_apply]
          simp [hFdef]
        rw [hval, if_neg h0, if_pos h1]
      · have hval : Function.extend (⇑e) F 0 i = 0 := by
          apply Function.extend_apply'
          rintro ⟨⟨(_ | _)⟩, hp⟩
          · exact h1 (by rw [← hp, he1])
          · exact h0 (by rw [← hp, he0])
        rw [hval, if_neg h0, if_neg h1]
  show sumOf (κ := κ) (le_of_eq (mk_Idx κ)) _ = a + b
  rw [hfun, sumOf_extend hUB (le_of_eq (mk_Idx κ)) e, sumOf_two a b hUB]

/-- (A3), Lemma 2.5: `Σ` is invariant under permutations of the index set. -/
theorem ksum_perm (x : Idx κ → H) (π : Idx κ ≃ Idx κ) :
    ksum (κ := κ) x = ksum (κ := κ) (x ∘ π) :=
  sumOf_equiv _ _ π x

/-- (A4), Lemma 2.5: iterated sums may be interchanged. -/
theorem ksum_comm (x : Idx κ → Idx κ → H) :
    ksum (κ := κ) (fun i => ksum (κ := κ) (x i))
      = ksum (κ := κ) (fun j => ksum (κ := κ) fun i => x i j) := by
  have hidx : #(Idx κ) ≤ κ := le_of_eq (mk_Idx κ)
  have hσ : #((_ : Idx κ) × Idx κ) ≤ κ := mk_sigma_le (H := H) hidx fun _ => hidx
  have h1 : ksum (κ := κ) (fun i => ksum (κ := κ) (x i))
      = sumOf (κ := κ) hσ (fun p => x p.1 p.2) := sumOf_sigma hidx (fun _ => hidx) hσ x
  have h2 : ksum (κ := κ) (fun j => ksum (κ := κ) fun i => x i j)
      = sumOf (κ := κ) hσ (fun p => x p.2 p.1) :=
    sumOf_sigma hidx (fun _ => hidx) hσ (fun j i => x i j)
  rw [h1, h2]
  exact sumOf_equiv hσ hσ ((Equiv.sigmaEquivProd (Idx κ) (Idx κ)).trans
    ((Equiv.prodComm (Idx κ) (Idx κ)).trans (Equiv.sigmaEquivProd (Idx κ) (Idx κ)).symm)) _

/-- Zero-padding along a self-embedding of `Idx κ` does not change a `κ`-sum. -/
theorem ksum_extend (g : Idx κ ↪ Idx κ) (x : Idx κ → H) :
    ksum (κ := κ) (Function.extend g x 0) = ksum (κ := κ) x :=
  sumOf_extend _ _ g x

end KMonoid

namespace KMonoid

/-! ### Cardinal scalar multiplication (Definition 2.6, Lemma 2.7)

Definition 2.6, Lemma 2.7 and Lemma 2.8 are proved for `λ⁻`-monoids in `LMonoid`; what follows
is the special case `λ = κ⁺`, in which `α < κ⁺` reads `α ≤ κ`. -/

section Cmul

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-- A cardinal is `≤ κ` exactly when it may index a `κ`-sum. -/
theorem lt_succ_of_le {α κ : Cardinal.{u}} (h : α ≤ κ) : α < Order.succ κ := Order.lt_succ_iff.mpr h

/-- `ℵ₀` may index a `κ`-sum. -/
theorem aleph0_lt_succ (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] : ℵ₀ < Order.succ κ :=
  lt_succ_of_le (aleph0_le (κ := κ) (H := H))

/-- `cmul α x` is the sum of `α` many copies of `x` (Definition 2.6). -/
noncomputable def cmul (α : Cardinal.{u}) (hα : α ≤ κ) (x : H) : H :=
  LMonoid.lcmul (lam := Order.succ κ) α (lt_succ_of_le hα) x

theorem cmul_eq_lcmul (α : Cardinal.{u}) (hα : α ≤ κ) (x : H) :
    cmul (κ := κ) α hα x = LMonoid.lcmul (lam := Order.succ κ) α (lt_succ_of_le hα) x := rfl

@[simp] theorem cmul_zero_cardinal (x : H) : cmul (κ := κ) 0 zero_le x = 0 :=
  LMonoid.lcmul_zero_cardinal (lam := Order.succ κ) _ x

/-- Lemma 2.7(1), second half. -/
@[simp] theorem cmul_one (h1 : (1 : Cardinal.{u}) ≤ κ) (x : H) : cmul (κ := κ) 1 h1 x = x :=
  LMonoid.lcmul_one (lam := Order.succ κ) _ x

theorem cmul_congr {α β : Cardinal.{u}} (h : α = β) (hα : α ≤ κ) (hβ : β ≤ κ) (x : H) :
    cmul (κ := κ) α hα x = cmul (κ := κ) β hβ x :=
  LMonoid.lcmul_congr (lam := Order.succ κ) h _ _ x

/-- Lemma 2.7(2). -/
theorem cmul_sumOf_cardinal {I : Type u} (hI : #I ≤ κ) (l : I → Cardinal.{u})
    (hl : ∀ i, l i ≤ κ) (hsum : Cardinal.sum l ≤ κ) (x : H) :
    cmul (κ := κ) (Cardinal.sum l) hsum x
      = sumOf (κ := κ) hI fun i => cmul (κ := κ) (l i) (hl i) x :=
  LMonoid.lcmul_lsumOf_cardinal (lam := Order.succ κ) (lt_succ hI) l
    (fun i => lt_succ_of_le (hl i)) (lt_succ_of_le hsum) x

/-- Lemma 2.7(3). -/
theorem cmul_sumOf {I : Type u} (hI : #I ≤ κ) (α : Cardinal.{u}) (hα : α ≤ κ) (x : I → H) :
    cmul (κ := κ) α hα (sumOf (κ := κ) hI x)
      = sumOf (κ := κ) hI fun i => cmul (κ := κ) α hα (x i) :=
  LMonoid.lcmul_lsumOf (lam := Order.succ κ) (lt_succ hI) α (lt_succ_of_le hα) x

/-- Lemma 2.7(2) for a two-term sum of cardinals. -/
theorem cmul_add {α β : Cardinal.{u}} (hα : α ≤ κ) (hβ : β ≤ κ) (hαβ : α + β ≤ κ) (x : H) :
    cmul (κ := κ) (α + β) hαβ x = cmul (κ := κ) α hα x + cmul (κ := κ) β hβ x :=
  LMonoid.lcmul_add (lam := Order.succ κ) (lt_succ_of_le hα) (lt_succ_of_le hβ)
    (lt_succ_of_le hαβ) x

/-- Any number of copies of `0` is `0`. -/
@[simp] theorem cmul_zero (α : Cardinal.{u}) (hα : α ≤ κ) :
    cmul (κ := κ) α hα (0 : H) = 0 :=
  LMonoid.lcmul_zero (lam := Order.succ κ) (X := H) α _

/-- Lemma 2.7(4): iterated scalar multiplication multiplies the cardinals. -/
theorem cmul_cmul {α β : Cardinal.{u}} (hα : α ≤ κ) (hβ : β ≤ κ) (hαβ : α * β ≤ κ) (x : H) :
    cmul (κ := κ) α hα (cmul (κ := κ) β hβ x) = cmul (κ := κ) (α * β) hαβ x :=
  LMonoid.lcmul_lcmul (lam := Order.succ κ) (lt_succ_of_le hα) (lt_succ_of_le hβ)
    (lt_succ_of_le hαβ) x

/-- `#ι` copies of `x` are the sum of the family constantly equal to `x`, indexed by `ι`. -/
theorem cmul_eq_sumOf {ι : Type u} (hι : #ι ≤ κ) (x : H) :
    cmul (κ := κ) #ι hι x = sumOf (κ := κ) hι (fun _ : ι => x) := by
  obtain ⟨e⟩ := Cardinal.eq.mp (mk_Idx (#ι))
  exact (sumOf_equiv hι (le_of_eq_of_le (mk_Idx (#ι)) hι) e (fun _ : ι => x)).symm

/-- Indices outside a subset off which the family vanishes may be dropped from a sum. -/
theorem sumOf_eq_sumOf_subset {ι : Type u} (hι : #ι ≤ κ) {S : Set ι} (hS : #S ≤ κ) (f : ι → H)
    (hout : ∀ i ∉ S, f i = 0) :
    sumOf (κ := κ) hι f = sumOf (κ := κ) hS (fun i : S => f i) := by
  classical
  have hfun : f = Function.extend (Function.Embedding.subtype (· ∈ S)) (fun i : S => f i) 0 := by
    funext i
    by_cases hi : i ∈ S
    · have hval : (Function.Embedding.subtype (· ∈ S)) ⟨i, hi⟩ = i := rfl
      rw [← hval, (Function.Embedding.subtype (· ∈ S)).injective.extend_apply]
      rfl
    · rw [Function.extend_apply' (fun i : S => f i) (0 : ι → H) i
        (by rintro ⟨t, ht⟩; exact hi (ht ▸ t.2))]
      exact hout i hi
  conv_lhs => rw [hfun]
  exact sumOf_extend hS hι _ (fun i : S => f i)

/-- A family taking the value `x` on `S` and `0` off it sums to `#S · x`. -/
theorem sumOf_indicator {ι : Type u} (hι : #ι ≤ κ) {S : Set ι} (hS : #S ≤ κ) (x : H) (f : ι → H)
    (hin : ∀ i ∈ S, f i = x) (hout : ∀ i ∉ S, f i = 0) :
    sumOf (κ := κ) hι f = cmul (κ := κ) #S hS x := by
  rw [sumOf_eq_sumOf_subset hι hS f hout, cmul_eq_sumOf]
  exact congrArg _ (funext fun i => hin i i.2)

/-- Cardinal scalar multiplication by a natural number is the `nsmul` of the additive monoid. -/
theorem cmul_natCast (x : H) : ∀ n : ℕ,
    cmul (κ := κ) (n : Cardinal.{u}) (le_trans (le_of_lt Cardinal.natCast_lt_aleph0)
      (aleph0_le (κ := κ) (H := H))) x = n • x
  | 0 => by
      rw [cmul_congr (by rw [Nat.cast_zero] : ((0 : ℕ) : Cardinal.{u}) = 0) _ zero_le,
        cmul_zero_cardinal, zero_smul]
  | (n + 1) => by
      have h1 : ((n + 1 : ℕ) : Cardinal.{u}) = (n : Cardinal.{u}) + 1 := by push_cast; ring
      rw [cmul_congr h1 _ (le_trans (le_of_eq h1.symm) (le_trans
        (le_of_lt Cardinal.natCast_lt_aleph0) (aleph0_le (κ := κ) (H := H)))),
        cmul_add (le_trans (le_of_lt Cardinal.natCast_lt_aleph0) (aleph0_le (κ := κ) (H := H)))
          (le_trans (le_of_lt Cardinal.one_lt_aleph0) (aleph0_le (κ := κ) (H := H))),
        cmul_natCast x n, cmul_one, succ_nsmul]

/-! ### Reducedness (Lemma 2.8) -/

/-- `κ`-many copies of `0` sum to `0`. -/
theorem cmul_top_zero (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] :
    cmul (κ := κ) κ le_rfl (0 : H) = 0 :=
  LMonoid.lcmul_zero (lam := Order.succ κ) (X := H) _ _

/-- Scaling by `κ` distributes over `+`. -/
theorem cmul_top_distrib (a b : H) :
    cmul (κ := κ) κ le_rfl (a + b) = cmul (κ := κ) κ le_rfl a + cmul (κ := κ) κ le_rfl b :=
  LMonoid.lcmul_distrib (lam := Order.succ κ) _ a b

/-- The remark after Definition 2.6: for an infinite cardinal `α`, adding one more copy of `z` to
`α`-many copies of `z` does not change the value.  With `α = κ` this is the key idempotence step
of the swindle proving Lemma 2.8(1). -/
theorem add_cmul_self {α : Cardinal.{u}} (hα0 : ℵ₀ ≤ α) (hα : α ≤ κ) (z : H) :
    z + cmul (κ := κ) α hα z = cmul (κ := κ) α hα z :=
  LMonoid.add_lcmul_self (lam := Order.succ κ) hα0 _ z

/-- Lemma 2.8(2), the key idempotence step of the swindle: adding one more copy of `z` to
`κ`-many copies of `z` does not change the value. -/
theorem add_cmul_top_self (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] (z : H) :
    z + cmul (κ := κ) κ le_rfl z = cmul (κ := κ) κ le_rfl z :=
  add_cmul_self (aleph0_le (κ := κ) (H := H)) le_rfl z

/-- Lemma 2.8(1): a variant of the Eilenberg–Mazur swindle shows that every `κ`-monoid is
reduced.  The swindle is run at the `λ⁻` level in `LMonoid.isConical`; here `ℵ₀ ≤ κ < κ⁺`
supplies its hypothesis. -/
theorem isConical (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] : IsConical H :=
  LMonoid.isConical (lam := Order.succ κ) (aleph0_lt_succ κ H)

/-- Applying `cmul κ` twice is the same as applying it once (since `κ * κ = κ`). -/
theorem cmul_top_idem (z : H) :
    cmul (κ := κ) κ le_rfl (cmul (κ := κ) κ le_rfl z) = cmul (κ := κ) κ le_rfl z :=
  LMonoid.lcmul_idem (lam := Order.succ κ) (aleph0_le (κ := κ) (H := H)) _ z

/-- Lemma 2.8(2). -/
theorem add_cmul_top_eq {t₁ t₂ t₃ : H} (h : t₁ + t₂ = cmul (κ := κ) κ le_rfl t₃) :
    t₁ + cmul (κ := κ) κ le_rfl t₃ = cmul (κ := κ) κ le_rfl t₃ :=
  LMonoid.add_lcmul_eq (lam := Order.succ κ) (aleph0_le (κ := κ) (H := H)) _ h

end Cmul

/-! ### Homomorphisms, submonoids and generation (Section 2.1) -/

section Sub

variable {κ : Cardinal.{u}} {H : Type v} [KMonoid κ H]

/-- A homomorphism of `κ`-monoids. -/
def IsKHom (κ : Cardinal.{u}) {H : Type v} {K : Type w} [KMonoid κ H] [KMonoid κ K]
    (f : H → K) : Prop :=
  f 0 = 0 ∧ ∀ x : Idx κ → H, f (ksum (κ := κ) x) = ksum (κ := κ) (f ∘ x)

/-- `κ`-homomorphisms compose.  Stated across three independent universes, which is what
`isUniversalKExtension_unique'` needs: a `have` inside a proof cannot be universe-polymorphic, so
this has to be a lemma. -/
theorem IsKHom.comp {K : Type w} {L : Type t} [KMonoid κ K] [KMonoid κ L] {g : H → K} {h : K → L}
    (hg : IsKHom κ g) (hh : IsKHom κ h) : IsKHom κ (fun a => h (g a)) := by
  refine ⟨by show h (g 0) = 0; rw [hg.1, hh.1], fun x => ?_⟩
  show h (g (ksum (κ := κ) x)) = ksum (κ := κ) (fun i => h (g (x i)))
  rw [hg.2 x, hh.2 (g ∘ x)]
  rfl

/-- The identity is a `κ`-homomorphism. -/
theorem IsKHom.id' : IsKHom κ (fun a : H => a) := ⟨rfl, fun _ => rfl⟩

/-- A `κ`-homomorphism commutes with sums over arbitrary small index types, not just `Idx κ`:
pad along an embedding into `Idx κ` and use that `f 0 = 0`. -/
theorem IsKHom.map_sumOf {K : Type w} [KMonoid κ K] {f : H → K} (hf : IsKHom κ f)
    {ι : Type u} (h : #ι ≤ κ) (x : ι → H) :
    f (sumOf (κ := κ) h x) = sumOf (κ := κ) h (f ∘ x) := by
  classical
  have hext : f ∘ Function.extend (emb h) x 0 = Function.extend (emb h) (f ∘ x) 0 := by
    funext k
    by_cases hk : ∃ i, emb h i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [Function.comp_apply, (emb h).injective.extend_apply, (emb h).injective.extend_apply]
      rfl
    · rw [Function.comp_apply, Function.extend_apply' _ _ _ hk,
        Function.extend_apply' _ _ _ hk]
      exact hf.1
  rw [sumOf_eq_extend h (emb h) x, hf.2, hext, ← sumOf_eq_extend h (emb h) (f ∘ x)]

/-- A `κ`-homomorphism is additive: `a + b` is a `κ`-sum indexed by `Bool`. -/
theorem IsKHom.map_add {K : Type w} [KMonoid κ K] {f : H → K} (hf : IsKHom κ f) (a b : H) :
    f (a + b) = f a + f b := by
  have hUB : #(ULift.{u} Bool) ≤ κ :=
    le_trans (le_of_lt (Cardinal.lt_aleph0_iff_finite.mpr inferInstance))
      (aleph0_le (κ := κ) (H := H))
  rw [← sumOf_two a b hUB, hf.map_sumOf hUB, ← sumOf_two (f a) (f b) hUB]
  exact congrArg _ (funext fun p => by rcases p with ⟨(_ | _)⟩ <;> rfl)

/-- The inverse of a bijective `κ`-homomorphism is again a `κ`-homomorphism. -/
theorem IsKHom.inv {K : Type w} [KMonoid κ K] {f : H → K} (hf : IsKHom κ f)
    (hbij : Function.Bijective f) {g : K → H} (hfg : Function.RightInverse g f) :
    IsKHom κ g := by
  refine ⟨hbij.1 ?_, fun x => hbij.1 ?_⟩
  · rw [hfg 0, hf.1]
  · rw [hfg (ksum (κ := κ) x), hf.2 (g ∘ x)]
    exact congrArg _ (funext fun i => (hfg (x i)).symm)

/-- A `κ`-homomorphism commutes with `cmul`: both sides are the sum of a constant family. -/
theorem IsKHom.map_cmul {K : Type w} [KMonoid κ K] {f : H → K} (hf : IsKHom κ f)
    {α : Cardinal.{u}} (hα : α ≤ κ) (x : H) :
    f (cmul (κ := κ) α hα x) = cmul (κ := κ) α hα (f x) := by
  have hmk : #(Idx α) ≤ κ := le_of_eq_of_le (mk_Idx α) hα
  have h1 : cmul (κ := κ) α hα x = sumOf (κ := κ) hmk (fun _ : Idx α => x) :=
    (cmul_congr (mk_Idx α).symm hα hmk x).trans (cmul_eq_sumOf hmk x)
  have h2 : cmul (κ := κ) α hα (f x) = sumOf (κ := κ) hmk (fun _ : Idx α => f x) :=
    (cmul_congr (mk_Idx α).symm hα hmk (f x)).trans (cmul_eq_sumOf hmk (f x))
  rw [h1, h2, hf.map_sumOf hmk (fun _ : Idx α => x)]
  rfl

/-- A `κ`-submonoid of a `κ`-monoid. -/
structure IsKSubmonoid (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) : Prop where
  zero_mem : (0 : H) ∈ S
  ksum_mem : ∀ x : Idx κ → H, (∀ i, x i ∈ S) → ksum (κ := κ) x ∈ S

/-- A `κ`-submonoid is closed under sums over arbitrary small index types. -/
theorem IsKSubmonoid.sumOf_mem {S : Set H} (hS : IsKSubmonoid κ S) {ι : Type u} (h : #ι ≤ κ)
    (x : ι → H) (hx : ∀ i, x i ∈ S) : sumOf (κ := κ) h x ∈ S := by
  classical
  rw [← sumOf_extend h (le_of_eq (mk_Idx κ)) (emb h) x]
  refine hS.ksum_mem _ fun k => ?_
  by_cases hk : ∃ i, emb h i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [(emb h).injective.extend_apply]
    exact hx i
  · rw [Function.extend_apply' _ _ _ hk]
    exact hS.zero_mem

/-- A `κ`-submonoid is closed under `+`. -/
theorem IsKSubmonoid.add_mem {S : Set H} (hS : IsKSubmonoid κ S) {a b : H} (ha : a ∈ S)
    (hb : b ∈ S) : a + b ∈ S := by
  have hUB := mk_uLift_bool_le κ H
  rw [← sumOf_two a b hUB]
  exact hS.sumOf_mem hUB _ (by rintro ⟨(_ | _)⟩ <;> simpa)

/-- The `κ`-submonoid `⟨S⟩_κ` generated by a subset. -/
def kclosure (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) : Set H :=
  ⋂₀ {T | S ⊆ T ∧ IsKSubmonoid κ T}

theorem subset_kclosure {S : Set H} : S ⊆ kclosure κ S := fun _ hx _ hT => hT.1 hx

/-- The `κ`-closure of a set is a `κ`-submonoid: an intersection of `κ`-submonoids is one. -/
theorem isKSubmonoid_kclosure (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) :
    IsKSubmonoid κ (kclosure κ S) where
  zero_mem := fun _ hT => hT.2.zero_mem
  ksum_mem := fun x hx T hT => hT.2.ksum_mem x fun i => hx i T hT

/-- `⟨S⟩_κ` is the smallest `κ`-submonoid containing `S`. -/
theorem kclosure_le {S T : Set H} (hST : S ⊆ T) (hT : IsKSubmonoid κ T) : kclosure κ S ⊆ T :=
  fun _ hx => hx T ⟨hST, hT⟩

theorem kclosure_mono {S S' : Set H} (h : S ⊆ S') : kclosure κ S ⊆ kclosure κ S' :=
  kclosure_le (h.trans subset_kclosure) (isKSubmonoid_kclosure κ S')

/-- Elements of `⟨S⟩_κ` are exactly the `κ`-sums of families in `S`. -/
theorem mem_kclosure_iff {S : Set H} (h0 : (0 : H) ∈ S) (h : H) :
    h ∈ kclosure κ S ↔ ∃ x : Idx κ → H, (∀ i, x i ∈ S) ∧ h = ksum (κ := κ) x := by
  classical
  have hκ := aleph0_le (κ := κ) (H := H)
  obtain ⟨i₀⟩ := nonempty_Idx hκ
  refine ⟨fun hh => ?_, ?_⟩
  · refine hh {h | ∃ x : Idx κ → H, (∀ i, x i ∈ S) ∧ h = ksum (κ := κ) x} ⟨?_, ?_, ?_⟩
    · intro a ha
      refine ⟨fun i => if i = i₀ then a else 0, fun i => ?_, ?_⟩
      · show (if i = i₀ then a else 0) ∈ S
        by_cases hi : i = i₀
        · rwa [if_pos hi]
        · rwa [if_neg hi]
      · rw [ksum_single i₀ _ fun i hi => if_neg hi, if_pos rfl]
    · exact ⟨fun _ => 0, fun _ => h0, ksum_zero.symm⟩
    · intro y hy
      choose x hxS hxsum using hy
      refine ⟨fun k => x ((pairEquiv hκ).symm k).1 ((pairEquiv hκ).symm k).2, fun k => hxS _ _, ?_⟩
      rw [← ksum_sigma x (pairEquiv hκ)]
      exact congrArg _ (funext hxsum)
  · rintro ⟨x, hxS, rfl⟩
    exact (isKSubmonoid_kclosure κ S).ksum_mem x fun i => subset_kclosure (hxS i)

/-- `H` is generated as a `κ`-monoid by `S`. -/
def KGenerates (κ : Cardinal.{u}) {H : Type v} [KMonoid κ H] (S : Set H) : Prop :=
  kclosure κ S = Set.univ

theorem kGenerates_iff {S : Set H} : KGenerates κ S ↔ ∀ h : H, h ∈ kclosure κ S :=
  ⟨fun hg h => hg ▸ Set.mem_univ h, fun h => Set.eq_univ_of_forall h⟩

/-- The singleton `{0}` is a `κ`-submonoid. -/
theorem isKSubmonoid_zero : IsKSubmonoid κ ({0} : Set H) where
  zero_mem := rfl
  ksum_mem x hx := by
    rw [show x = fun _ => (0 : H) from funext fun i => hx i, ksum_zero]
    rfl

/-- The image of a `κ`-homomorphism is a `κ`-submonoid. -/
theorem isKSubmonoid_range {K : Type w} [KMonoid κ K] {g : H → K} (hg : IsKHom κ g) :
    IsKSubmonoid κ (Set.range g) where
  zero_mem := ⟨0, hg.1⟩
  ksum_mem := by
    classical
    intro x hx
    choose y hy using hx
    exact ⟨ksum (κ := κ) y, (hg.2 y).trans (congrArg _ (funext hy))⟩

/-- A surjective `κ`-homomorphism carries generating sets to generating sets. -/
theorem KGenerates.map {K : Type w} [KMonoid κ K] {g : H → K} (hg : IsKHom κ g)
    (hsurj : Function.Surjective g) {S : Set H} (hS : KGenerates κ S) :
    KGenerates κ (g '' S) := by
  have hT : IsKSubmonoid κ (g ⁻¹' kclosure κ (g '' S)) :=
    { zero_mem := by
        show g 0 ∈ kclosure κ (g '' S)
        rw [hg.1]
        exact (isKSubmonoid_kclosure κ (g '' S)).zero_mem
      ksum_mem := fun x hx => by
        show g (ksum (κ := κ) x) ∈ kclosure κ (g '' S)
        rw [hg.2 x]
        exact (isKSubmonoid_kclosure κ (g '' S)).ksum_mem _ hx }
  have hsub : kclosure κ S ⊆ g ⁻¹' kclosure κ (g '' S) :=
    kclosure_le (fun s hs => subset_kclosure ⟨s, hs, rfl⟩) hT
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  exact hsub (kGenerates_iff.mp hS x)

/-- **Definition 2.10(1)**: `H` is `α`-*generated* as a `κ`-monoid.  The paper defines this by the
existence of a surjective homomorphism `F_κ(B) → H` from the free `κ`-monoid on a basis `B` of
cardinality `α`, and observes that it is equivalent to the existence of a family of at most `α`
generators; that is the form used here.  The two are identified in
`KappaMonoid.isAlphaGenerated_iff`, once `F_κ(B)` is available. -/
def IsAlphaGenerated (κ α : Cardinal.{u}) (H : Type v) [KMonoid κ H] : Prop :=
  ∃ (ι : Type u) (g : ι → H), #ι ≤ α ∧ KGenerates κ (Set.range g)

/-- **Definition 2.10(2)**: `H` is *cyclic*, i.e. `1`-generated. -/
def IsCyclicKMonoid (κ : Cardinal.{u}) (H : Type v) [KMonoid κ H] : Prop :=
  IsAlphaGenerated κ 1 H

theorem IsAlphaGenerated.mono {α β : Cardinal.{u}} (hαβ : α ≤ β)
    (h : IsAlphaGenerated κ α H) : IsAlphaGenerated κ β H :=
  let ⟨ι, g, hι, hgen⟩ := h; ⟨ι, g, hι.trans hαβ, hgen⟩

/-- A `κ`-monoid is cyclic exactly when it is generated by a single element. -/
theorem isCyclicKMonoid_iff : IsCyclicKMonoid κ H ↔ ∃ u : H, KGenerates κ {u} := by
  constructor
  · rintro ⟨ι, g, hι, hgen⟩
    rcases isEmpty_or_nonempty ι with he | hne
    · refine ⟨0, Set.eq_univ_of_forall fun h => ?_⟩
      rw [Set.range_eq_empty g] at hgen
      have h0 : h ∈ ({0} : Set H) :=
        kclosure_le (Set.empty_subset _) isKSubmonoid_zero (kGenerates_iff.mp hgen h)
      rw [Set.mem_singleton_iff] at h0
      subst h0
      exact subset_kclosure rfl
    · obtain ⟨i₀⟩ := hne
      have hsub : Subsingleton ι := Cardinal.le_one_iff_subsingleton.mp hι
      refine ⟨g i₀, ?_⟩
      have hrange : Set.range g = {g i₀} :=
        Set.eq_singleton_iff_unique_mem.mpr ⟨⟨i₀, rfl⟩, by
          rintro v ⟨i, rfl⟩
          rw [Subsingleton.elim i i₀]⟩
      rwa [hrange] at hgen
  · rintro ⟨u, hu⟩
    refine ⟨PUnit.{u + 1}, fun _ => u, le_of_eq (Cardinal.mk_eq_one _), ?_⟩
    rwa [show Set.range (fun _ : PUnit.{u + 1} => u) = {u} from Set.range_const]

end Sub

end KMonoid

end KappaMonoid
