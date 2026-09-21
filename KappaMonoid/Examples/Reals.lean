/-
**Examples 3.3(2)(3)**: the universal `ℵ₀`-extension `H = ℝ≥0 ∪ ℝ̃>0 ∪ {∞}` of `ℝ≥0`, a second
copy of the positive reals recording that a sum was reached only with infinite support, and the
same construction over `ℚ≥0`.
-/
import KappaMonoid.Examples.NNReal

universe u v

open Cardinal Function Set
open scoped ENNReal NNReal Classical

namespace KappaMonoid

open KMonoid LMonoid

/-! ## Examples 3.3(2): the `ℵ₀`-monoid `H = ℝ≥0 ∪ ℝ̃>0 ∪ {∞}`

The paper's construction.  An element is a value in `ℝ≥0∞` together with a tilde flag, where only a
value that is neither `0` nor `∞` may carry the flag — so there is exactly one `0` and one `∞`, as
required.  The `ℵ₀`-sum of a family is the series sum of the values, marked with a tilde unless the
family is plain and finitely supported: the flag records that the sum was reached only with
infinite support, or from a tilded summand. -/

/-- The carrier `H = ℝ≥0 ∪ ℝ̃>0 ∪ {∞}` of Examples 3.3(2). -/
def RTilde : Type := {p : ℝ≥0∞ × Bool // p.2 = true → p.1 ≠ 0 ∧ p.1 ≠ ⊤}

namespace RTilde

/-- The underlying value in `ℝ≥0∞`. -/
def val (h : RTilde) : ℝ≥0∞ := h.1.1

/-- Whether the element lies in the tilde copy `ℝ̃>0`. -/
def tilded (h : RTilde) : Bool := h.1.2

theorem ext {h h' : RTilde} (hv : h.val = h'.val) (ht : h.tilded = h'.tilded) : h = h' :=
  Subtype.ext (Prod.ext hv ht)

theorem val_ne_zero {h : RTilde} (ht : h.tilded = true) : h.val ≠ 0 := (h.2 ht).1

theorem val_ne_top {h : RTilde} (ht : h.tilded = true) : h.val ≠ ⊤ := (h.2 ht).2

/-- The plain copy of `ℝ≥0`. -/
def ofReal (a : ℝ≥0) : RTilde := ⟨(a, false), by simp⟩

/-- The tilde copy of `ℝ>0`. -/
def tilde (a : ℝ≥0) (ha : a ≠ 0) : RTilde :=
  ⟨(a, true), fun _ => ⟨by simpa using ha, ENNReal.coe_ne_top⟩⟩

/-- The element `∞`. -/
def top : RTilde := ⟨(⊤, false), by simp⟩

instance : Zero RTilde := ⟨ofReal 0⟩

@[simp] theorem val_ofReal (a : ℝ≥0) : (ofReal a).val = (a : ℝ≥0∞) := rfl

@[simp] theorem tilded_ofReal (a : ℝ≥0) : (ofReal a).tilded = false := rfl

@[simp] theorem val_tilde (a : ℝ≥0) (ha : a ≠ 0) : (tilde a ha).val = (a : ℝ≥0∞) := rfl

@[simp] theorem tilded_tilde (a : ℝ≥0) (ha : a ≠ 0) : (tilde a ha).tilded = true := rfl

@[simp] theorem val_top : (top : RTilde).val = ⊤ := rfl

@[simp] theorem tilded_top : (top : RTilde).tilded = false := rfl

@[simp] theorem val_zero : (0 : RTilde).val = 0 := rfl

@[simp] theorem tilded_zero : (0 : RTilde).tilded = false := rfl

/-- The tilde copy omits `0`, so `0` is the only element of value `0`. -/
theorem eq_zero_of_val_eq_zero {h : RTilde} (hv : h.val = 0) : h = 0 := by
  refine ext hv ?_
  cases ht : h.tilded with
  | false => rfl
  | true => exact absurd hv (val_ne_zero ht)

theorem val_eq_zero_iff {h : RTilde} : h.val = 0 ↔ h = 0 :=
  ⟨eq_zero_of_val_eq_zero, fun h => by rw [h, val_zero]⟩

/-- There is only one element of value `∞`. -/
theorem eq_top_of_val_eq_top {h : RTilde} (hv : h.val = ⊤) : h = top := by
  refine ext hv ?_
  cases ht : h.tilded with
  | false => rfl
  | true => exact absurd hv (val_ne_top ht)

/-- Equality of the flags follows from their equality as propositions. -/
theorem tilded_eq_of_iff {h h' : RTilde} (hiff : h.tilded = false ↔ h'.tilded = false) :
    h.tilded = h'.tilded := by
  cases hh : h.tilded <;> cases hh' : h'.tilded <;> simp_all

/-! ### The summation -/

/-- A family stays in the plain copy exactly when every entry does and only finitely many entries
are nonzero. -/
def IsPlain {ι : Type u} (x : ι → RTilde) : Prop :=
  (∀ i, (x i).tilded = false) ∧ (Function.support x).Finite

/-- If a family is not plain, then some entry — a tilded one, or one of the infinitely many nonzero
ones — has nonzero value, so the total is nonzero. -/
theorem tsum_val_ne_zero {ι : Type u} {x : ι → RTilde} (hpl : ¬ IsPlain x) :
    (∑' i, (x i).val) ≠ 0 := by
  intro h0
  have hz : ∀ i, x i = 0 := fun i => eq_zero_of_val_eq_zero (ENNReal.tsum_eq_zero.mp h0 i)
  refine hpl ⟨fun i => by rw [hz i, tilded_zero], ?_⟩
  have hsupp : Function.support x = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun i hi => hi (hz i)
  rw [hsupp]
  exact Set.finite_empty

/-- The tilde flag of an `ℵ₀`-sum: set unless the total is `∞` — where the answer is the single
element `∞` — or the family is plain and finitely supported. -/
noncomputable def sigmaFlag {ι : Type u} (x : ι → RTilde) : Bool :=
  if (∑' i, (x i).val) = ⊤ ∨ IsPlain x then false else true

theorem sigmaFlag_eq_false_iff {ι : Type u} (x : ι → RTilde) :
    sigmaFlag x = false ↔ ((∑' i, (x i).val) = ⊤ ∨ IsPlain x) := by
  unfold sigmaFlag
  by_cases h : (∑' i, (x i).val) = ⊤ ∨ IsPlain x
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun hc => absurd hc (by simp), fun hc => absurd hc h⟩

/-- The `ℵ₀`-summation of `H`: the series sum of the values, tilded unless the family is plain and
finitely supported. -/
noncomputable def sigma {ι : Type u} (x : ι → RTilde) : RTilde :=
  ⟨(∑' i, (x i).val, sigmaFlag x), fun ht => by
    have ht' : sigmaFlag x = true := ht
    have h := (sigmaFlag_eq_false_iff x).not.mp (by simp [ht'])
    exact ⟨tsum_val_ne_zero fun hp => h (Or.inr hp), fun hc => h (Or.inl hc)⟩⟩

@[simp] theorem val_sigma {ι : Type u} (x : ι → RTilde) : (sigma x).val = ∑' i, (x i).val := rfl

@[simp] theorem tilded_sigma {ι : Type u} (x : ι → RTilde) : (sigma x).tilded = sigmaFlag x := rfl

/-- The result is plain exactly when the family was, the case of an infinite total aside. -/
theorem tilded_sigma_eq_false_iff {ι : Type u} (x : ι → RTilde) :
    (sigma x).tilded = false ↔ ((∑' i, (x i).val) = ⊤ ∨ IsPlain x) :=
  sigmaFlag_eq_false_iff x

/-- A family whose values sum to `∞` sums to `∞`. -/
theorem sigma_of_val_eq_top {ι : Type u} {x : ι → RTilde} (htop : (∑' i, (x i).val) = ⊤) :
    sigma x = top := by
  refine ext (by rw [val_sigma, htop, val_top]) ?_
  rw [tilded_top]
  exact (tilded_sigma_eq_false_iff x).mpr (Or.inl htop)

theorem sigma_eq_zero_iff {ι : Type u} (x : ι → RTilde) : sigma x = 0 ↔ ∀ i, x i = 0 := by
  rw [← val_eq_zero_iff, val_sigma, ENNReal.tsum_eq_zero]
  exact ⟨fun h i => eq_zero_of_val_eq_zero (h i), fun h i => by rw [h i, val_zero]⟩

/-! ### The three axioms -/

theorem sigma_comp_equiv {ι ι' : Type u} (e : ι ≃ ι') (x : ι' → RTilde) :
    sigma (x ∘ e) = sigma x := by
  have hval : (∑' i, ((x ∘ e) i).val) = ∑' i', (x i').val := e.tsum_eq fun i' => (x i').val
  have hsupp : Function.support (x ∘ e) = e ⁻¹' Function.support x := rfl
  have hpl : IsPlain (x ∘ e) ↔ IsPlain x := by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i' => by rw [← e.apply_symm_apply i']; exact h1 (e.symm i'), ?_⟩
      rw [← Set.image_preimage_eq (Function.support x) e.surjective, ← hsupp]
      exact h2.image _
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => h1 (e i), ?_⟩
      rw [hsupp]
      exact h2.preimage e.injective.injOn
  refine ext (by rw [val_sigma, val_sigma, hval]) (tilded_eq_of_iff ?_)
  rw [tilded_sigma_eq_false_iff, tilded_sigma_eq_false_iff, hval]
  exact or_congr Iff.rfl hpl

theorem sigma_unique {ι : Type u} [Unique ι] (x : ι → RTilde) : sigma x = x default := by
  have hval : (∑' i, (x i).val) = (x default).val :=
    tsum_eq_single default fun i hi => absurd (Unique.eq_default i) hi
  refine ext (by rw [val_sigma, hval]) (tilded_eq_of_iff ?_)
  rw [tilded_sigma_eq_false_iff, hval]
  constructor
  · rintro (htop | ⟨h1, _⟩)
    · cases ht : (x default).tilded with
      | false => rfl
      | true => exact absurd htop (val_ne_top ht)
    · exact h1 default
  · intro hd
    refine Or.inr ⟨fun i => by rw [Unique.eq_default i]; exact hd, ?_⟩
    exact Set.toFinite _

/-- The row sums of a family with finite total are themselves finite. -/
theorem tsum_row_ne_top {ι : Type u} {ρ : ι → Type u} (x : ∀ i, ρ i → RTilde)
    (htop : (∑' p : (i : ι) × ρ i, (x p.1 p.2).val) ≠ ⊤) (i : ι) :
    (∑' j, (x i j).val) ≠ ⊤ := by
  refine fun hrow => htop ?_
  have hle : (∑' j, (x i j).val) ≤ ∑' i', ∑' j, (x i' j).val :=
    ENNReal.le_tsum i
  rw [← ENNReal.tsum_sigma fun i j => (x i j).val] at hle
  exact top_unique (hrow ▸ hle)

/-- The key compatibility: for a family with finite total, the family of row sums is plain exactly
when the whole double family is.  This is what makes the marking of `sigma` associative. -/
theorem isPlain_sigma_iff {ι : Type u} {ρ : ι → Type u} (x : ∀ i, ρ i → RTilde)
    (htop : (∑' p : (i : ι) × ρ i, (x p.1 p.2).val) ≠ ⊤) :
    IsPlain (fun i => sigma (x i)) ↔ IsPlain (fun p : (i : ι) × ρ i => x p.1 p.2) := by
  classical
  have hrow : ∀ i, (∑' j, (x i j).val) ≠ ⊤ := tsum_row_ne_top x htop
  have hrowpl : ∀ i, (sigma (x i)).tilded = false ↔ IsPlain (x i) := by
    intro i
    rw [tilded_sigma_eq_false_iff]
    exact ⟨fun h => h.elim (fun hc => absurd hc (hrow i)) id, Or.inr⟩
  constructor
  · rintro ⟨h1, h2⟩
    have hrowpl' : ∀ i, IsPlain (x i) := fun i => (hrowpl i).mp (h1 i)
    refine ⟨fun p => (hrowpl' p.1).1 p.2, ?_⟩
    refine Set.Finite.subset (Set.Finite.biUnion h2 fun i _ =>
      ((hrowpl' i).2.image (fun j : ρ i => (⟨i, j⟩ : (i : ι) × ρ i)))) ?_
    rintro ⟨i, j⟩ hij
    refine Set.mem_biUnion (show i ∈ Function.support fun i => sigma (x i) from ?_) ⟨j, hij, rfl⟩
    intro hcon
    exact hij ((sigma_eq_zero_iff (x i)).mp hcon j)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (hrowpl i).mpr ⟨fun j => h1 ⟨i, j⟩, ?_⟩, ?_⟩
    · refine Set.Finite.of_finite_image (f := fun j : ρ i => (⟨i, j⟩ : (i : ι) × ρ i)) ?_ ?_
      · refine Set.Finite.subset h2 ?_
        rintro _ ⟨j, hj, rfl⟩
        exact hj
      · exact Set.injOn_of_injective fun a b hab => by simpa using hab
    · refine Set.Finite.subset (h2.image Sigma.fst) ?_
      intro i hi
      obtain ⟨j, hj⟩ := not_forall.mp (fun hc => hi ((sigma_eq_zero_iff (x i)).mpr hc))
      exact ⟨⟨i, j⟩, hj, rfl⟩

theorem sigma_sigma {ι : Type u} {ρ : ι → Type u} (x : ∀ i, ρ i → RTilde) :
    sigma (fun i => sigma (x i)) = sigma (fun p : (i : ι) × ρ i => x p.1 p.2) := by
  have hvals : (∑' i, (sigma (x i)).val) = ∑' p : (i : ι) × ρ i, (x p.1 p.2).val := by
    rw [tsum_congr fun i => val_sigma (x i)]
    exact (ENNReal.tsum_sigma fun i j => (x i j).val).symm
  refine ext (by rw [val_sigma, val_sigma, hvals]) (tilded_eq_of_iff ?_)
  rw [tilded_sigma_eq_false_iff, tilded_sigma_eq_false_iff, hvals]
  by_cases htop : (∑' p : (i : ι) × ρ i, (x p.1 p.2).val) = ⊤
  · simp [htop]
  · exact or_congr Iff.rfl (isPlain_sigma_iff x htop)

/-! ### `H` as an `ℵ₀`-monoid -/

/-- `Σ` on `H`. -/
noncomputable def sumData : SumData (Order.succ (ℵ₀ : Cardinal.{u})) RTilde where
  isRegular := Cardinal.isRegular_succ le_rfl
  sum _ x := sigma x
  sum_congr _ _ e x := sigma_comp_equiv e x
  sum_unique := fun {_ι} _ _ x => sigma_unique x
  sum_sigma _ _ x _ := sigma_sigma x

theorem sumData_zero :
    (sumData : SumData (Order.succ (ℵ₀ : Cardinal.{u})) RTilde).zero = 0 := by
  show sigma (PEmpty.elim : PEmpty.{u + 1} → RTilde) = 0
  refine (sigma_eq_zero_iff _).mpr fun i => i.elim

/-- **Examples 3.3(2)**: `H = ℝ≥0 ∪ ℝ̃>0 ∪ {∞}` is an `ℵ₀`-monoid. -/
@[instance_reducible]
noncomputable def instKMonoid : KMonoid (ℵ₀ : Cardinal.{u}) RTilde where
  toLMonoid := sumData.toLMonoidOfZero sumData_zero
  aleph0_le := le_rfl

/-- The `ℵ₀`-sum of `H` is `sigma`. -/
@[simp] theorem instKMonoid_sumOf {ι : Type u} (h : #ι ≤ (ℵ₀ : Cardinal.{u})) (x : ι → RTilde) :
    letI := instKMonoid
    KMonoid.sumOf (κ := (ℵ₀ : Cardinal.{u})) h x = sigma x := rfl

/-- Addition on `H` adds the values. -/
theorem val_add (a b : RTilde) :
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
    (a + b).val = a.val + b.val := by
  let : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
  show (sigma (Sum.elim (fun _ : PUnit.{u + 1} => a) (fun _ : PUnit.{u + 1} => b))).val = _
  rw [val_sigma, tsum_fintype]
  simp

/-- `H` is reduced. -/
theorem isConical :
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
    IsConical RTilde := by
  let : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
  intro a b hab
  have hval : a.val + b.val = 0 := by
    rw [← val_add a b, hab, val_zero]
  obtain ⟨h1, h2⟩ := add_eq_zero.mp hval
  exact ⟨eq_zero_of_val_eq_zero h1, eq_zero_of_val_eq_zero h2⟩

/-! ### `H` is `ℵ₀⁻`-braided over `ℝ≥0` -/

theorem support_ofReal_comp {ι : Type u} (x : ι → ℝ≥0) :
    Function.support (fun i => ofReal (x i)) = Function.support x := by
  ext i
  simp only [Function.mem_support, ne_eq, ← val_eq_zero_iff, val_ofReal]
  exact ⟨fun h hc => h (by rw [hc]; rfl), fun h hc => h (by exact_mod_cast hc)⟩

theorem tsum_val_ofReal_comp {ι : Type u} (x : ι → ℝ≥0) :
    (∑' i, (ofReal (x i)).val) = esum x := rfl

theorem isPlain_ofReal_comp_iff {ι : Type u} (x : ι → ℝ≥0) :
    IsPlain (fun i => ofReal (x i)) ↔ (Function.support x).Finite := by
  rw [IsPlain, support_ofReal_comp]
  exact ⟨fun h => h.2, fun h => ⟨fun _ => rfl, h⟩⟩

/-- The `ℵ₀`-sum of a family from the plain copy: its value is the series sum, and it is tilded
exactly when the family is not finitely supported (the total being finite). -/
theorem sigma_ofReal_comp {ι : Type u} (x : ι → ℝ≥0) :
    (sigma fun i => ofReal (x i)).val = esum x ∧
      ((sigma fun i => ofReal (x i)).tilded = false ↔
        (esum x = ⊤ ∨ (Function.support x).Finite)) := by
  refine ⟨rfl, ?_⟩
  rw [tilded_sigma_eq_false_iff, tsum_val_ofReal_comp, isPlain_ofReal_comp_iff]

/-- **Examples 3.3(2)**: `H = ℝ≥0 ∪ ℝ̃>0 ∪ {∞}` is `ℵ₀⁻`-braided over `ℝ≥0`, along the inclusion of
the plain copy.

The three generation cases are the paper's three kinds of element: a plain `a` is a one-term sum,
a tilded `ã` is the sum of a geometric family with sum `a` — which has infinite support, hence gets
the tilde — and `∞` is the sum of infinitely many `1`s.  Braidedness is the classification
`isBraided_nnreal_iff`: equal `ℵ₀`-sums in `H` say exactly that the series sums agree *and* that
the two families are simultaneously finitely supported. -/
theorem isBraidedOver_rtilde :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
    IsBraidedOver (ℵ₀ : Cardinal.{u}) ℵ₀ ℝ≥0 RTilde le_rfl ofReal := by
  let := LMonoid.ofAddCommMonoid ℝ≥0
  let : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
  classical
  -- a countable index type for the two infinite constructions
  have hUL : #(ULift.{u} ℕ) = #(Idx (ℵ₀ : Cardinal.{u})) := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0, mk_Idx]
  obtain ⟨e0⟩ := Cardinal.eq.mp hUL
  set e : ℕ ≃ Idx (ℵ₀ : Cardinal.{u}) := Equiv.ulift.symm.trans e0 with hedef
  refine ⟨⟨rfl, fun {ι} h x => ?_⟩, fun a b hab => ?_, fun h => ?_, fun x y hxy => ?_⟩
  · -- the inclusion is an `ℵ₀⁻`-homomorphism
    have : Finite ι := Cardinal.lt_aleph0_iff_finite.mp h
    have : Fintype ι := Fintype.ofFinite ι
    have hfin : (Function.support x).Finite := Set.toFinite _
    have hgoal : ofReal (lsumOf (lam := (ℵ₀ : Cardinal.{u})) h x)
        = sigma (fun i => ofReal (x i)) := by
      refine ext ?_ ?_
      · rw [val_ofReal, val_sigma, tsum_val_ofReal_comp, esum, tsum_fintype,
          LMonoid.lsumOf_aleph0_eq_finsum h x]
        push_cast
        rfl
      · rw [tilded_ofReal]
        exact ((sigma_ofReal_comp x).2.mpr (Or.inr hfin)).symm
    exact hgoal
  · -- injectivity
    have hv := congrArg val hab
    rw [val_ofReal, val_ofReal] at hv
    exact_mod_cast hv
  · -- `ℝ≥0` generates `H`
    by_cases htop : h.val = ⊤
    · -- `∞` is the sum of infinitely many `1`s
      refine ⟨fun _ => 1, ?_⟩
      rw [eq_top_of_val_eq_top htop]
      refine (sigma_of_val_eq_top ?_).symm
      have : Infinite (Idx (ℵ₀ : Cardinal.{u})) := infinite_Idx le_rfl
      show (∑' _ : Idx (ℵ₀ : Cardinal.{u}), ((1 : ℝ≥0) : ℝ≥0∞)) = ⊤
      simp
    · -- a finite value: one term if plain, a geometric family if tilded
      set a : ℝ≥0 := h.val.toNNReal with hadef
      have ha : ((a : ℝ≥0) : ℝ≥0∞) = h.val := ENNReal.coe_toNNReal htop
      cases hfl : h.tilded with
      | false =>
          obtain ⟨i₀⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{u}))
          refine ⟨fun i => if i = i₀ then a else 0, ?_⟩
          have hks : (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{u}))
              fun i => ofReal (if i = i₀ then a else 0)) = ofReal a := by
            rw [KMonoid.ksum_single i₀ _ fun i hi => by rw [if_neg hi]; rfl, if_pos rfl]
          have hval : ofReal a = h :=
            ext (by rw [val_ofReal]; exact ha) (by rw [tilded_ofReal, hfl])
          exact (hks.trans hval).symm
      | true =>
          have ha0 : a ≠ 0 := by
            intro hc
            refine val_ne_zero hfl ?_
            rw [← ha, hc]
            simp
          refine ⟨fun i => geomTo a (e.symm i), ?_⟩
          have hesum : esum (fun i => geomTo a (e.symm i)) = h.val := by
            rw [show esum (fun i => geomTo a (e.symm i)) = esum (geomTo a) from
              esum_comp_equiv e.symm (geomTo a), esum_geomTo, ha]
          have hinf : ¬ (Function.support fun i => geomTo a (e.symm i)).Finite :=
            infinite_support_comp_equiv e (infinite_support_geomTo ha0)
          rw [show (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{u}))
              fun i => ofReal (geomTo a (e.symm i)))
            = sigma (fun i => ofReal (geomTo a (e.symm i))) from rfl]
          refine (ext ?_ ?_).symm
          · rw [val_sigma, tsum_val_ofReal_comp, hesum]
          · rw [hfl]
            cases hs : (sigma fun i => ofReal (geomTo a (e.symm i))).tilded with
            | false =>
                rcases (sigma_ofReal_comp _).2.mp hs with hc | hc
                · rw [hesum] at hc
                  exact absurd hc htop
                · exact absurd hc hinf
            | true => rfl
  · -- families with equal `ℵ₀`-sums are braided
    have hxy' : sigma (fun i => ofReal (x i)) = sigma (fun i => ofReal (y i)) := hxy
    have hval : esum x = esum y := by
      have hv := congrArg val hxy'
      rw [val_sigma, val_sigma, tsum_val_ofReal_comp, tsum_val_ofReal_comp] at hv
      exact hv
    refine (isBraided_nnreal_iff (le_of_eq (mk_Idx _)) x y).mpr ⟨hval, ?_⟩
    have hfl := congrArg tilded hxy'
    by_cases htop : esum x = ⊤
    · -- neither family can be finitely supported
      exact ⟨fun hc => absurd htop (esum_ne_top_of_finite_support hc),
        fun hc => absurd (hval ▸ htop : esum y = ⊤) (esum_ne_top_of_finite_support hc)⟩
    · -- otherwise the flags read off finiteness of the supports
      have hx := (sigma_ofReal_comp x).2
      have hy := (sigma_ofReal_comp y).2
      constructor
      · intro hc
        rcases hy.mp (hfl ▸ hx.mpr (Or.inr hc)) with hcc | hcc
        · exact absurd (hval.trans hcc) htop
        · exact hcc
      · intro hc
        rcases hx.mp (hfl.symm ▸ hy.mpr (Or.inr hc)) with hcc | hcc
        · exact absurd hcc htop
        · exact hcc

/-- **Examples 3.13** for `ℝ≥0`: by Theorem 3.12(2) the universal `ℵ₀`-extension of `ℝ≥0` is
`ℝ≥0 ∪ ℝ̃>0 ∪ {∞}`. -/
theorem isUniversalKExtension_rtilde :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
    IsUniversalKExtension (ℵ₀ : Cardinal.{u}) ℵ₀ ℝ≥0 RTilde le_rfl ofReal := by
  let := LMonoid.ofAddCommMonoid ℝ≥0
  let : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := instKMonoid
  exact isBraidedOver_rtilde.isUniversalKExtension le_rfl

/-! ### `H` is not `ℵ₀⁻`-braided over itself

The paper's last remark in Examples 3.3(2): repeat the argument that defeated `ℝ≥0 ∪ {∞}`, with
`{0} ∪ ℝ̃>0` in place of `ℝ≥0`.  A single tilded `2̃` and a tilded geometric family have the same
`ℵ₀`-sum `2̃`, but one has finite and the other infinite support, so they are not braided. -/

theorem tilde_ne_zero (a : ℝ≥0) (ha : a ≠ 0) : tilde a ha ≠ 0 := by
  intro hc
  exact val_ne_zero (tilded_tilde a ha) (by rw [hc, val_zero])

/-- **Examples 3.3(2)**, last claim: `H` is not `ℵ₀⁻`-braided over itself — there are two families
in `H` with the same `ℵ₀`-sum that are not `ℵ₀⁻`-braided. -/
theorem not_isBraidedOver_rtilde_self :
    letI : KMonoid (ℵ₀ : Cardinal.{0}) RTilde := instKMonoid
    letI := KMonoid.toLMonoidOfLE RTilde Cardinal.isRegular_aleph0 (le_refl (ℵ₀ : Cardinal.{0}))
    ¬ IsBraidedOver (ℵ₀ : Cardinal.{0}) ℵ₀ RTilde RTilde le_rfl id := by
  let : KMonoid (ℵ₀ : Cardinal.{0}) RTilde := instKMonoid
  let := KMonoid.toLMonoidOfLE RTilde Cardinal.isRegular_aleph0 (le_refl (ℵ₀ : Cardinal.{0}))
  intro hbr
  classical
  -- a countable index type
  have hUL : #(ULift.{0} ℕ) = #(Idx (ℵ₀ : Cardinal.{0})) := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0, mk_Idx]
  obtain ⟨e0⟩ := Cardinal.eq.mp hUL
  set e : ℕ ≃ Idx (ℵ₀ : Cardinal.{0}) := Equiv.ulift.symm.trans e0 with hedef
  obtain ⟨i₀⟩ := nonempty_Idx (le_refl (ℵ₀ : Cardinal.{0}))
  have h2 : (2 : ℝ≥0) ≠ 0 := two_ne_zero
  -- the single tilded `2̃`, and the tilded geometric family
  set X : Idx (ℵ₀ : Cardinal.{0}) → RTilde :=
    fun i => if i = i₀ then tilde 2 h2 else 0 with hXdef
  set Y : Idx (ℵ₀ : Cardinal.{0}) → RTilde :=
    fun i => tilde (geom (e.symm i)) (geom_ne_zero _) with hYdef
  -- both have `ℵ₀`-sum `2̃`
  have hXsum : KMonoid.ksum (κ := (ℵ₀ : Cardinal.{0})) X = tilde 2 h2 := by
    rw [hXdef, KMonoid.ksum_single i₀ _ fun i hi => if_neg hi, if_pos rfl]
  have hYsum : KMonoid.ksum (κ := (ℵ₀ : Cardinal.{0})) Y = tilde 2 h2 := by
    have hks : (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{0})) Y) = sigma Y := rfl
    have hval : (∑' i, (Y i).val) = 2 := by
      rw [hYdef]
      show (∑' i, ((geom (e.symm i) : ℝ≥0) : ℝ≥0∞)) = 2
      rw [show (∑' i, ((geom (e.symm i) : ℝ≥0) : ℝ≥0∞)) = esum (geom ∘ e.symm) from rfl,
        esum_comp_equiv e.symm geom, esum_geom]
    rw [hks]
    refine ext ?_ ?_
    · rw [val_sigma, hval, val_tilde]
      norm_num
    · rw [tilded_tilde]
      cases hs : (sigma Y).tilded with
      | false =>
          rcases (tilded_sigma_eq_false_iff Y).mp hs with hc | hc
          · rw [hval] at hc
            exact absurd hc (by norm_num)
          · exact absurd (hc.1 i₀) (by rw [hYdef, tilded_tilde]; simp)
      | true => rfl
  -- so they are braided over `H`, which contradicts their support behaviour
  have hbraid := hbr.braided X Y (by exact hXsum.trans hYsum.symm)
  have hXfin : #(Function.support X) < (ℵ₀ : Cardinal.{0}) := by
    refine Cardinal.lt_aleph0_iff_set_finite.mpr (Set.Finite.subset (Set.finite_singleton i₀) ?_)
    intro i hi
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact hi (by rw [hXdef]; exact if_neg hne)
  have hYinf : ¬ #(Function.support Y) < (ℵ₀ : Cardinal.{0}) := by
    intro hc
    have hfin := Cardinal.lt_aleph0_iff_set_finite.mp hc
    have huniv : Function.support Y = Set.univ :=
      Set.eq_univ_of_forall fun i => by
        rw [hYdef]
        exact tilde_ne_zero _ _
    rw [huniv] at hfin
    have : Infinite (Idx (ℵ₀ : Cardinal.{0})) := infinite_Idx le_rfl
    exact Set.infinite_univ hfin
  exact hYinf (hbraid.mk_support_lt (lam := (ℵ₀ : Cardinal.{0})) isConical hXfin)

end RTilde

/-! ## Examples 3.3(3): the same construction over `ℚ≥0`

`ℚ≥0` is a *saturated* `ℵ₀⁻`-submonoid of `ℝ≥0` — the complement of a rational in a rational is
rational — so Lemma 3.14(2) applies at `λ = ℵ₀` and identifies the universal `ℵ₀`-extension of
`ℚ≥0` as the `ℵ₀`-submonoid of `H` generated by `ℚ≥0`, with no need to redo the braiding
construction.  Being an `ℵ₀`-sum of rationals constrains only the *plain* part: a plain irrational
is not such a sum (`ofReal_notMem_kclosure_of_not_mem_ratSet`), which is the paper's remark that the
irrationals occur in only one copy — the tilded one. -/

/-- The nonnegative rationals inside `ℝ≥0`. -/
def ratSet : Set ℝ≥0 := {a | ∃ q : ℚ, (q : ℝ) = (a : ℝ)}

theorem zero_mem_ratSet : (0 : ℝ≥0) ∈ ratSet := ⟨0, by simp⟩

theorem add_mem_ratSet {a b : ℝ≥0} (ha : a ∈ ratSet) (hb : b ∈ ratSet) : a + b ∈ ratSet := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  refine ⟨p + q, ?_⟩
  rw [NNReal.coe_add, ← hp, ← hq]
  push_cast
  ring

theorem mul_mem_ratSet {a b : ℝ≥0} (ha : a ∈ ratSet) (hb : b ∈ ratSet) : a * b ∈ ratSet := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  refine ⟨p * q, ?_⟩
  rw [NNReal.coe_mul, ← hp, ← hq]
  push_cast
  ring

theorem inv_two_mem_ratSet : (2⁻¹ : ℝ≥0) ∈ ratSet := ⟨2⁻¹, by norm_num⟩

theorem pow_mem_ratSet {a : ℝ≥0} (ha : a ∈ ratSet) (n : ℕ) : a ^ n ∈ ratSet := by
  induction n with
  | zero => exact ⟨1, by norm_num⟩
  | succ n ih => rw [pow_succ]; exact mul_mem_ratSet ih ha

/-- The rationals as an additive submonoid of `ℝ≥0`, for summing over finsets. -/
def ratSubmonoid : AddSubmonoid ℝ≥0 where
  carrier := ratSet
  zero_mem' := zero_mem_ratSet
  add_mem' := add_mem_ratSet

theorem isLSubmonoid_ratSet :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    IsLSubmonoid (ℵ₀ : Cardinal.{u}) ratSet := by
  let := LMonoid.ofAddCommMonoid ℝ≥0
  refine ⟨zero_mem_ratSet, fun {ι} h x hx => ?_⟩
  have : Finite ι := Cardinal.lt_aleph0_iff_finite.mp h
  have : Fintype ι := Fintype.ofFinite ι
  rw [LMonoid.lsumOf_aleph0_eq_finsum h x]
  exact ratSubmonoid.sum_mem fun i _ => hx i

/-- **`ℚ≥0` is saturated in `ℝ≥0`**: if `s = t + h` with `s`, `t` rational, then `h = s - t` is
rational. -/
theorem isSaturated_ratSet : IsSaturated ratSet := by
  rintro s ⟨p, hp⟩ t ⟨q, hq⟩ h hsum
  refine ⟨p - q, ?_⟩
  have hreal : (s : ℝ) = (t : ℝ) + (h : ℝ) := by rw [hsum, NNReal.coe_add]
  push_cast
  rw [hp, hq, hreal]
  ring

/-! ### Every positive real is the sum of a series of positive rationals

The one analytic input the `ℚ≥0` case needs beyond the `ℝ≥0` one, and what makes every *tilded*
element an `ℵ₀`-sum of rationals.  For a rational value the geometric family already does it; for an
irrational one, take the dyadic truncations `⌊a·2ⁿ⌋/2ⁿ` and sum their increments — irrationality is
exactly what keeps infinitely many of those increments nonzero. -/

/-- The `n`-th dyadic truncation `⌊a·2ⁿ⌋/2ⁿ` of `a`. -/
noncomputable def dyadic (a : ℝ≥0) (n : ℕ) : ℝ≥0 := (⌊a * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n

theorem dyadic_mem_ratSet (a : ℝ≥0) (n : ℕ) : dyadic a n ∈ ratSet := by
  refine ⟨(⌊a * 2 ^ n⌋₊ : ℚ) / 2 ^ n, ?_⟩
  rw [dyadic]
  push_cast
  ring

theorem dyadic_le (a : ℝ≥0) (n : ℕ) : dyadic a n ≤ a := by
  rw [dyadic, div_le_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ n)]
  exact Nat.floor_le zero_le

theorem dyadic_mono (a : ℝ≥0) : Monotone (dyadic a) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [dyadic, dyadic, div_le_div_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ n)
    (by positivity : (0 : ℝ≥0) < 2 ^ (n + 1))]
  have hle : ((2 * ⌊a * 2 ^ n⌋₊ : ℕ) : ℝ≥0) ≤ a * 2 ^ (n + 1) := by
    push_cast
    rw [pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0) _]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le zero_le) zero_le
  have hfloor : 2 * ⌊a * 2 ^ n⌋₊ ≤ ⌊a * 2 ^ (n + 1)⌋₊ := Nat.le_floor hle
  calc (⌊a * 2 ^ n⌋₊ : ℝ≥0) * 2 ^ (n + 1) = ((2 * ⌊a * 2 ^ n⌋₊ : ℕ) : ℝ≥0) * 2 ^ n := by
        push_cast
        rw [pow_succ]
        ring
    _ ≤ (⌊a * 2 ^ (n + 1)⌋₊ : ℝ≥0) * 2 ^ n := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfloor) zero_le

/-- The dyadic truncations approximate from below to within `2⁻ⁿ`. -/
theorem lt_dyadic_add (a : ℝ≥0) (n : ℕ) : a < dyadic a n + (2⁻¹ : ℝ≥0) ^ n := by
  have hpos : (0 : ℝ≥0) < 2 ^ n := by positivity
  have key : (dyadic a n + (2⁻¹ : ℝ≥0) ^ n) * 2 ^ n = (⌊a * 2 ^ n⌋₊ : ℝ≥0) + 1 := by
    rw [dyadic, add_mul, div_mul_cancel₀ _ (ne_of_gt hpos), ← mul_pow]
    norm_num
  refine lt_of_mul_lt_mul_right ?_ (le_of_lt hpos)
  rw [key]
  exact Nat.lt_floor_add_one (a * 2 ^ n)

/-- So the dyadic truncations have supremum `a`. -/
theorem iSup_dyadic (a : ℝ≥0) : (⨆ n, ((dyadic a n : ℝ≥0) : ℝ≥0∞)) = (a : ℝ≥0∞) := by
  refine le_antisymm (iSup_le fun n => by exact_mod_cast dyadic_le a n) ?_
  refine le_iSup_iff.mpr fun b hb => ?_
  by_contra hcon
  rw [not_le] at hcon
  have hbtop : b ≠ ⊤ := fun hc => absurd (hc ▸ hcon) (by simp)
  set c : ℝ≥0 := b.toNNReal with hcdef
  have hbc : (c : ℝ≥0∞) = b := ENNReal.coe_toNNReal hbtop
  have hca : c < a := by rw [← ENNReal.coe_lt_coe, hbc]; exact hcon
  have hD : ∀ n, dyadic a n ≤ c := fun n => by
    rw [← ENNReal.coe_le_coe, hbc]; exact hb n
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (tsub_pos_of_lt hca) (by norm_num : (2⁻¹ : ℝ≥0) < 1)
  have h1 : a < c + (a - c) := lt_of_lt_of_le (lt_dyadic_add a n)
    (add_le_add (hD n) (le_of_lt hn))
  rw [add_tsub_cancel_of_le (le_of_lt hca)] at h1
  exact absurd h1 (lt_irrefl a)

/-- The increments of a monotone sequence form a family whose series sum is its supremum. -/
theorem esum_increments {P : ℕ → ℝ≥0} (hmono : Monotone P) :
    esum (fun n => if n = 0 then P 1 else P (n + 1) - P n) = ⨆ n, ((P n : ℝ≥0) : ℝ≥0∞) := by
  set x : ℕ → ℝ≥0 := fun n => if n = 0 then P 1 else P (n + 1) - P n with hxdef
  have hpsum : ∀ N, psum x (N + 1) = P (N + 1) := by
    intro N
    induction N with
    | zero => simp [psum, hxdef]
    | succ N ih =>
        rw [psum, Finset.sum_range_succ, ← psum, ih, hxdef]
        show P (N + 1) + (if N + 1 = 0 then P 1 else P (N + 2) - P (N + 1)) = P (N + 2)
        rw [if_neg (Nat.succ_ne_zero N)]
        exact add_tsub_cancel_of_le (hmono (Nat.le_succ (N + 1)))
  have hesum : esum x = ⨆ N, ((psum x N : ℝ≥0) : ℝ≥0∞) := by
    rw [esum, ENNReal.tsum_eq_iSup_nat]
    exact iSup_congr fun N => (coe_psum x N).symm
  rw [hesum]
  refine le_antisymm (iSup_le fun N => ?_) (iSup_le fun n => ?_)
  · cases N with
    | zero => simp [psum]
    | succ N =>
        rw [hpsum N]
        exact le_iSup (fun n => ((P n : ℝ≥0) : ℝ≥0∞)) (N + 1)
  · refine le_trans (by exact_mod_cast hmono (Nat.le_succ n) : ((P n : ℝ≥0) : ℝ≥0∞) ≤ (P (n + 1) : ℝ≥0∞)) ?_
    rw [← hpsum n]
    exact le_iSup (fun N => ((psum x N : ℝ≥0) : ℝ≥0∞)) (n + 1)

/-- **Every positive real is the sum of a series of positive rationals** — with infinite support, as
it must be. -/
theorem exists_ratSet_family {a : ℝ≥0} (ha : a ≠ 0) :
    ∃ x : ℕ → ℝ≥0, (∀ n, x n ∈ ratSet) ∧ (Function.support x).Infinite
      ∧ esum x = (a : ℝ≥0∞) := by
  classical
  by_cases hrat : a ∈ ratSet
  · -- a rational value: the geometric family, whose terms are rational
    refine ⟨geomTo a, fun n => ?_, infinite_support_geomTo ha, esum_geomTo a⟩
    rw [geomTo]
    exact mul_mem_ratSet (mul_mem_ratSet hrat inv_two_mem_ratSet)
      (pow_mem_ratSet inv_two_mem_ratSet n)
  · -- an irrational value: the increments of the dyadic truncations
    refine ⟨fun n => if n = 0 then dyadic a 1 else dyadic a (n + 1) - dyadic a n, fun n => ?_, ?_,
      by rw [esum_increments (dyadic_mono a), iSup_dyadic]⟩
    · -- each increment is rational, being a difference of rationals
      cases n with
      | zero => exact dyadic_mem_ratSet a 1
      | succ n =>
          refine isSaturated_ratSet _ (dyadic_mem_ratSet a (n + 2)) _
            (dyadic_mem_ratSet a (n + 1)) _ ?_
          simp only [if_neg (Nat.succ_ne_zero n)]
          exact (add_tsub_cancel_of_le (dyadic_mono a (Nat.le_succ (n + 1)))).symm
    · -- infinitely many increments are nonzero: else `a` would be a dyadic truncation
      intro hfin
      obtain ⟨N, hN⟩ := (Set.Finite.bddAbove hfin)
      have hconst : ∀ m, dyadic a (N + 1 + m) = dyadic a (N + 1) := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
            have hzero : dyadic a (N + 1 + m + 1) - dyadic a (N + 1 + m) = 0 := by
              by_contra hne
              have hmem : (N + 1 + m) ∈ Function.support
                  (fun n => if n = 0 then dyadic a 1 else dyadic a (n + 1) - dyadic a n) := by
                simp only [Function.mem_support, if_neg (show N + 1 + m ≠ 0 by omega)]
                exact hne
              have := hN hmem
              omega
            have := add_tsub_cancel_of_le (dyadic_mono a (Nat.le_succ (N + 1 + m)))
            rw [hzero, add_zero] at this
            rw [show N + 1 + (m + 1) = N + 1 + m + 1 from rfl, ← this, ih]
      -- then `a` is that truncation, which is rational
      refine hrat ?_
      have heq : a = dyadic a (N + 1) := by
        refine le_antisymm ?_ (dyadic_le a (N + 1))
        by_contra hlt
        rw [not_le] at hlt
        obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (tsub_pos_of_lt hlt)
          (by norm_num : (2⁻¹ : ℝ≥0) < 1)
        have hmono2 : (2⁻¹ : ℝ≥0) ^ (N + 1 + k) ≤ (2⁻¹ : ℝ≥0) ^ k :=
          pow_le_pow_of_le_one zero_le (by norm_num) (by omega)
        have h1 : a < dyadic a (N + 1) + (a - dyadic a (N + 1)) :=
          lt_of_lt_of_le (lt_dyadic_add a (N + 1 + k))
            (add_le_add (le_of_eq (hconst k)) (le_of_lt (lt_of_le_of_lt hmono2 hk)))
        rw [add_tsub_cancel_of_le (le_of_lt hlt)] at h1
        exact absurd h1 (lt_irrefl a)
      rw [heq]
      exact dyadic_mem_ratSet a (N + 1)

/-- **Examples 3.3(3)** / **Examples 3.13** for `ℚ≥0`: the universal `ℵ₀`-extension of `ℚ≥0` is the
`ℵ₀`-submonoid of `H = ℝ≥0 ∪ ℝ̃>0 ∪ {∞}` generated by `ℚ≥0`. -/
theorem isUniversalKExtension_ratSet :
    letI := LMonoid.ofAddCommMonoid ℝ≥0
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
    letI := (isLSubmonoid_ratSet : IsLSubmonoid (ℵ₀ : Cardinal.{u}) ratSet).lmonoid
    letI := (KMonoid.isKSubmonoid_kclosure (ℵ₀ : Cardinal.{u})
      (RTilde.ofReal '' ratSet)).kmonoid
    IsUniversalKExtension (ℵ₀ : Cardinal.{u}) ℵ₀ ↥ratSet
      ↥(KMonoid.kclosure (ℵ₀ : Cardinal.{u}) (RTilde.ofReal '' ratSet)) le_rfl
      (fun s => ⟨RTilde.ofReal (s : ℝ≥0), KMonoid.subset_kclosure ⟨(s : ℝ≥0), s.2, rfl⟩⟩) := by
  let := LMonoid.ofAddCommMonoid ℝ≥0
  let : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
  exact lemma_3_14_sub le_rfl RTilde.isBraidedOver_rtilde ratSet isLSubmonoid_ratSet
    (Or.inr isSaturated_ratSet)

/-- The elements of `H` that an `ℵ₀`-sum of rationals can reach: everything tilded, `∞`, and the
plain *rationals*. -/
def ratReachable : Set RTilde :=
  {h | h.tilded = true ∨ h.val = ⊤ ∨ ∃ b ∈ ratSet, h = RTilde.ofReal b}

theorem isKSubmonoid_ratReachable :
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
    KMonoid.IsKSubmonoid (ℵ₀ : Cardinal.{u}) ratReachable := by
  let : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
  refine ⟨Or.inr (Or.inr ⟨0, zero_mem_ratSet, rfl⟩), fun x hx => ?_⟩
  show RTilde.sigma x ∈ ratReachable
  cases hfl : (RTilde.sigma x).tilded with
  | true => exact Or.inl hfl
  | false =>
      by_cases htop : (RTilde.sigma x).val = ⊤
      · exact Or.inr (Or.inl htop)
      · -- a plain, finite sum: every entry is a plain rational and only finitely many are nonzero
        rcases (RTilde.tilded_sigma_eq_false_iff x).mp hfl with hc | hpl
        · exact absurd (by rw [RTilde.val_sigma]; exact hc) htop
        · have hentry : ∀ i, ∃ b ∈ ratSet, x i = RTilde.ofReal b := by
            intro i
            have hne : (x i).val ≠ ⊤ := by
              intro hc
              refine htop ?_
              rw [RTilde.val_sigma]
              refine top_unique ?_
              rw [← hc]
              exact ENNReal.le_tsum i
            rcases hx i with hct | hct | hct
            · exact absurd (hpl.1 i) (by rw [hct]; simp)
            · exact absurd hct hne
            · exact hct
          choose b hbrat hbeq using hentry
          have hzero : ∀ i, x i = 0 ↔ b i = 0 := by
            intro i
            rw [hbeq i]
            constructor
            · intro hc
              have hv := congrArg RTilde.val hc
              rw [RTilde.val_ofReal, RTilde.val_zero] at hv
              exact_mod_cast hv
            · intro hc
              rw [hc]
              rfl
          have hsupp : Function.support b = Function.support x := by
            ext i
            simp only [Function.mem_support, ne_eq, hzero i]
          have hbfin : (Function.support b).Finite := by rw [hsupp]; exact hpl.2
          refine Or.inr (Or.inr ⟨∑ᶠ i, b i, ?_, ?_⟩)
          · rw [finsum_eq_sum b hbfin]
            exact ratSubmonoid.sum_mem fun i _ => hbrat i
          · refine RTilde.ext ?_ ?_
            · rw [RTilde.val_sigma, RTilde.val_ofReal, coe_finsum_eq_esum hbfin, esum]
              exact tsum_congr fun i => by rw [hbeq i, RTilde.val_ofReal]
            · rw [hfl, RTilde.tilded_ofReal]

/-- **Examples 3.3(3)**: a plain irrational is not an `ℵ₀`-sum of rationals — the irrationals
appear in the universal `ℵ₀`-extension of `ℚ≥0` only in the tilde copy. -/
theorem ofReal_notMem_kclosure_of_not_mem_ratSet {a : ℝ≥0} (ha : a ∉ ratSet) :
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
    RTilde.ofReal a ∉ KMonoid.kclosure (ℵ₀ : Cardinal.{u}) (RTilde.ofReal '' ratSet) := by
  let : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
  intro hmem
  have hsub : KMonoid.kclosure (ℵ₀ : Cardinal.{u}) (RTilde.ofReal '' ratSet) ⊆ ratReachable :=
    KMonoid.kclosure_le (fun _ ⟨b, hb, hbe⟩ => Or.inr (Or.inr ⟨b, hb, hbe.symm⟩))
      isKSubmonoid_ratReachable
  rcases hsub hmem with hc | hc | ⟨b, hb, hbe⟩
  · exact absurd hc (by rw [RTilde.tilded_ofReal]; simp)
  · exact absurd hc (by rw [RTilde.val_ofReal]; exact ENNReal.coe_ne_top)
  · refine ha ?_
    have : ((a : ℝ≥0) : ℝ≥0∞) = ((b : ℝ≥0) : ℝ≥0∞) := congrArg RTilde.val hbe
    rw [show a = b from by exact_mod_cast this]
    exact hb

/-! ### The extension of `ℚ≥0` is `ℚ≥0 ∪ ℝ̃>0 ∪ {∞}` on the nose -/

/-- Every tilded element is an `ℵ₀`-sum of rationals: expand its value as a series of positive
rationals, which has infinite support and therefore gets the tilde. -/
theorem tilde_mem_kclosure (a : ℝ≥0) (ha : a ≠ 0) :
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
    RTilde.tilde a ha ∈ KMonoid.kclosure (ℵ₀ : Cardinal.{u}) (RTilde.ofReal '' ratSet) := by
  let : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
  obtain ⟨x, hxrat, hxinf, hxsum⟩ := exists_ratSet_family ha
  have hUL : #(ULift.{u} ℕ) = #(Idx (ℵ₀ : Cardinal.{u})) := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0, mk_Idx]
  obtain ⟨e0⟩ := Cardinal.eq.mp hUL
  set e : ℕ ≃ Idx (ℵ₀ : Cardinal.{u}) := Equiv.ulift.symm.trans e0 with hedef
  set y : Idx (ℵ₀ : Cardinal.{u}) → ℝ≥0 := fun i => x (e.symm i) with hydef
  have hyinf : (Function.support y).Infinite := infinite_support_comp_equiv e hxinf
  have hysum : esum y = (a : ℝ≥0∞) := by
    rw [hydef, show (esum fun i => x (e.symm i)) = esum (x ∘ e.symm) from rfl,
      esum_comp_equiv e.symm x, hxsum]
  have hmem := (KMonoid.isKSubmonoid_kclosure (ℵ₀ : Cardinal.{u})
    (RTilde.ofReal '' ratSet)).ksum_mem (fun i => RTilde.ofReal (y i))
    fun i => KMonoid.subset_kclosure ⟨y i, hxrat (e.symm i), rfl⟩
  have heq : (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{u})) fun i => RTilde.ofReal (y i))
      = RTilde.tilde a ha := by
    rw [show (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{u})) fun i => RTilde.ofReal (y i))
      = RTilde.sigma (fun i => RTilde.ofReal (y i)) from rfl]
    refine RTilde.ext ?_ ?_
    · rw [RTilde.val_sigma, RTilde.tsum_val_ofReal_comp, hysum, RTilde.val_tilde]
    · rw [RTilde.tilded_tilde]
      cases hs : (RTilde.sigma fun i => RTilde.ofReal (y i)).tilded with
      | false =>
          rcases (RTilde.sigma_ofReal_comp y).2.mp hs with hc | hc
          · rw [hysum] at hc
            exact absurd hc ENNReal.coe_ne_top
          · exact absurd hc hyinf
      | true => rfl
  rw [← heq]
  exact hmem

/-- `∞` is an `ℵ₀`-sum of rationals: infinitely many `1`s. -/
theorem top_mem_kclosure :
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
    RTilde.top ∈ KMonoid.kclosure (ℵ₀ : Cardinal.{u}) (RTilde.ofReal '' ratSet) := by
  let : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
  have hone : (1 : ℝ≥0) ∈ ratSet := ⟨1, by norm_num⟩
  have hmem := (KMonoid.isKSubmonoid_kclosure (ℵ₀ : Cardinal.{u})
    (RTilde.ofReal '' ratSet)).ksum_mem (fun _ : Idx (ℵ₀ : Cardinal.{u}) => RTilde.ofReal 1)
    fun _ => KMonoid.subset_kclosure ⟨1, hone, rfl⟩
  have heq : (KMonoid.ksum (κ := (ℵ₀ : Cardinal.{u})) fun _ : Idx (ℵ₀ : Cardinal.{u}) =>
      RTilde.ofReal 1) = RTilde.top := by
    refine RTilde.sigma_of_val_eq_top ?_
    have : Infinite (Idx (ℵ₀ : Cardinal.{u})) := infinite_Idx le_rfl
    show (∑' _ : Idx (ℵ₀ : Cardinal.{u}), ((1 : ℝ≥0) : ℝ≥0∞)) = ⊤
    simp
  rw [← heq]
  exact hmem

/-- **Examples 3.3(3)**: the `ℵ₀`-submonoid of `H` generated by `ℚ≥0` — the universal
`ℵ₀`-extension of `ℚ≥0`, by `isUniversalKExtension_ratSet` — is exactly
`ℚ≥0 ∪ ℝ̃>0 ∪ {∞}`: every tilded element and `∞` are reached, and no plain irrational is. -/
theorem kclosure_ofReal_ratSet :
    letI : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
    KMonoid.kclosure (ℵ₀ : Cardinal.{u}) (RTilde.ofReal '' ratSet) = ratReachable := by
  let : KMonoid (ℵ₀ : Cardinal.{u}) RTilde := RTilde.instKMonoid
  refine Set.Subset.antisymm (KMonoid.kclosure_le
    (fun _ ⟨b, hb, hbe⟩ => Or.inr (Or.inr ⟨b, hb, hbe.symm⟩)) isKSubmonoid_ratReachable) ?_
  rintro h (hfl | hval | ⟨b, hb, rfl⟩)
  · -- a tilded element: its value is neither `0` nor `∞`
    have hne : h.val ≠ ⊤ := RTilde.val_ne_top hfl
    set a : ℝ≥0 := h.val.toNNReal with hadef
    have ha : ((a : ℝ≥0) : ℝ≥0∞) = h.val := ENNReal.coe_toNNReal hne
    have ha0 : a ≠ 0 := by
      intro hc
      refine RTilde.val_ne_zero hfl ?_
      rw [← ha, hc]
      simp
    rw [show h = RTilde.tilde a ha0 from RTilde.ext (by rw [RTilde.val_tilde, ha])
      (by rw [RTilde.tilded_tilde, hfl])]
    exact tilde_mem_kclosure a ha0
  · rw [RTilde.eq_top_of_val_eq_top hval]
    exact top_mem_kclosure
  · exact KMonoid.subset_kclosure ⟨b, hb, rfl⟩

end KappaMonoid
