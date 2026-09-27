/-
**§3.2, around Proposition 3.15**: the slack-variable construction and the failure of saturation
over `F_κ`, the explicit descriptions of **Example 3.16**, and the paper's own families,
listings and slack-variable extension of **Example 3.17**.
-/
import KappaMonoid.Examples.Diophantine

universe u t

open Cardinal Function Set

namespace KappaMonoid

section DiophantineExtra

variable {n : ℕ} {κ : Cardinal.{u}}

/-! ## Helpers: values of points of `F_{ℵ₀}^n` -/

/-- A linear form in two unknowns over any `F_κ`, evaluated on cardinals. -/
theorem val_linEval_two' (hκ : ℵ₀ ≤ κ) (a : Fin 2 → ℕ) (x : Fin 2 → Fcard κ) :
    ((linEval hκ a x : Fcard κ) : Cardinal.{u})
      = (a 0 : Cardinal.{u}) * ((x 0 : Fcard κ) : Cardinal.{u})
        + (a 1 : Cardinal.{u}) * ((x 1 : Fcard κ) : Cardinal.{u}) := by
  let := Fcard.instKMonoid hκ
  show ((∑ i, (a i) • x i : Fcard κ) : Cardinal.{u}) = _
  rw [← fcardVal_apply hκ, map_sum, Fin.sum_univ_two]
  simp only [fcardVal_apply, map_nsmul, nsmul_eq_mul]

/-- The value of a component of `h + ℵ₀h'`: that of `h` where `h'` vanishes, `ℵ₀` elsewhere. -/
theorem val_add_alephPart (h h' : Fin n → Fcard (ℵ₀ : Cardinal.{u})) (i : Fin n) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    (((h + alephPart h') i : Fcard ℵ₀) : Cardinal.{u})
      = if ((h' i : Fcard ℵ₀) : Cardinal.{u}) = 0 then ((h i : Fcard ℵ₀) : Cardinal.{u})
        else ℵ₀ := by
  show ((h i + alephPart h' i : Fcard ℵ₀) : Cardinal.{u}) = _
  rw [Fcard.instKMonoid_add, val_alephPart]
  split
  · rw [add_zero]
  · exact Cardinal.add_eq_right le_rfl (Fcard.le _)

/-- Membership in `ℵ₀H`, componentwise. -/
theorem LinSystem.mem_image_alephPart_iff (sys : LinSystem n)
    (x : Fin n → Fcard (ℵ₀ : Cardinal.{u})) :
    x ∈ alephPart '' sys.finSolutions ↔ ∃ h ∈ sys.finSolutions, ∀ i,
      ((x i : Fcard ℵ₀) : Cardinal.{u})
        = if ((h i : Fcard ℵ₀) : Cardinal.{u}) = 0 then 0 else ℵ₀ := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, fun i => val_alephPart h i⟩
  · rintro ⟨h, hh, hx⟩
    exact ⟨h, hh, funext fun i => Fcard.ext ((val_alephPart h i).trans (hx i).symm)⟩

/-- Membership in `H + ℵ₀H`, componentwise. -/
theorem LinSystem.mem_alephExt_iff (sys : LinSystem n) (x : Fin n → Fcard (ℵ₀ : Cardinal.{u})) :
    x ∈ sys.alephExt ↔ ∃ h ∈ sys.finSolutions, ∃ h' ∈ sys.finSolutions, ∀ i,
      ((x i : Fcard ℵ₀) : Cardinal.{u})
        = if ((h' i : Fcard ℵ₀) : Cardinal.{u}) = 0 then ((h i : Fcard ℵ₀) : Cardinal.{u})
          else ℵ₀ := by
  constructor
  · rintro ⟨h, hh, h', hh', rfl⟩
    exact ⟨h, hh, h', hh', fun i => val_add_alephPart h h' i⟩
  · rintro ⟨h, hh, h', hh', hx⟩
    exact ⟨h, hh, h', hh',
      funext fun i => Fcard.ext ((hx i).trans (val_add_alephPart h h' i).symm)⟩

theorem forall_fin_two' {p : Fin 2 → Prop} (h0 : p 0) (h1 : p 1) : ∀ i, p i := by
  intro i; fin_cases i
  · exact h0
  · exact h1

theorem forall_fin_three' {p : Fin 3 → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) : ∀ i, p i := by
  intro i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem fcard_eq_zero_of_val {c : Fcard (ℵ₀ : Cardinal.{u})} (h : (c : Cardinal.{u}) = 0) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    c = 0 :=
  Fcard.ext (h.trans (Fcard.instKMonoid_zero (le_refl (ℵ₀ : Cardinal.{u}))).symm)

/-- The point `(m, m')` of `F_{ℵ₀}²`. -/
noncomputable def pt2 (m m' : ℕ) : Fin 2 → Fcard (ℵ₀ : Cardinal.{u}) :=
  fun i => if i = 0 then Fcard.mk (m : Cardinal.{u}) Cardinal.natCast_lt_aleph0.le
    else Fcard.mk (m' : Cardinal.{u}) Cardinal.natCast_lt_aleph0.le

@[simp] theorem val_pt2_zero (m m' : ℕ) : ((pt2.{u} m m' 0 : Fcard ℵ₀) : Cardinal.{u}) = m := rfl

@[simp] theorem val_pt2_one (m m' : ℕ) : ((pt2.{u} m m' 1 : Fcard ℵ₀) : Cardinal.{u}) = m' := rfl

/-- The point `(a, b, c)` of `F_{ℵ₀}³`. -/
noncomputable def pt3 (a b c : ℕ) : Fin 3 → Fcard (ℵ₀ : Cardinal.{u}) :=
  fun i => if i = 0 then Fcard.mk (a : Cardinal.{u}) Cardinal.natCast_lt_aleph0.le
    else if i = 1 then Fcard.mk (b : Cardinal.{u}) Cardinal.natCast_lt_aleph0.le
    else Fcard.mk (c : Cardinal.{u}) Cardinal.natCast_lt_aleph0.le

@[simp] theorem val_pt3_zero (a b c : ℕ) : ((pt3.{u} a b c 0 : Fcard ℵ₀) : Cardinal.{u}) = a :=
  rfl

@[simp] theorem val_pt3_one (a b c : ℕ) : ((pt3.{u} a b c 1 : Fcard ℵ₀) : Cardinal.{u}) = b :=
  rfl

@[simp] theorem val_pt3_two (a b c : ℕ) : ((pt3.{u} a b c 2 : Fcard ℵ₀) : Cardinal.{u}) = c :=
  rfl

/-! ## The prose before Proposition 3.15

Two remarks of the paper.  First, a system with inequalities can be rewritten without them by
introducing one slack variable per inequality; over `ℕ₀^n` this changes the monoid only up to
isomorphism (`LinSystem.withSlack`, `LinSystem.withSlackEquiv`), and conversely an equation is the
same as two inequalities (`LinSystem.eqsAsIneqs`).  Second, cancellativity makes a monoid cut out
of `ℕ₀^n` by equations and congruences saturated (`isSaturatedFin_of_ineqs_empty`), but over `F_κ`
this fails (`not_isSaturated_diagSystem`). -/

/-- In `F_κ`, `AddLe` is the order of cardinals. -/
theorem fcard_addLe_iff (hκ : ℵ₀ ≤ κ) (a b : Fcard κ) :
    letI := Fcard.instKMonoid hκ
    AddLe a b ↔ (a : Cardinal.{u}) ≤ b := by
  let := Fcard.instKMonoid hκ
  constructor
  · rintro ⟨c, hc⟩
    rw [← hc, Fcard.instKMonoid_add]
    exact self_le_add_right _ _
  · intro h
    obtain ⟨c, hc⟩ := le_iff_exists_add.mp h
    refine ⟨Fcard.mk c ((self_le_add_left c (a : Cardinal.{u})).trans
      ((le_of_eq hc.symm).trans (Fcard.le b))), Fcard.ext ?_⟩
    rw [Fcard.instKMonoid_add, Fcard.val_mk, ← hc]

/-- **An equation is two inequalities** (the prose before Proposition 3.15): the system with every
equation `A = B` replaced by the two inequalities `A ≤ B` and `B ≤ A`. -/
def LinSystem.eqsAsIneqs (sys : LinSystem n) : LinSystem n where
  eqs := ∅
  ineqs := sys.ineqs ∪ sys.eqs ∪ Prod.swap '' sys.eqs
  congrs := sys.congrs

/-- **An equation is two inequalities**: `eqsAsIneqs` has the same solutions over every `F_κ`. -/
theorem LinSystem.solutions_eqsAsIneqs (sys : LinSystem n) (hκ : ℵ₀ ≤ κ) :
    sys.eqsAsIneqs.solutions hκ = sys.solutions hκ := by
  let := Fcard.instKMonoid hκ
  have key : ∀ a b : Fcard κ, a = b ↔ AddLe a b ∧ AddLe b a := by
    intro a b
    rw [fcard_addLe_iff, fcard_addLe_iff]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => Fcard.ext (le_antisymm h.1 h.2)⟩
  ext x
  constructor
  · rintro ⟨-, hineq, hcong⟩
    exact ⟨fun p hp => (key _ _).mpr ⟨hineq p (Or.inl (Or.inr hp)),
      hineq (Prod.swap p) (Or.inr ⟨p, hp, rfl⟩)⟩, fun p hp => hineq p (Or.inl (Or.inl hp)), hcong⟩
  · rintro ⟨heq, hineq, hcong⟩
    refine ⟨fun p hp => absurd hp (Set.notMem_empty p), ?_, hcong⟩
    rintro p ((hp | hp) | ⟨q, hq, rfl⟩)
    · exact hineq p hp
    · exact ((key _ _).mp (heq p hp)).1
    · exact ((key _ _).mp (heq q hq)).2

/-- **The slack-variable construction** (the prose before Proposition 3.15).  Given the
inequalities `A_j ≤ B_j` of a system as a family `e : Fin k → _`, the system in `n + k` unknowns
with the same equations and congruences (in the first `n` unknowns) and, for each `j`, the
equation `A_j(x) + s_j = B_j(x)` in the slack variable `s_j`.  It has no inequalities. -/
def LinSystem.withSlack (sys : LinSystem n) {k : ℕ} (e : Fin k → (Fin n → ℕ) × (Fin n → ℕ)) :
    LinSystem (n + k) where
  eqs := (fun p => (Fin.append p.1 0, Fin.append p.2 0)) '' sys.eqs ∪
    Set.range fun j => (Fin.append (e j).1 (Pi.single j 1), Fin.append (e j).2 0)
  ineqs := ∅
  congrs := (fun p => (Fin.append p.1 0, p.2)) '' sys.congrs

theorem LinSystem.withSlack_ineqs (sys : LinSystem n) {k : ℕ}
    (e : Fin k → (Fin n → ℕ) × (Fin n → ℕ)) : (sys.withSlack e).ineqs = ∅ := rfl

/-- A linear form in `n + k` unknowns splits into the forms in the first `n` and the last `k`. -/
theorem linEval_append (hκ : ℵ₀ ≤ κ) {k : ℕ} (a : Fin n → ℕ) (c : Fin k → ℕ)
    (y : Fin (n + k) → Fcard κ) :
    letI := Fcard.instKMonoid hκ
    linEval hκ (Fin.append a c) y
      = linEval hκ a (fun i => y (Fin.castAdd k i))
        + linEval hκ c (fun j => y (Fin.natAdd n j)) := by
  let := Fcard.instKMonoid hκ
  show ∑ i, (Fin.append a c i) • y i
    = ∑ i, (a i) • y (Fin.castAdd k i) + ∑ j, (c j) • y (Fin.natAdd n j)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem linEval_zero_coeff (hκ : ℵ₀ ≤ κ) {k : ℕ} (s : Fin k → Fcard κ) :
    letI := Fcard.instKMonoid hκ
    linEval hκ (0 : Fin k → ℕ) s = 0 := by
  let := Fcard.instKMonoid hκ
  show ∑ i, ((0 : Fin k → ℕ) i) • s i = 0
  exact Finset.sum_eq_zero fun i _ => zero_smul ℕ (s i)

theorem linEval_single (hκ : ℵ₀ ≤ κ) {k : ℕ} (j : Fin k) (s : Fin k → Fcard κ) :
    linEval hκ (Pi.single j 1 : Fin k → ℕ) s = s j := by
  let := Fcard.instKMonoid hκ
  show ∑ l, (Pi.single j 1 : Fin k → ℕ) l • s l = s j
  rw [Finset.sum_eq_single j (fun l _ hl => by rw [Pi.single_apply, if_neg hl, zero_smul])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_apply, if_pos rfl, one_smul]

/-- The natural-number shadow of a linear form is additive on families with finite components. -/
theorem linEvalNat_add (a : Fin n → ℕ) {x y : Fin n → Fcard (ℵ₀ : Cardinal.{u})}
    (hx : ∀ i, ((x i : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀)
    (hy : ∀ i, ((y i : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    linEvalNat a (x + y) = linEvalNat a x + linEvalNat a y := by
  let := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  let := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  unfold linEvalNat
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (((x + y) i : Fcard ℵ₀) : Cardinal.{u}) = (x i : Cardinal.{u}) + (y i : Cardinal.{u}) :=
    Fcard.instKMonoid_add (le_refl _) (x i) (y i)
  rw [h, Cardinal.toNat_add (hx i) (hy i), Nat.mul_add]

/-- On `H`, an inequality `A ≤ B` of the system holds between the natural-number shadows. -/
theorem LinSystem.linEvalNat_le_of_mem (sys : LinSystem n) {p : (Fin n → ℕ) × (Fin n → ℕ)}
    (hp : p ∈ sys.ineqs) {x : Fin n → Fcard (ℵ₀ : Cardinal.{u})} (hx : x ∈ sys.finSolutions) :
    linEvalNat p.1 x ≤ linEvalNat p.2 x := by
  have h := (fcard_addLe_iff (le_refl (ℵ₀ : Cardinal.{u})) _ _).mp (hx.1.2.1 p hp)
  rw [val_linEval_eq_linEvalNat _ hx.2, val_linEval_eq_linEvalNat _ hx.2] at h
  exact_mod_cast h

/-- The slack values `B_j(x) - A_j(x)` of a family with finite components. -/
noncomputable def slackVals {k : ℕ} (e : Fin k → (Fin n → ℕ) × (Fin n → ℕ))
    (x : Fin n → Fcard (ℵ₀ : Cardinal.{u})) : Fin k → Fcard (ℵ₀ : Cardinal.{u}) :=
  fun j => Fcard.mk ((linEvalNat (e j).2 x - linEvalNat (e j).1 x : ℕ) : Cardinal.{u})
    Cardinal.natCast_lt_aleph0.le

/-- `x ↦ (x, B(x) - A(x))` maps `H` into `H'`. -/
theorem LinSystem.append_slackVals_mem (sys : LinSystem n) {k : ℕ}
    (e : Fin k → (Fin n → ℕ) × (Fin n → ℕ)) (he : sys.ineqs = Set.range e)
    {x : Fin n → Fcard (ℵ₀ : Cardinal.{u})} (hx : x ∈ sys.finSolutions) :
    Fin.append x (slackVals e x) ∈ (sys.withSlack e).finSolutions := by
  have hle : ∀ j, linEvalNat (e j).1 x ≤ linEvalNat (e j).2 x := fun j =>
    sys.linEvalNat_le_of_mem (he ▸ Set.mem_range_self j) hx
  obtain ⟨⟨heq, -, hcong⟩, hfin⟩ := hx
  have hleft : (fun i => Fin.append x (slackVals e x) (Fin.castAdd k i)) = x :=
    funext fun i => Fin.append_left x _ i
  have hright : (fun j => Fin.append x (slackVals e x) (Fin.natAdd n j)) = slackVals e x :=
    funext fun j => Fin.append_right x _ j
  refine ⟨⟨?_, fun p hp => absurd hp (Set.notMem_empty p), ?_⟩, ?_⟩
  · rintro p (⟨q, hq, rfl⟩ | ⟨j, rfl⟩)
    · show linEval _ (Fin.append q.1 0) _ = linEval _ (Fin.append q.2 0) _
      rw [linEval_append, linEval_append, hleft, hright, linEval_zero_coeff, add_zero, add_zero]
      exact heq q hq
    · show linEval _ (Fin.append (e j).1 (Pi.single j 1)) _ = linEval _ (Fin.append (e j).2 0) _
      rw [linEval_append, linEval_append, hleft, hright, linEval_zero_coeff, add_zero,
        linEval_single]
      refine Fcard.ext ?_
      rw [Fcard.instKMonoid_add, val_linEval_eq_linEvalNat _ hfin,
        val_linEval_eq_linEvalNat _ hfin]
      show (linEvalNat (e j).1 x : Cardinal.{u})
        + ((linEvalNat (e j).2 x - linEvalNat (e j).1 x : ℕ) : Cardinal.{u}) = _
      rw [← Nat.cast_add, Nat.add_sub_cancel' (hle j)]
  · rintro p ⟨q, hq, rfl⟩
    obtain ⟨y, hy⟩ := hcong q hq
    refine ⟨y, ?_⟩
    show linEval _ (Fin.append q.1 0) _ = _
    rw [linEval_append, hleft, linEval_zero_coeff, add_zero]
    exact hy
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hfin i
    · rw [Fin.append_right]; exact Cardinal.natCast_lt_aleph0

/-- `(x, s) ↦ x` maps `H'` into `H`: the slack equation `A_j(x) + s_j = B_j(x)` witnesses the
inequality `A_j(x) ≤ B_j(x)`. -/
theorem LinSystem.castAdd_mem (sys : LinSystem n) {k : ℕ}
    (e : Fin k → (Fin n → ℕ) × (Fin n → ℕ)) (he : sys.ineqs = Set.range e)
    {y : Fin (n + k) → Fcard (ℵ₀ : Cardinal.{u})} (hy : y ∈ (sys.withSlack e).finSolutions) :
    (fun i => y (Fin.castAdd k i)) ∈ sys.finSolutions := by
  obtain ⟨⟨heq, -, hcong⟩, hfin⟩ := hy
  refine ⟨⟨fun q hq => ?_, fun p hp => ?_, fun q hq => ?_⟩, fun i => hfin _⟩
  · have h : linEval (le_refl (ℵ₀ : Cardinal.{u})) (Fin.append q.1 0) y
        = linEval (le_refl (ℵ₀ : Cardinal.{u})) (Fin.append q.2 0) y :=
      heq _ (Or.inl ⟨q, hq, rfl⟩)
    rw [linEval_append, linEval_append, linEval_zero_coeff, add_zero, add_zero] at h
    exact h
  · rw [he] at hp
    obtain ⟨j, rfl⟩ := hp
    have h : linEval (le_refl (ℵ₀ : Cardinal.{u})) (Fin.append (e j).1 (Pi.single j 1)) y
        = linEval (le_refl (ℵ₀ : Cardinal.{u})) (Fin.append (e j).2 0) y :=
      heq _ (Or.inr ⟨j, rfl⟩)
    rw [linEval_append, linEval_append, linEval_single, linEval_zero_coeff, add_zero] at h
    exact ⟨y (Fin.natAdd n j), h⟩
  · obtain ⟨z, hz⟩ := hcong _ ⟨q, hq, rfl⟩
    have hz' : linEval (le_refl (ℵ₀ : Cardinal.{u})) (Fin.append q.1 0) y = q.2 • z := hz
    rw [linEval_append, linEval_zero_coeff, add_zero] at hz'
    exact ⟨z, hz'⟩

/-- On `H'` the slack coordinates are determined by the others. -/
theorem LinSystem.append_slackVals_castAdd (sys : LinSystem n) {k : ℕ}
    (e : Fin k → (Fin n → ℕ) × (Fin n → ℕ))
    {y : Fin (n + k) → Fcard (ℵ₀ : Cardinal.{u})} (hy : y ∈ (sys.withSlack e).finSolutions) :
    Fin.append (fun i => y (Fin.castAdd k i)) (slackVals e fun i => y (Fin.castAdd k i)) = y := by
  obtain ⟨⟨heq, -, -⟩, hfin⟩ := hy
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
  · rw [Fin.append_right]
    have h : linEval (le_refl (ℵ₀ : Cardinal.{u})) (Fin.append (e j).1 (Pi.single j 1)) y
        = linEval (le_refl (ℵ₀ : Cardinal.{u})) (Fin.append (e j).2 0) y :=
      heq _ (Or.inr ⟨j, rfl⟩)
    rw [linEval_append, linEval_append, linEval_single, linEval_zero_coeff, add_zero] at h
    have hv := congrArg (fun c : Fcard ℵ₀ => (c : Cardinal.{u})) h
    rw [Fcard.instKMonoid_add, val_linEval_eq_linEvalNat _ (fun i => hfin _),
      val_linEval_eq_linEvalNat _ (fun i => hfin _)] at hv
    refine Fcard.ext ?_
    show ((linEvalNat (e j).2 (fun i => y (Fin.castAdd k i))
      - linEvalNat (e j).1 (fun i => y (Fin.castAdd k i)) : ℕ) : Cardinal.{u}) = _
    rw [← Cardinal.cast_toNat_of_lt_aleph0 (hfin (Fin.natAdd n j))] at hv ⊢
    have h2 : linEvalNat (e j).1 (fun i => y (Fin.castAdd k i))
        + ((y (Fin.natAdd n j) : Fcard ℵ₀) : Cardinal.{u}).toNat
        = linEvalNat (e j).2 (fun i => y (Fin.castAdd k i)) := by
      exact_mod_cast hv
    exact congrArg _ (by omega)

/-- The slack values are additive on `H`. -/
theorem LinSystem.slackVals_add (sys : LinSystem n) {k : ℕ}
    (e : Fin k → (Fin n → ℕ) × (Fin n → ℕ)) (he : sys.ineqs = Set.range e)
    {x y : Fin n → Fcard (ℵ₀ : Cardinal.{u})} (hx : x ∈ sys.finSolutions)
    (hy : y ∈ sys.finSolutions) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    letI := KMonoid.pi ℵ₀ (fun _ : Fin k => Fcard ℵ₀) (le_refl ℵ₀)
    slackVals e (x + y) = slackVals e x + slackVals e y := by
  let := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  let := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  let := KMonoid.pi ℵ₀ (fun _ : Fin k => Fcard ℵ₀) (le_refl ℵ₀)
  funext j
  have h1 := sys.linEvalNat_le_of_mem (he ▸ Set.mem_range_self j) hx
  have h2 := sys.linEvalNat_le_of_mem (he ▸ Set.mem_range_self j) hy
  refine Fcard.ext ?_
  show ((linEvalNat (e j).2 (x + y) - linEvalNat (e j).1 (x + y) : ℕ) : Cardinal.{u})
    = ((slackVals e x j + slackVals e y j : Fcard ℵ₀) : Cardinal.{u})
  rw [Fcard.instKMonoid_add]
  show _ = ((linEvalNat (e j).2 x - linEvalNat (e j).1 x : ℕ) : Cardinal.{u})
    + ((linEvalNat (e j).2 y - linEvalNat (e j).1 y : ℕ) : Cardinal.{u})
  rw [linEvalNat_add _ hx.2 hy.2, linEvalNat_add _ hx.2 hy.2, ← Nat.cast_add]
  exact congrArg _ (by omega)

/-- **The slack-variable construction is an isomorphism over `ℕ₀^n`** (the prose before
Proposition 3.15): if `e` enumerates the inequalities of `sys`, then `x ↦ (x, B(x) - A(x))` is an
isomorphism of monoids from `H = sys.finSolutions` onto `H' = (sys.withSlack e).finSolutions`,
the monoid cut out by a system *without* inequalities.  Example 3.17's `example_3_17_slack_iso`
is the instance `x₁ ≤ x₂`. -/
noncomputable def LinSystem.withSlackEquiv (sys : LinSystem n) {k : ℕ}
    (e : Fin k → (Fin n → ℕ) × (Fin n → ℕ)) (he : sys.ineqs = Set.range e) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
    letI := KMonoid.pi ℵ₀ (fun _ : Fin (n + k) => Fcard ℵ₀) (le_refl ℵ₀)
    letI : AddCommMonoid ↥sys.finSolutions :=
      addCommMonoidOfClosed sys.addSubmonoid_finSolutions.1
        (fun a ha b hb => sys.addSubmonoid_finSolutions.2 a ha b hb)
    letI : AddCommMonoid ↥(sys.withSlack e).finSolutions :=
      addCommMonoidOfClosed (sys.withSlack e).addSubmonoid_finSolutions.1
        (fun a ha b hb => (sys.withSlack e).addSubmonoid_finSolutions.2 a ha b hb)
    ↥sys.finSolutions ≃+ ↥(sys.withSlack e).finSolutions :=
  letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
  letI := KMonoid.pi ℵ₀ (fun _ : Fin k => Fcard ℵ₀) (le_refl ℵ₀)
  letI := KMonoid.pi ℵ₀ (fun _ : Fin (n + k) => Fcard ℵ₀) (le_refl ℵ₀)
  letI : AddCommMonoid ↥sys.finSolutions :=
    addCommMonoidOfClosed sys.addSubmonoid_finSolutions.1
      (fun a ha b hb => sys.addSubmonoid_finSolutions.2 a ha b hb)
  letI : AddCommMonoid ↥(sys.withSlack e).finSolutions :=
    addCommMonoidOfClosed (sys.withSlack e).addSubmonoid_finSolutions.1
      (fun a ha b hb => (sys.withSlack e).addSubmonoid_finSolutions.2 a ha b hb)
  { toFun := fun x => ⟨Fin.append (x : Fin n → Fcard ℵ₀) (slackVals e x),
      sys.append_slackVals_mem e he x.2⟩
    invFun := fun y => ⟨fun i => (y : Fin (n + k) → Fcard ℵ₀) (Fin.castAdd k i),
      sys.castAdd_mem e he y.2⟩
    left_inv := fun x => Subtype.ext (funext fun i => Fin.append_left _ _ i)
    right_inv := fun y => Subtype.ext (sys.append_slackVals_castAdd e y.2)
    map_add' := fun a b => Subtype.ext (by
      show Fin.append ((a : Fin n → Fcard ℵ₀) + (b : Fin n → Fcard ℵ₀))
          (slackVals e ((a : Fin n → Fcard ℵ₀) + (b : Fin n → Fcard ℵ₀)))
        = Fin.append (a : Fin n → Fcard ℵ₀) (slackVals e a)
          + Fin.append (b : Fin n → Fcard ℵ₀) (slackVals e b)
      rw [sys.slackVals_add e he a.2 b.2]
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · show _ = Fin.append (a : Fin n → Fcard ℵ₀) (slackVals e a) (Fin.castAdd k i)
          + Fin.append (b : Fin n → Fcard ℵ₀) (slackVals e b) (Fin.castAdd k i)
        rw [Fin.append_left, Fin.append_left, Fin.append_left]
        rfl
      · show _ = Fin.append (a : Fin n → Fcard ℵ₀) (slackVals e a) (Fin.natAdd n j)
          + Fin.append (b : Fin n → Fcard ℵ₀) (slackVals e b) (Fin.natAdd n j)
        rw [Fin.append_right, Fin.append_right, Fin.append_right]
        rfl) }

/-- **The slack-variable construction** for a system with finitely many inequalities: its monoid
over `ℕ₀^n` is isomorphic to one cut out by a system without inequalities. -/
theorem LinSystem.exists_withSlack_iso (sys : LinSystem n) (hfin : sys.ineqs.Finite) :
    ∃ (k : ℕ) (e : Fin k → (Fin n → ℕ) × (Fin n → ℕ)),
      (sys.withSlack e).ineqs = ∅ ∧
      letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
      letI := KMonoid.pi ℵ₀ (fun _ : Fin n => Fcard ℵ₀) (le_refl ℵ₀)
      letI := KMonoid.pi ℵ₀ (fun _ : Fin (n + k) => Fcard ℵ₀) (le_refl ℵ₀)
      letI : AddCommMonoid ↥sys.finSolutions :=
        addCommMonoidOfClosed sys.addSubmonoid_finSolutions.1
          (fun a ha b hb => sys.addSubmonoid_finSolutions.2 a ha b hb)
      letI : AddCommMonoid ↥(sys.withSlack e).finSolutions :=
        addCommMonoidOfClosed (sys.withSlack e).addSubmonoid_finSolutions.1
          (fun a ha b hb => (sys.withSlack e).addSubmonoid_finSolutions.2 a ha b hb)
      Nonempty (↥sys.finSolutions ≃+ ↥(sys.withSlack e).finSolutions) := by
  obtain ⟨k, e, -, he⟩ := hfin.fin_param
  exact ⟨k, e, rfl, ⟨sys.withSlackEquiv e he.symm⟩⟩

/-- Membership in the solutions of `x₁ = x₂` over any `F_κ`. -/
theorem mem_diagSystem_solutions' (hκ : ℵ₀ ≤ κ) (x : Fin 2 → Fcard κ) :
    x ∈ diagSystem.solutions hκ ↔
      ((x 0 : Fcard κ) : Cardinal.{u}) = ((x 1 : Fcard κ) : Cardinal.{u}) := by
  constructor
  · intro h
    have h1 := congrArg (fun c : Fcard κ => (c : Cardinal.{u})) (h.1 _ rfl)
    rw [val_linEval_two', val_linEval_two'] at h1
    simpa using h1
  · intro h
    refine ⟨fun p hp => ?_, fun p hp => absurd hp (Set.notMem_empty p),
      fun p hp => absurd hp (Set.notMem_empty p)⟩
    obtain rfl : p = (fun i => if i = 0 then 1 else 0, fun i => if i = 0 then 0 else 1) := hp
    refine Fcard.ext ?_
    rw [val_linEval_two', val_linEval_two']
    simpa using h

/-- **Equations do not give saturated `κ`-submonoids of `F_κ^n`** (the prose before
Proposition 3.15): for every infinite `κ` the `κ`-submonoid of `F_κ²` cut out by the single
equation `x₁ = x₂` is not saturated, because `(ℵ₀, ℵ₀) = (ℵ₀, ℵ₀) + (0, 1)` while `(0, 1)` is not a
solution.  Over `ℕ₀^n` such a monoid is saturated (`isSaturatedFin_of_ineqs_empty`). -/
theorem not_isSaturated_diagSystem (hκ : ℵ₀ ≤ κ) :
    letI := Fcard.instKMonoid hκ
    letI := KMonoid.pi κ (fun _ : Fin 2 => Fcard κ) hκ
    ¬ IsSaturated (diagSystem.solutions hκ) := by
  let := Fcard.instKMonoid hκ
  let := KMonoid.pi κ (fun _ : Fin 2 => Fcard κ) hκ
  intro hsat
  have hmem : (fun _ => Fcard.mk ℵ₀ hκ : Fin 2 → Fcard κ) ∈ diagSystem.solutions hκ :=
    (mem_diagSystem_solutions' hκ _).mpr rfl
  have hnot : (fun i => if i = 0 then Fcard.mk 0 zero_le
      else Fcard.mk 1 (Cardinal.one_lt_aleph0.le.trans hκ) : Fin 2 → Fcard κ)
      ∉ diagSystem.solutions hκ := by
    intro hm
    have h := (mem_diagSystem_solutions' hκ _).mp hm
    simp at h
  refine hnot (hsat _ hmem _ hmem _ (funext fun i => Fcard.ext ?_))
  fin_cases i
  · show (ℵ₀ : Cardinal.{u}) = ((Fcard.mk ℵ₀ hκ + Fcard.mk 0 zero_le : Fcard κ) : Cardinal.{u})
    rw [Fcard.instKMonoid_add]
    simp
  · show (ℵ₀ : Cardinal.{u}) = ((Fcard.mk ℵ₀ hκ
      + Fcard.mk 1 (Cardinal.one_lt_aleph0.le.trans hκ) : Fcard κ) : Cardinal.{u})
    rw [Fcard.instKMonoid_add]
    simp [Cardinal.add_one_eq le_rfl]

/-! ## Example 3.16: the explicit descriptions -/

/-- **Example 3.16**: `Ĥ = {(n, n) : n ∈ ℕ₀} ∪ {(ℵ₀, ℵ₀)}`.  Here `Ĥ = H + ℵ₀H` for the diagonal
`H`, the universal `ℵ₀`-extension by `prop_3_15_two_of_ineqs_empty diagSystem rfl`. -/
theorem mem_alephExt_diagSystem_iff (x : Fin 2 → Fcard (ℵ₀ : Cardinal.{u})) :
    x ∈ diagSystem.alephExt ↔
      (∃ m : ℕ, ((x 0 : Fcard ℵ₀) : Cardinal.{u}) = m ∧ ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = m) ∨
      (((x 0 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ ∧ ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀) := by
  rw [example_3_16.{u}.2.2.1, mem_diagSystem_solutions]
  constructor
  · intro h
    rcases lt_or_eq_of_le (Fcard.le (x 0)) with h0 | h0
    · obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp h0
      exact Or.inl ⟨m, hm, h.symm.trans hm⟩
    · exact Or.inr ⟨h0, h.symm.trans h0⟩
  · rintro (⟨m, h0, h1⟩ | ⟨h0, h1⟩) <;> rw [h0, h1]

theorem diag_mem_alephExt (c : Fcard (ℵ₀ : Cardinal.{u})) :
    (fun _ => c) ∈ (diagSystem.alephExt : Set (Fin 2 → Fcard (ℵ₀ : Cardinal.{u}))) := by
  rw [example_3_16.{u}.2.2.1, mem_diagSystem_solutions]

/-- The diagonal map `F_{ℵ₀} → Ĥ`, `c ↦ (c, c)`. -/
noncomputable def diagIncl (c : Fcard (ℵ₀ : Cardinal.{u})) :
    ↥(diagSystem.alephExt : Set (Fin 2 → Fcard (ℵ₀ : Cardinal.{u}))) :=
  ⟨fun _ => c, diag_mem_alephExt c⟩

/-- **Example 3.16**: `Ĥ ≅ F_{ℵ₀}` as `ℵ₀`-monoids, along `c ↦ (c, c)`. -/
theorem example_3_16_iso :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin 2 => Fcard ℵ₀) (le_refl ℵ₀)
    letI := diagSystem.isKSubmonoid_alephExt.kmonoid
    KMonoid.IsKHom ℵ₀ diagIncl.{u} ∧ Function.Bijective diagIncl.{u} := by
  refine ⟨⟨Subtype.ext rfl, fun x => Subtype.ext rfl⟩, fun a b hab => ?_, fun z => ?_⟩
  · exact congrFun (congrArg Subtype.val hab) 0
  · have hz' : (z : Fin 2 → Fcard ℵ₀) ∈ diagSystem.solutions (le_refl (ℵ₀ : Cardinal.{u})) := by
      rw [← example_3_16.{u}.2.2.1]; exact z.2
    have hz := (mem_diagSystem_solutions _).mp hz'
    refine ⟨(z : Fin 2 → Fcard ℵ₀) 0, Subtype.ext (funext fun i => ?_)⟩
    fin_cases i
    · rfl
    · exact Fcard.ext hz

/-- **Example 3.16**: the `ℵ₀`-submonoid of `F_{ℵ₀}²` cut out by `2x₁ = x₁ + x₂` is
`{(n, n)} ∪ {(ℵ₀, n) : n ∈ ℕ₀} ∪ {(ℵ₀, ℵ₀)}`. -/
theorem mem_doubleSystem_solutions_iff (x : Fin 2 → Fcard (ℵ₀ : Cardinal.{u})) :
    x ∈ doubleSystem.solutions (le_refl (ℵ₀ : Cardinal.{u})) ↔
      (∃ m : ℕ, ((x 0 : Fcard ℵ₀) : Cardinal.{u}) = m ∧ ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = m) ∨
      (∃ m : ℕ, ((x 0 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ ∧ ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = m) ∨
      (((x 0 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ ∧ ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀) := by
  rw [mem_doubleSystem_solutions]
  constructor
  · intro h
    rcases lt_or_eq_of_le (Fcard.le (x 0)) with h0 | h0
    · -- a finite first coordinate cancels
      rw [two_mul] at h
      have h01 := Cardinal.eq_of_add_eq_add_left h h0
      obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp h0
      exact Or.inl ⟨m, hm, h01.symm.trans hm⟩
    · rcases lt_or_eq_of_le (Fcard.le (x 1)) with h1 | h1
      · obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp h1
        exact Or.inr (Or.inl ⟨m, h0, hm⟩)
      · exact Or.inr (Or.inr ⟨h0, h1⟩)
  · rintro (⟨m, h0, h1⟩ | ⟨m, h0, h1⟩ | ⟨h0, h1⟩) <;> rw [h0, h1]
    · rw [two_mul]
    · rw [two_mul, Cardinal.aleph0_add_aleph0, Cardinal.aleph0_add_nat]
    · rw [two_mul]

/-! ## Example 3.17: `H = {(x, y) ∈ ℕ₀² : x ≤ y}` -/

/-- Membership in `H = {(x, y) ∈ ℕ₀² : x ≤ y}`, in natural numbers. -/
theorem mem_finSolutions_ineqSystem_iff (x : Fin 2 → Fcard (ℵ₀ : Cardinal.{u})) :
    x ∈ ineqSystem.finSolutions ↔ ∃ m m' : ℕ, m ≤ m' ∧
      ((x 0 : Fcard ℵ₀) : Cardinal.{u}) = m ∧ ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = m' := by
  constructor
  · intro hx
    exact ⟨_, _, le_of_mem_finSolutions_ineqSystem hx,
      (Cardinal.cast_toNat_of_lt_aleph0 (hx.2 0)).symm,
      (Cardinal.cast_toNat_of_lt_aleph0 (hx.2 1)).symm⟩
  · rintro ⟨m, m', hmm, h0, h1⟩
    refine mem_finSolutions_ineqSystem x
      (Fcard.mk ((m' - m : ℕ) : Cardinal.{u}) Cardinal.natCast_lt_aleph0.le) (fun i => ?_) ?_
    · fin_cases i
      · show ((x 0 : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀
        rw [h0]; exact Cardinal.natCast_lt_aleph0
      · show ((x 1 : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀
        rw [h1]; exact Cardinal.natCast_lt_aleph0
    · rw [h0, h1, Fcard.val_mk, ← Nat.cast_add, Nat.add_sub_cancel' hmm]

/-- Membership in `H' = {(x, y, z) ∈ ℕ₀³ : y = x + z}`, in natural numbers. -/
theorem mem_finSolutions_slackSystem_iff' (x : Fin 3 → Fcard (ℵ₀ : Cardinal.{u})) :
    x ∈ slackSystem.finSolutions ↔ ∃ a c : ℕ, ((x 0 : Fcard ℵ₀) : Cardinal.{u}) = a ∧
      ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = ((a + c : ℕ) : Cardinal.{u}) ∧
      ((x 2 : Fcard ℵ₀) : Cardinal.{u}) = c := by
  rw [mem_finSolutions_slackSystem_iff]
  constructor
  · rintro ⟨heq, hfin⟩
    refine ⟨_, _, (Cardinal.cast_toNat_of_lt_aleph0 (hfin 0)).symm, ?_,
      (Cardinal.cast_toNat_of_lt_aleph0 (hfin 2)).symm⟩
    rw [heq, Nat.cast_add, Cardinal.cast_toNat_of_lt_aleph0 (hfin 0),
      Cardinal.cast_toNat_of_lt_aleph0 (hfin 2)]
  · rintro ⟨a, c, h0, h1, h2⟩
    refine ⟨by rw [h0, h1, h2, Nat.cast_add], fun i => ?_⟩
    fin_cases i
    · show ((x 0 : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀
      rw [h0]; exact Cardinal.natCast_lt_aleph0
    · show ((x 1 : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀
      rw [h1]; exact Cardinal.natCast_lt_aleph0
    · show ((x 2 : Fcard ℵ₀) : Cardinal.{u}) < ℵ₀
      rw [h2]; exact Cardinal.natCast_lt_aleph0

theorem pt2_mem_ineq {m m' : ℕ} (h : m ≤ m') : pt2.{u} m m' ∈ ineqSystem.finSolutions :=
  (mem_finSolutions_ineqSystem_iff _).mpr ⟨m, m', h, rfl, rfl⟩

theorem pt3_mem_slack (a c : ℕ) : pt3.{u} a (a + c) c ∈ slackSystem.finSolutions :=
  (mem_finSolutions_slackSystem_iff' _).mpr ⟨a, c, rfl, rfl, rfl⟩

/-- **Example 3.17**: `ℵ₀H = {(0,0), (0,ℵ₀), (ℵ₀,ℵ₀)}`. -/
theorem example_3_17_alephPart_ineq :
    alephPart '' (ineqSystem.finSolutions : Set (Fin 2 → Fcard (ℵ₀ : Cardinal.{u})))
      = {x | (((x 0 : Fcard ℵ₀) : Cardinal.{u}), ((x 1 : Fcard ℵ₀) : Cardinal.{u})) ∈
          ({(0, 0), (0, ℵ₀), (ℵ₀, ℵ₀)} : Set (Cardinal.{u} × Cardinal.{u}))} := by
  ext x
  rw [LinSystem.mem_image_alephPart_iff]
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨h, hh, hx⟩
    obtain ⟨m, m', hmm, h0, h1⟩ := (mem_finSolutions_ineqSystem_iff h).mp hh
    rw [hx 0, hx 1, h0, h1]
    by_cases hm : m = 0
    · by_cases hm' : m' = 0 <;> simp [hm, hm']
    · have hm' : m' ≠ 0 := by omega
      simp [hm, hm']
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩)
    · exact ⟨pt2 0 0, pt2_mem_ineq le_rfl, forall_fin_two' (by simp [h0]) (by simp [h1])⟩
    · exact ⟨pt2 0 1, pt2_mem_ineq (by norm_num),
        forall_fin_two' (by simp [h0]) (by simp [h1])⟩
    · exact ⟨pt2 1 1, pt2_mem_ineq le_rfl, forall_fin_two' (by simp [h0]) (by simp [h1])⟩

/-- **Example 3.17**: `H + ℵ₀H = H ∪ {(n, ℵ₀) : n ∈ ℕ₀} ∪ {(ℵ₀, ℵ₀)}`. -/
theorem example_3_17_alephExt_ineq :
    (ineqSystem.alephExt : Set (Fin 2 → Fcard (ℵ₀ : Cardinal.{u})))
      = {x | (∃ m m' : ℕ, m ≤ m' ∧
              ((x 0 : Fcard ℵ₀) : Cardinal.{u}) = m ∧ ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = m') ∨
          (∃ m : ℕ, ((x 0 : Fcard ℵ₀) : Cardinal.{u}) = m ∧
              ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀) ∨
          (((x 0 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ ∧ ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀)} := by
  ext x
  rw [LinSystem.mem_alephExt_iff]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, hh, h', hh', hx⟩
    obtain ⟨m, m', hmm, h0, h1⟩ := (mem_finSolutions_ineqSystem_iff h).mp hh
    obtain ⟨l, l', hll, h0', h1'⟩ := (mem_finSolutions_ineqSystem_iff h').mp hh'
    rw [hx 0, hx 1, h0, h1, h0', h1']
    by_cases hl : l = 0
    · by_cases hl' : l' = 0
      · exact Or.inl ⟨m, m', hmm, by simp [hl], by simp [hl']⟩
      · exact Or.inr (Or.inl ⟨m, by simp [hl], by simp [hl']⟩)
    · have hl' : l' ≠ 0 := by omega
      exact Or.inr (Or.inr ⟨by simp [hl], by simp [hl']⟩)
  · rintro (⟨m, m', hmm, h0, h1⟩ | ⟨m, h0, h1⟩ | ⟨h0, h1⟩)
    · exact ⟨pt2 m m', pt2_mem_ineq hmm, pt2 0 0, pt2_mem_ineq le_rfl,
        forall_fin_two' (by simp [h0]) (by simp [h1])⟩
    · exact ⟨pt2 m m, pt2_mem_ineq le_rfl, pt2 0 1, pt2_mem_ineq (by norm_num),
        forall_fin_two' (by simp [h0]) (by simp [h1])⟩
    · exact ⟨pt2 0 0, pt2_mem_ineq le_rfl, pt2 1 1, pt2_mem_ineq le_rfl,
        forall_fin_two' (by simp [h0]) (by simp [h1])⟩

/-- **Example 3.17**: `ℵ₀H' = {(0,0,0), (0,ℵ₀,ℵ₀), (ℵ₀,ℵ₀,0), (ℵ₀,ℵ₀,ℵ₀)}`. -/
theorem example_3_17_alephPart_slack :
    alephPart '' (slackSystem.finSolutions : Set (Fin 3 → Fcard (ℵ₀ : Cardinal.{u})))
      = {x | (((x 0 : Fcard ℵ₀) : Cardinal.{u}), ((x 1 : Fcard ℵ₀) : Cardinal.{u}),
            ((x 2 : Fcard ℵ₀) : Cardinal.{u})) ∈
          ({(0, 0, 0), (0, ℵ₀, ℵ₀), (ℵ₀, ℵ₀, 0), (ℵ₀, ℵ₀, ℵ₀)} :
            Set (Cardinal.{u} × Cardinal.{u} × Cardinal.{u}))} := by
  ext x
  rw [LinSystem.mem_image_alephPart_iff]
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨h, hh, hx⟩
    obtain ⟨a, c, h0, h1, h2⟩ := (mem_finSolutions_slackSystem_iff' h).mp hh
    rw [hx 0, hx 1, hx 2, h0, h1, h2]
    by_cases ha : a = 0 <;> by_cases hc : c = 0 <;> simp [ha, hc]
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · exact ⟨pt3 0 (0 + 0) 0, pt3_mem_slack 0 0,
        forall_fin_three' (by simp [h0]) (by simp [h1]) (by simp [h2])⟩
    · exact ⟨pt3 0 (0 + 1) 1, pt3_mem_slack 0 1,
        forall_fin_three' (by simp [h0]) (by simp [h1]) (by simp [h2])⟩
    · exact ⟨pt3 1 (1 + 0) 0, pt3_mem_slack 1 0,
        forall_fin_three' (by simp [h0]) (by simp [h1]) (by simp [h2])⟩
    · exact ⟨pt3 1 (1 + 1) 1, pt3_mem_slack 1 1,
        forall_fin_three' (by simp [h0]) (by simp [h1]) (by simp [h2])⟩

/-- **Example 3.17**: `Ĥ' = H' + ℵ₀H' = H' ∪ {(n,ℵ₀,ℵ₀)} ∪ {(ℵ₀,ℵ₀,n)} ∪ {(ℵ₀,ℵ₀,ℵ₀)}`. -/
theorem example_3_17_alephExt_slack :
    (slackSystem.alephExt : Set (Fin 3 → Fcard (ℵ₀ : Cardinal.{u})))
      = {x | (∃ a c : ℕ, ((x 0 : Fcard ℵ₀) : Cardinal.{u}) = a ∧
              ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = ((a + c : ℕ) : Cardinal.{u}) ∧
              ((x 2 : Fcard ℵ₀) : Cardinal.{u}) = c) ∨
          (∃ m : ℕ, ((x 0 : Fcard ℵ₀) : Cardinal.{u}) = m ∧
              ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ ∧ ((x 2 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀) ∨
          (∃ m : ℕ, ((x 0 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ ∧
              ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ ∧ ((x 2 : Fcard ℵ₀) : Cardinal.{u}) = m) ∨
          (((x 0 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ ∧ ((x 1 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ ∧
              ((x 2 : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀)} := by
  ext x
  rw [LinSystem.mem_alephExt_iff]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, hh, h', hh', hx⟩
    obtain ⟨a, c, h0, h1, h2⟩ := (mem_finSolutions_slackSystem_iff' h).mp hh
    obtain ⟨a', c', h0', h1', h2'⟩ := (mem_finSolutions_slackSystem_iff' h').mp hh'
    rw [hx 0, hx 1, hx 2, h0, h1, h2, h0', h1', h2']
    by_cases ha : a' = 0 <;> by_cases hc : c' = 0
    · exact Or.inl ⟨a, c, by simp [ha], by simp [ha, hc], by simp [hc]⟩
    · exact Or.inr (Or.inl ⟨a, by simp [ha], by simp [ha, hc], by simp [hc]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, by simp [ha], by simp [ha, hc], by simp [hc]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by simp [ha], by simp [ha, hc], by simp [hc]⟩))
  · rintro (⟨a, c, h0, h1, h2⟩ | ⟨m, h0, h1, h2⟩ | ⟨m, h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · exact ⟨pt3 a (a + c) c, pt3_mem_slack a c, pt3 0 (0 + 0) 0, pt3_mem_slack 0 0,
        forall_fin_three' (by simp [h0]) (by simp [h1]) (by simp [h2])⟩
    · -- `(m, ℵ₀, ℵ₀) = (m, m, 0) + ℵ₀ (0, 1, 1)`
      exact ⟨pt3 m (m + 0) 0, pt3_mem_slack m 0, pt3 0 (0 + 1) 1, pt3_mem_slack 0 1,
        forall_fin_three' (by simp [h0]) (by simp [h1]) (by simp [h2])⟩
    · -- `(ℵ₀, ℵ₀, m) = (0, m, m) + ℵ₀ (1, 1, 0)`
      exact ⟨pt3 0 (0 + m) m, pt3_mem_slack 0 m, pt3 1 (1 + 0) 0, pt3_mem_slack 1 0,
        forall_fin_three' (by simp [h0]) (by simp [h1]) (by simp [h2])⟩
    · exact ⟨pt3 0 (0 + 0) 0, pt3_mem_slack 0 0, pt3 1 (1 + 1) 1, pt3_mem_slack 1 1,
        forall_fin_three' (by simp [h0]) (by simp [h1]) (by simp [h2])⟩

/-! ### The paper's pair of families -/

/-- `(0, 1) ∈ H`, on which the slack is `1`. -/
noncomputable def ptZeroOne :
    ↥(ineqSystem.finSolutions : Set (Fin 2 → Fcard (ℵ₀ : Cardinal.{u}))) :=
  ⟨pt2 0 1, pt2_mem_ineq (by norm_num)⟩

/-- `(1, 1) ∈ H`, on which the slack is `0`. -/
noncomputable def ptOneOne' :
    ↥(ineqSystem.finSolutions : Set (Fin 2 → Fcard (ℵ₀ : Cardinal.{u}))) :=
  ⟨pt2 1 1, pt2_mem_ineq le_rfl⟩

/-- The index carrying the exceptional term `(0, 1)`: the paper's `i = 0`. -/
noncomputable def idx0 : Idx (ℵ₀ : Cardinal.{u}) := Classical.choice (nonempty_Idx le_rfl)

open Classical in
/-- **Example 3.17**: the paper's family `(a_i) = (0,1), (1,1), (1,1), …`. -/
noncomputable def famA (i : Idx (ℵ₀ : Cardinal.{u})) :
    ↥(ineqSystem.finSolutions : Set (Fin 2 → Fcard (ℵ₀ : Cardinal.{u}))) :=
  if i = idx0 then ptZeroOne else ptOneOne'

/-- **Example 3.17**: the paper's family `(b_i) = (1,1), (1,1), …`. -/
noncomputable def famB (_ : Idx (ℵ₀ : Cardinal.{u})) :
    ↥(ineqSystem.finSolutions : Set (Fin 2 → Fcard (ℵ₀ : Cardinal.{u}))) :=
  ptOneOne'

/-- A countable sum in `F_{ℵ₀}` with infinitely many nonzero terms is `ℵ₀`. -/
theorem val_ksum_eq_aleph0 (z : Idx (ℵ₀ : Cardinal.{u}) → Fcard (ℵ₀ : Cardinal.{u}))
    (hz : {i | ((z i : Fcard ℵ₀) : Cardinal.{u}) ≠ 0}.Infinite) :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    ((KMonoid.ksum (κ := ℵ₀) z : Fcard ℵ₀) : Cardinal.{u}) = ℵ₀ := by
  let := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  refine le_antisymm (Fcard.le _) ?_
  show ℵ₀ ≤ Cardinal.sum fun i => ((z i : Fcard ℵ₀) : Cardinal.{u})
  exact (Cardinal.infinite_iff.mp hz.to_subtype).trans (Cardinal.mk_support_le_sum _)

/-- **Example 3.17**: the paper's families `a = (0,1), (1,1), (1,1), …` and `b = (1,1), (1,1), …`
both have `ℵ₀`-sum `(ℵ₀, ℵ₀)` — in `F_{ℵ₀}²`, hence in `H + ℵ₀H`, whose sums are computed there
(`IsKSubmonoid.coe_ksum`) — but they are **not** `ℵ₀⁻`-braided in `H`.  So `H + ℵ₀H` is not
braided over `H`.

Paper proof: a braiding would give `(l - 1, l) = u₀` and `(k, k) = v₁ + u₀`, forcing
`v₁ = (k - l + 1, k - l) ∉ H`.  The proof below uses instead the slack `δ(x, y) = y - x`, an
additive map `H → ℕ₀` (`not_isBraidedOver_ineqSystem`): along `b` the slack vanishes, so every
braiding term has slack `0`, whereas the piece of the braiding containing the `(0, 1)` of `a`
has slack at least `1`. -/
theorem example_3_17_families :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin 2 => Fcard ℵ₀) (le_refl ℵ₀)
    letI : AddCommMonoid ↥ineqSystem.finSolutions :=
      addCommMonoidOfClosed ineqSystem.addSubmonoid_finSolutions.1
        (fun a ha b hb => ineqSystem.addSubmonoid_finSolutions.2 a ha b hb)
    letI := LMonoid.ofAddCommMonoid ↥ineqSystem.finSolutions
    (KMonoid.ksum (κ := ℵ₀) fun i => ((famA.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀))
        = (fun _ => Fcard.mk ℵ₀ le_rfl) ∧
      (KMonoid.ksum (κ := ℵ₀) fun i =>
          ((famB.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀))
        = (fun _ => Fcard.mk ℵ₀ le_rfl) ∧
      ¬ IsBraided ℵ₀ famA.{u} famB.{u} := by
  let := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  let := KMonoid.pi ℵ₀ (fun _ : Fin 2 => Fcard ℵ₀) (le_refl ℵ₀)
  let : AddCommMonoid ↥ineqSystem.finSolutions :=
    addCommMonoidOfClosed ineqSystem.addSubmonoid_finSolutions.1
      (fun a ha b hb => ineqSystem.addSubmonoid_finSolutions.2 a ha b hb)
  let := LMonoid.ofAddCommMonoid ↥ineqSystem.finSolutions
  have : Infinite (Idx (ℵ₀ : Cardinal.{u})) := infinite_Idx le_rfl
  have hA : ∀ i, i ≠ idx0 → famA.{u} i = ptOneOne' := fun i hi => if_neg hi
  have hA0 : famA.{u} idx0 = ptZeroOne := if_pos rfl
  -- both families have nonzero components off `idx0`, so both sums are `(ℵ₀, ℵ₀)`
  have hAne : ∀ j : Fin 2, ∀ i, i ≠ idx0 →
      ((((famA.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀) j : Fcard ℵ₀)
        : Cardinal.{u}) ≠ 0 := by
    intro j i hi
    rw [hA i hi]
    refine forall_fin_two' (p := fun j => (((ptOneOne'.{u} : ↥ineqSystem.finSolutions)
      : Fin 2 → Fcard ℵ₀) j : Cardinal.{u}) ≠ 0) ?_ ?_ j <;> simp [ptOneOne']
  have hBne : ∀ j : Fin 2, ∀ i,
      ((((famB.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀) j : Fcard ℵ₀)
        : Cardinal.{u}) ≠ 0 := by
    intro j i
    refine forall_fin_two' (p := fun j => (((famB.{u} i : ↥ineqSystem.finSolutions)
      : Fin 2 → Fcard ℵ₀) j : Cardinal.{u}) ≠ 0) ?_ ?_ j <;> simp [famB, ptOneOne']
  refine ⟨funext fun j => Fcard.ext ?_, funext fun j => Fcard.ext ?_, ?_⟩
  · exact val_ksum_eq_aleph0 (fun i => ((famA.{u} i : ↥ineqSystem.finSolutions)
      : Fin 2 → Fcard ℵ₀) j) ((Set.finite_singleton idx0).infinite_compl.mono
        fun i hi => hAne j i hi)
  · exact val_ksum_eq_aleph0 (fun i => ((famB.{u} i : ↥ineqSystem.finSolutions)
      : Fin 2 → Fcard ℵ₀) j) (Set.infinite_univ.mono fun i _ => hBne j i)
  -- not braided: the slack `δ(x, y) = y - x` is an additive map `H → ℕ₀`
  intro hbr
  obtain ⟨B⟩ := hbr.symm
  set δ : ↥ineqSystem.finSolutions →+ ℕ :=
    { toFun := fun h => ineqSlack (h : Fin 2 → Fcard ℵ₀)
      map_zero' := ineqSlack_zero
      map_add' := fun a b => ineqSlack_add a.2 b.2 } with hδdef
  have hδ : ∀ h : ↥ineqSystem.finSolutions, δ h = ineqSlack (h : Fin 2 → Fcard ℵ₀) :=
    fun _ => rfl
  have hδB : ∀ i, δ (famB.{u} i) = 0 := fun i => by
    rw [hδ]; simp [famB, ptOneOne', ineqSlack]
  have hδA : δ (famA.{u} idx0) = 1 := by
    rw [hδ, hA0]; simp [ptZeroOne, ineqSlack]
  -- along `b` the slack vanishes, so every braiding term has slack `0`
  have hI : ∀ p, δ (B.v p) + δ (B.u p) = 0 := by
    intro p
    have h := (LMonoid.lsumOf_eq_finsum (B.I_lt p) famB).symm.trans (B.hI p)
    have h2 := congrArg δ h
    rw [AddMonoidHom.map_finsum_mem famB δ (Cardinal.lt_aleph0_iff_set_finite.mp (B.I_lt p)),
      map_add] at h2
    rw [← h2]
    simp [hδB]
  have hu : ∀ p, δ (B.u p) = 0 := fun p => by have := hI p; omega
  have hv : ∀ p, δ (B.v p) = 0 := fun p => by have := hI p; omega
  -- but the piece of `a` containing `(0, 1)` has slack at least `1`
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (B.J_cover ▸ Set.mem_univ idx0)
  have hJfin : (B.J p).Finite := Cardinal.lt_aleph0_iff_set_finite.mp (B.J_lt p)
  have hJ := (LMonoid.lsumOf_eq_finsum (B.J_lt p) famA).symm.trans (B.hJ p)
  have hJ2 := congrArg δ hJ
  rw [AddMonoidHom.map_finsum_mem famA δ hJfin, map_add, hu, hv, add_zero] at hJ2
  rw [show B.J p = insert idx0 (B.J p \ {idx0}) from
      (Set.insert_sdiff_singleton.trans (Set.insert_eq_self.mpr hp)).symm,
    finsum_mem_insert _ (by simp) (hJfin.sdiff)] at hJ2
  omega

/-! ### `Ĥ` via the slack variable -/

/-- **Example 3.17**, the composite statement: `Ĥ' = H' + ℵ₀H'`, pulled back along the
isomorphism `H ≅ H'`, `(a, b) ↦ (a, b, b - a)` (`example_3_17_slack_iso`), is `ℵ₀⁻`-braided over
`H = {(x, y) ∈ ℕ₀² : x ≤ y}`; so it is the universal `ℵ₀`-extension of `H`
(`isUniversalKExtension_slackSystem_alephExt`).

Paper proof: `H'` is cut out by an equation, so Proposition 3.15(2) identifies `Ĥ'` as
`H' + ℵ₀H'` (`prop_3_15_two_of_ineqs_empty`); a universal extension of a reduced monoid is braided
over it (`isBraidedOver_of_isUniversalKExtension`), and braidedness moves along the isomorphism of
bases (`IsBraidedOver.of_base_iso`). -/
theorem isBraidedOver_slackSystem_alephExt :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin 2 => Fcard ℵ₀) (le_refl ℵ₀)
    letI := KMonoid.pi ℵ₀ (fun _ : Fin 3 => Fcard ℵ₀) (le_refl ℵ₀)
    letI : AddCommMonoid ↥ineqSystem.finSolutions :=
      addCommMonoidOfClosed ineqSystem.addSubmonoid_finSolutions.1
        (fun a ha b hb => ineqSystem.addSubmonoid_finSolutions.2 a ha b hb)
    letI := LMonoid.ofAddCommMonoid ↥ineqSystem.finSolutions
    letI := slackSystem.isKSubmonoid_alephExt.kmonoid
    IsBraidedOver ℵ₀ ℵ₀ ↥ineqSystem.finSolutions ↥slackSystem.alephExt (Order.le_succ ℵ₀)
      (fun h => ⟨toSlack (h : Fin 2 → Fcard ℵ₀), ⟨toSlack (h : Fin 2 → Fcard ℵ₀),
        toSlack_mem h.2, 0, slackSystem.addSubmonoid_finSolutions.1,
        by rw [alephPart_zero, add_zero]⟩⟩) := by
  let : AddCommMonoid ↥ineqSystem.finSolutions :=
    addCommMonoidOfClosed ineqSystem.addSubmonoid_finSolutions.1
      (fun a ha b hb => ineqSystem.addSubmonoid_finSolutions.2 a ha b hb)
  let := LMonoid.ofAddCommMonoid ↥ineqSystem.finSolutions
  let : AddCommMonoid ↥slackSystem.finSolutions :=
    addCommMonoidOfClosed slackSystem.addSubmonoid_finSolutions.1
      (fun a ha b hb => slackSystem.addSubmonoid_finSolutions.2 a ha b hb)
  let := LMonoid.ofAddCommMonoid ↥slackSystem.finSolutions
  let := slackSystem.isKSubmonoid_alephExt.kmonoid
  -- `H'` is reduced, being a submonoid of `F_{ℵ₀}³`
  have hcon : IsConical ↥slackSystem.finSolutions :=
    LMonoid.isConical_of_injective (lam := ℵ₀) (κ := ℵ₀)
      (X := ↥slackSystem.finSolutions) (H := Fin 3 → Fcard ℵ₀)
      (fun h => (h : Fin 3 → Fcard ℵ₀)) (fun _ _ h => Subtype.ext h) rfl fun _ _ => rfl
  -- Proposition 3.15(2) for `H'`, read as a braiding
  have hbr' := isBraidedOver_of_isUniversalKExtension Cardinal.isRegular_aleph0
    (Order.le_succ ℵ₀) hcon (prop_3_15_two_of_ineqs_empty slackSystem slackSystem_ineqs)
  -- the isomorphism `H ≅ H'` and its inverse, as `ℵ₀⁻`-homomorphisms
  have hg : IsLMonoidHom (ℵ₀ : Cardinal.{u}) (fun x : ↥ineqSystem.finSolutions =>
      (⟨toSlack (x : Fin 2 → Fcard ℵ₀), toSlack_mem x.2⟩ : ↥slackSystem.finSolutions)) :=
    isLMonoidHom_aleph0_of_add (g := fun x : ↥ineqSystem.finSolutions =>
      (⟨toSlack (x : Fin 2 → Fcard ℵ₀), toSlack_mem x.2⟩ : ↥slackSystem.finSolutions))
      (map_zero example_3_17_slack_iso.{u}) (map_add example_3_17_slack_iso.{u})
  have hg' : IsLMonoidHom (ℵ₀ : Cardinal.{u}) (fun y : ↥slackSystem.finSolutions =>
      (⟨ofSlack (y : Fin 3 → Fcard ℵ₀), ofSlack_mem y.2⟩ : ↥ineqSystem.finSolutions)) :=
    isLMonoidHom_aleph0_of_add (g := fun y : ↥slackSystem.finSolutions =>
      (⟨ofSlack (y : Fin 3 → Fcard ℵ₀), ofSlack_mem y.2⟩ : ↥ineqSystem.finSolutions))
      (map_zero example_3_17_slack_iso.{u}.symm) (map_add example_3_17_slack_iso.{u}.symm)
  exact hbr'.of_base_iso (Order.le_succ ℵ₀)
    (g := fun x : ↥ineqSystem.finSolutions =>
      (⟨toSlack (x : Fin 2 → Fcard ℵ₀), toSlack_mem x.2⟩ : ↥slackSystem.finSolutions))
    (g' := fun y : ↥slackSystem.finSolutions =>
      (⟨ofSlack (y : Fin 3 → Fcard ℵ₀), ofSlack_mem y.2⟩ : ↥ineqSystem.finSolutions)) hg hg'
    (fun x => Subtype.ext (ofSlack_toSlack _))
    (fun y => Subtype.ext (toSlack_ofSlack y.2))

/-- **Example 3.17**: `Ĥ ≅ Ĥ' = H' + ℵ₀H'`, i.e. `slackSystem.alephExt`, along
`(a, b) ↦ (a, b, b - a)`, is the universal `ℵ₀`-extension of `H = {(x, y) ∈ ℕ₀² : x ≤ y}` — tested
against `ℵ₀`-monoids in every universe `t`. -/
theorem isUniversalKExtension_slackSystem_alephExt :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin 2 => Fcard ℵ₀) (le_refl ℵ₀)
    letI := KMonoid.pi ℵ₀ (fun _ : Fin 3 => Fcard ℵ₀) (le_refl ℵ₀)
    letI : AddCommMonoid ↥ineqSystem.finSolutions :=
      addCommMonoidOfClosed ineqSystem.addSubmonoid_finSolutions.1
        (fun a ha b hb => ineqSystem.addSubmonoid_finSolutions.2 a ha b hb)
    letI := LMonoid.ofAddCommMonoid ↥ineqSystem.finSolutions
    letI := slackSystem.isKSubmonoid_alephExt.kmonoid
    IsUniversalKExtension.{u, u + 1, u + 1, t} ℵ₀ ℵ₀ ↥ineqSystem.finSolutions
      ↥slackSystem.alephExt (Order.le_succ ℵ₀)
      (fun h => ⟨toSlack (h : Fin 2 → Fcard ℵ₀), ⟨toSlack (h : Fin 2 → Fcard ℵ₀),
        toSlack_mem h.2, 0, slackSystem.addSubmonoid_finSolutions.1,
        by rw [alephPart_zero, add_zero]⟩⟩) := by
  let : AddCommMonoid ↥ineqSystem.finSolutions :=
    addCommMonoidOfClosed ineqSystem.addSubmonoid_finSolutions.1
      (fun a ha b hb => ineqSystem.addSubmonoid_finSolutions.2 a ha b hb)
  let := LMonoid.ofAddCommMonoid ↥ineqSystem.finSolutions
  let := slackSystem.isKSubmonoid_alephExt.kmonoid
  exact isBraidedOver_slackSystem_alephExt.isUniversalKExtension (Order.le_succ ℵ₀)

/-- **Example 3.17**, the closing sentence: in `Ĥ'` the `ℵ₀`-sum of the slack form of `(a_i)` is
`(ℵ₀, ℵ₀, 1)`, that of `(b_i)` is `(ℵ₀, ℵ₀, 0)`; so `Ĥ` distinguishes the two non-braided
families. -/
theorem example_3_17_slack_sums :
    letI := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
    letI := KMonoid.pi ℵ₀ (fun _ : Fin 3 => Fcard ℵ₀) (le_refl ℵ₀)
    (∀ j : Fin 3, (((KMonoid.ksum (κ := ℵ₀) fun i =>
        toSlack ((famA.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀)) j : Fcard ℵ₀)
          : Cardinal.{u}) = if j = 2 then 1 else ℵ₀) ∧
    (∀ j : Fin 3, (((KMonoid.ksum (κ := ℵ₀) fun i =>
        toSlack ((famB.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀)) j : Fcard ℵ₀)
          : Cardinal.{u}) = if j = 2 then 0 else ℵ₀) := by
  let := Fcard.instKMonoid (le_refl (ℵ₀ : Cardinal.{u}))
  let := KMonoid.pi ℵ₀ (fun _ : Fin 3 => Fcard ℵ₀) (le_refl ℵ₀)
  have : Infinite (Idx (ℵ₀ : Cardinal.{u})) := infinite_Idx le_rfl
  have hA : ∀ i, i ≠ idx0 → famA.{u} i = ptOneOne' := fun i hi => if_neg hi
  have hA0 : famA.{u} idx0 = ptZeroOne := if_pos rfl
  have hinf : ({idx0.{u}}ᶜ : Set (Idx (ℵ₀ : Cardinal.{u}))).Infinite :=
    (Set.finite_singleton _).infinite_compl
  refine ⟨forall_fin_three' ?_ ?_ ?_, forall_fin_three' ?_ ?_ ?_⟩
  · rw [if_neg (by decide)]
    show ((KMonoid.ksum (κ := ℵ₀) fun i =>
      toSlack ((famA.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀) 0 : Fcard ℵ₀)
        : Cardinal.{u}) = ℵ₀
    refine val_ksum_eq_aleph0 _ (hinf.mono fun i hi => ?_)
    rw [Set.mem_ofPred_eq, hA i hi]
    simp [toSlack, ptOneOne']
  · rw [if_neg (by decide)]
    show ((KMonoid.ksum (κ := ℵ₀) fun i =>
      toSlack ((famA.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀) 1 : Fcard ℵ₀)
        : Cardinal.{u}) = ℵ₀
    refine val_ksum_eq_aleph0 _ (hinf.mono fun i hi => ?_)
    rw [Set.mem_ofPred_eq, hA i hi]
    simp [toSlack, ptOneOne']
  · rw [if_pos rfl]
    show ((KMonoid.ksum (κ := ℵ₀) fun i =>
      toSlack ((famA.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀) 2 : Fcard ℵ₀)
        : Cardinal.{u}) = 1
    have hx : ∀ i, i ≠ idx0 →
        toSlack ((famA.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀) 2 = 0 := by
      intro i hi
      refine fcard_eq_zero_of_val ?_
      rw [hA i hi]
      simp [toSlack, ptOneOne', ineqSlack]
    rw [KMonoid.ksum_single idx0 _ hx, hA0]
    simp [toSlack, ptZeroOne, ineqSlack]
  · rw [if_neg (by decide)]
    show ((KMonoid.ksum (κ := ℵ₀) fun i =>
      toSlack ((famB.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀) 0 : Fcard ℵ₀)
        : Cardinal.{u}) = ℵ₀
    refine val_ksum_eq_aleph0 _ (Set.infinite_univ.mono fun i _ => ?_)
    simp [famB, toSlack, ptOneOne']
  · rw [if_neg (by decide)]
    show ((KMonoid.ksum (κ := ℵ₀) fun i =>
      toSlack ((famB.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀) 1 : Fcard ℵ₀)
        : Cardinal.{u}) = ℵ₀
    refine val_ksum_eq_aleph0 _ (Set.infinite_univ.mono fun i _ => ?_)
    simp [famB, toSlack, ptOneOne']
  · rw [if_pos rfl]
    show ((KMonoid.ksum (κ := ℵ₀) fun i =>
      toSlack ((famB.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀) 2 : Fcard ℵ₀)
        : Cardinal.{u}) = 0
    have hx : (fun i => toSlack ((famB.{u} i : ↥ineqSystem.finSolutions) : Fin 2 → Fcard ℵ₀) 2)
        = fun _ => 0 :=
      funext fun i => fcard_eq_zero_of_val (by simp [famB, toSlack, ptOneOne', ineqSlack])
    rw [hx, KMonoid.ksum_zero, Fcard.instKMonoid_zero]

end DiophantineExtra

end KappaMonoid
