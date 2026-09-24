/-
Section 2.1 of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*.

Proposition 2.9: the free `κ`-monoid `F_κ(B)` on a set `B`, together with the analogue for
`λ⁻`-monoids asserted at the end of §2.4.  Both are the same construction inside the product
`F_{λ⁻}^B` of `KappaMonoid.LCard`, so everything is proved once at the `λ⁻` level and
specialised by `λ = κ⁺`.

Regularity of `λ` is carried as `[Fact lam.IsRegular]`, so that `F_{λ⁻}`, the product `F_{λ⁻}^B`
and `F_{λ⁻}(B)` are `λ⁻`-monoids by instance search rather than by hand at every statement.
-/
import KappaMonoid.Core.Cardinal

universe u v

open Cardinal Function Set
open scoped Classical

namespace KappaMonoid

/-! ## The `λ⁻`-monoids `F_{λ⁻}` and `F_{λ⁻}^B` as instances -/

namespace LCard

/-- `F_{λ⁻}` is a `λ⁻`-monoid whenever `λ` is known to be regular. -/
@[instance_reducible]
noncomputable instance instLMonoidOfFact (lam : Cardinal.{u}) [h : Fact lam.IsRegular] :
    LMonoid lam (LCard lam) := instLMonoid h.out

end LCard

/-- `F_{λ⁻}^B` is a `λ⁻`-monoid, with coordinatewise summation. -/
@[instance_reducible]
noncomputable instance instLMonoidPi (lam : Cardinal.{u}) [h : Fact lam.IsRegular] (B : Type u) :
    LMonoid lam (B → LCard lam) := LMonoid.pi lam (fun _ : B => LCard lam) h.out

/-! ## The support of a family of cardinals

`F_{λ⁻}(B)` is cut out of `F_{λ⁻}^B` by a condition on supports.  The support is defined by the
condition `(x b : Cardinal) ≠ 0` rather than through `Function.support`, so that it does not
depend on the `λ⁻`-monoid structure. -/

variable {lam : Cardinal.{u}} {B : Type u}

/-- The support of a family of cardinals: the indices at which it is nonzero. -/
def csupport (x : B → LCard lam) : Set B := {b | (x b : Cardinal.{u}) ≠ 0}

theorem mem_csupport {x : B → LCard lam} {b : B} :
    b ∈ csupport x ↔ (x b : Cardinal.{u}) ≠ 0 := Iff.rfl

theorem notMem_csupport {x : B → LCard lam} {b : B} :
    b ∉ csupport x ↔ (x b : Cardinal.{u}) = 0 := by
  rw [mem_csupport, not_not]

/-! ## `F_{λ⁻}(B)` and `F_κ(B)` -/

/-- `F_{λ⁻}(B)`, the free `λ⁻`-monoid on `B`: the families of cardinals `< λ` indexed by `B`
whose support has cardinality `< λ`. -/
def FreeL (lam : Cardinal.{u}) (B : Type u) : Set (B → LCard lam) := {x | #(csupport x) < lam}

/-- `F_κ(B)`, the free `κ`-monoid on `B` (Proposition 2.9): the families of cardinals `≤ κ`
indexed by `B` whose support has cardinality `≤ κ`. -/
abbrev FreeK (κ : Cardinal.{u}) (B : Type u) : Set (B → Fcard κ) := FreeL (Order.succ κ) B

theorem mem_FreeL {x : B → LCard lam} : x ∈ FreeL lam B ↔ #(csupport x) < lam := Iff.rfl

theorem mk_csupport_lt [Fact lam.IsRegular] (x : ↥(FreeL lam B)) :
    #(csupport (x : B → LCard lam)) < lam := x.2

/-- Every family indexed by a basis of size `< λ` lies in `F_{λ⁻}(B)`: its support is a subset of
the basis. -/
theorem mem_FreeL_of_mk_lt (hB : #B < lam) (x : B → LCard lam) : x ∈ FreeL lam B :=
  lt_of_le_of_lt (Cardinal.mk_set_le _) hB

/-- **After Proposition 2.9**: when `#B ≤ κ`, `F_κ(B) = F_κ^B` — every family of cardinals `≤ κ`
indexed by `B` lies in the free `κ`-monoid on `B`. -/
theorem FreeK_eq_univ {κ : Cardinal.{u}} (hB : #B ≤ κ) : FreeK κ B = Set.univ :=
  Set.eq_univ_of_forall fun x => mem_FreeL_of_mk_lt (Order.lt_succ_iff.mpr hB) x

/-! ## Proposition 2.9(1): `F_{λ⁻}(B)` is a `λ⁻`-submonoid of `F_{λ⁻}^B` -/

/-- The support of a sum is contained in the union of the supports: a coordinate of the sum is a
cardinal sum, and a cardinal sum vanishes exactly when every term does. -/
theorem csupport_lsumOf_subset [Fact lam.IsRegular] {ι : Type u} (h : #ι < lam)
    (x : ι → B → LCard lam) :
    csupport (LMonoid.lsumOf (lam := lam) h x) ⊆ ⋃ i, csupport (x i) := by
  intro b hb
  by_contra hcon
  refine hb ?_
  have hzero : ∀ i, ((x i b : LCard lam) : Cardinal.{u}) = 0 := fun i =>
    notMem_csupport.mp fun hmem => hcon (Set.mem_iUnion.mpr ⟨i, hmem⟩)
  show ((LMonoid.lsumOf (lam := lam) h x b : LCard lam) : Cardinal.{u}) = 0
  show (Cardinal.sum fun i => ((x i b : LCard lam) : Cardinal.{u})) = 0
  rw [funext hzero, Cardinal.sum_const', mul_zero]

/-- **Proposition 2.9(1)**: `F_{λ⁻}(B)` is a `λ⁻`-submonoid of `F_{λ⁻}^B`.

Paper proof: the support of `Σ_i x_i` is contained in `⋃_i supp(x_i)`, which by regularity of `λ`
is a union of `< λ` many sets of size `< λ`, hence of size `< λ`. -/
theorem isLSubmonoid_FreeL [h : Fact lam.IsRegular] : IsLSubmonoid lam (FreeL lam B) := by
  constructor
  · have hz : csupport (0 : B → LCard lam) = (∅ : Set B) := by
      ext b
      rw [mem_csupport, Set.mem_empty_iff_false, iff_false, not_not]
      exact LCard.val_zero h.out
    show #(csupport (0 : B → LCard lam)) < lam
    rw [hz, Cardinal.mk_eq_zero]
    exact h.out.pos
  · intro ι hι x hx
    show #(csupport (LMonoid.lsumOf (lam := lam) hι x)) < lam
    refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset (csupport_lsumOf_subset hι x)) ?_
    exact lt_of_le_of_lt Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_lt_of_isRegular h.out hι fun i => hx i)

/-- `F_{λ⁻}(B)` is a `λ⁻`-monoid. -/
@[instance_reducible]
noncomputable instance instLMonoidFreeL (lam : Cardinal.{u}) [Fact lam.IsRegular] (B : Type u) :
    LMonoid lam ↥(FreeL lam B) := isLSubmonoid_FreeL.lmonoid

/-- `F_κ(B)` is a `κ`-submonoid of `F_κ^B` (Proposition 2.9(1)). -/
theorem isKSubmonoid_FreeK {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) :
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    letI := Fcard.instKMonoid hκ
    letI := KMonoid.pi κ (fun _ : B => Fcard κ) hκ
    KMonoid.IsKSubmonoid κ (FreeK κ B) := by
  let : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  let := Fcard.instKMonoid hκ
  let := KMonoid.pi κ (fun _ : B => Fcard κ) hκ
  exact ⟨isLSubmonoid_FreeL.zero_mem, fun x hx =>
    isLSubmonoid_FreeL.lsumOf_mem (KMonoid.lt_succ (le_of_eq (mk_Idx κ))) x hx⟩

/-! ## The generators `ι(b)` -/

variable [hfact : Fact lam.IsRegular]

theorem one_lt : (1 : Cardinal.{u}) < lam := lt_of_lt_of_le one_lt_aleph0 hfact.out.aleph0_le

/-- The family with value `1` at `b` and `0` elsewhere. -/
noncomputable def iotaFun (b : B) : B → LCard lam := fun b' =>
  if b' = b then ⟨1, one_lt⟩ else ⟨0, hfact.out.pos⟩

@[simp] theorem val_iotaFun_self (b : B) :
    ((iotaFun (lam := lam) b b : LCard lam) : Cardinal.{u}) = 1 := by simp [iotaFun]

theorem val_iotaFun_of_ne {b b' : B} (h : b' ≠ b) :
    ((iotaFun (lam := lam) b b' : LCard lam) : Cardinal.{u}) = 0 := by simp [iotaFun, h]

theorem csupport_iotaFun (b : B) : csupport (iotaFun (lam := lam) b) = ({b} : Set B) := by
  ext b'
  rw [mem_csupport, Set.mem_singleton_iff]
  by_cases h : b' = b
  · subst h; simp
  · simp [val_iotaFun_of_ne (lam := lam) h, h]

/-- The map `ι : B → F_{λ⁻}(B)` of §2.1. -/
noncomputable def iota (b : B) : ↥(FreeL lam B) :=
  ⟨iotaFun b, by
    show #(csupport (iotaFun (lam := lam) b)) < lam
    rw [csupport_iotaFun, Cardinal.mk_singleton]
    exact one_lt⟩

@[simp] theorem coe_iota (b : B) : ((iota (lam := lam) b : ↥(FreeL lam B)) : B → LCard lam)
    = iotaFun b := rfl

/-! ## Proposition 2.9(2): the universal property

For `f : B → X` into a `λ⁻`-monoid, `lift f` is the map `x ↦ Σ_b λ_b f(b)` of the paper.  The sum
is taken over the support of `x`, but `lift_eq_of_subset` shows that any small superset of the
support gives the same value; that is what makes the homomorphism property provable, since it
lets both sides of the equation be summed over one common index set. -/

variable {X : Type v} [LMonoid lam X]

/-- The summand `λ_b · f(b)` of `Σ_b λ_b f(b)`. -/
noncomputable def term (f : B → X) (x : B → LCard lam) (b : B) : X :=
  LMonoid.lcmul (lam := lam) ((x b : LCard lam) : Cardinal.{u}) (x b).2 (f b)

omit hfact in
theorem term_def (f : B → X) (x : B → LCard lam) (b : B) :
    term f x b = LMonoid.lcmul (lam := lam) ((x b : LCard lam) : Cardinal.{u}) (x b).2 (f b) := rfl

theorem term_eq_zero {f : B → X} {x : B → LCard lam} {b : B} (h : (x b : Cardinal.{u}) = 0) :
    term f x b = 0 := by
  rw [term_def, LMonoid.lcmul_congr h _ hfact.out.pos, LMonoid.lcmul_zero_cardinal]

/-- The homomorphism `F_{λ⁻}(B) → X` extending `f : B → X`, namely `x ↦ Σ_b λ_b f(b)`. -/
noncomputable def lift (f : B → X) (x : ↥(FreeL lam B)) : X :=
  LMonoid.lsumOf (lam := lam) x.2 fun b : csupport (x : B → LCard lam) =>
    term f (x : B → LCard lam) (b : B)

omit hfact in
theorem lift_def (f : B → X) (x : ↥(FreeL lam B)) :
    lift f x = LMonoid.lsumOf (lam := lam) x.2 fun b : csupport (x : B → LCard lam) =>
      term f (x : B → LCard lam) (b : B) := rfl

/-- `lift f` may be computed over any small set containing the support: the extra terms are
`0 · f(b) = 0`. -/
theorem lift_eq_of_subset (f : B → X) (x : ↥(FreeL lam B)) {S : Set B} (hS : #S < lam)
    (hsub : csupport (x : B → LCard lam) ⊆ S) :
    lift f x = LMonoid.lsumOf (lam := lam) hS fun b : S => term f (x : B → LCard lam) (b : B) :=
  (LMonoid.lsumOf_of_subset hS x.2 hsub (term f (x : B → LCard lam)) fun _b _ hb =>
    term_eq_zero (notMem_csupport.mp hb)).symm

/-- **Proposition 2.9(2)**, existence: `lift f` extends `f` along `ι`. -/
@[simp] theorem lift_iota (f : B → X) (b : B) : lift f (iota (lam := lam) b) = f b := by
  have hsing : #({b} : Set B) < lam := by rw [Cardinal.mk_singleton]; exact one_lt
  have hsub : csupport ((iota (lam := lam) b : ↥(FreeL lam B)) : B → LCard lam) ⊆ ({b} : Set B) :=
    le_of_eq (csupport_iotaFun b)
  rw [lift_eq_of_subset f (iota b) hsing hsub]
  let : Unique ↥({b} : Set B) := Set.uniqueSingleton b
  rw [LMonoid.lsumOf_unique]
  have hdef : ((default : ↥({b} : Set B)) : B) = b := rfl
  rw [term_def, hdef,
    LMonoid.lcmul_congr
      (show (((iota (lam := lam) b : ↥(FreeL lam B)) : B → LCard lam) b : Cardinal.{u}) = 1 from
        val_iotaFun_self b) _ one_lt,
    LMonoid.lcmul_one]

/-- The `b`-th summand of a sum is the sum of the `b`-th summands: this is Lemma 2.7(2). -/
theorem term_lsumOf {ι : Type u} (h : #ι < lam) (f : B → X) (z : ι → B → LCard lam) (b : B) :
    term f (LMonoid.lsumOf (lam := lam) h z) b
      = LMonoid.lsumOf (lam := lam) h fun i => term f (z i) b :=
  LMonoid.lcmul_lsumOf_cardinal h (fun i => ((z i b : LCard lam) : Cardinal.{u}))
    (fun i => (z i b).2) _ (f b)

/-- **Proposition 2.9(2)**, existence: `lift f` is a homomorphism of `λ⁻`-monoids.

Paper proof: `f̄(Σ_i x_i) = Σ_b (Σ_i λ_{i,b}) f(b) = Σ_b Σ_i λ_{i,b} f(b) = Σ_i Σ_b λ_{i,b} f(b)
= Σ_i f̄(x_i)`, using Lemma 2.7(2) and (A4).  All four sums over `b` run over one set `S`, the
union of the supports, which is legitimate by `lift_eq_of_subset`. -/
theorem isLMonoidHom_lift (f : B → X) :
    IsLMonoidHom lam (lift (lam := lam) (B := B) (X := X) f) := by
  intro ι h y
  have hS : #(⋃ i, csupport ((y i : ↥(FreeL lam B)) : B → LCard lam)) < lam :=
    lt_of_le_of_lt Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_lt_of_isRegular hfact.out h fun i => (y i).2)
  have hsubi : ∀ i, csupport ((y i : ↥(FreeL lam B)) : B → LCard lam)
      ⊆ ⋃ i, csupport ((y i : ↥(FreeL lam B)) : B → LCard lam) := fun i =>
    Set.subset_iUnion (fun i => csupport ((y i : ↥(FreeL lam B)) : B → LCard lam)) i
  have hsum : csupport ((LMonoid.lsumOf (lam := lam) h y : ↥(FreeL lam B)) : B → LCard lam)
      ⊆ ⋃ i, csupport ((y i : ↥(FreeL lam B)) : B → LCard lam) :=
    csupport_lsumOf_subset h fun i => ((y i : ↥(FreeL lam B)) : B → LCard lam)
  rw [lift_eq_of_subset f _ hS hsum,
    show (fun b : ↥(⋃ i, csupport ((y i : ↥(FreeL lam B)) : B → LCard lam)) =>
          term f ((LMonoid.lsumOf (lam := lam) h y : ↥(FreeL lam B)) : B → LCard lam) (b : B))
        = fun b : ↥(⋃ i, csupport ((y i : ↥(FreeL lam B)) : B → LCard lam)) =>
          LMonoid.lsumOf (lam := lam) h fun i =>
            term f ((y i : ↥(FreeL lam B)) : B → LCard lam) (b : B) from
      funext fun b => term_lsumOf h f _ (b : B),
    LMonoid.lsumOf_comm hS h]
  congr 1
  funext i
  exact (lift_eq_of_subset f (y i) hS (hsubi i)).symm

/-! ### Uniqueness

Every `x ∈ F_{λ⁻}(B)` is `Σ_{b ∈ supp x} λ_b · ι(b)`; equivalently, `lift ι` is the identity.
Uniqueness of the extension follows by applying a homomorphism to that representation. -/

/-- The `b'`-coordinate of the `b`-th summand of `lift ι`: `λ_b · ι(b)` has coordinate
`λ_b · [b = b']`. -/
theorem val_term_iota_apply (x : B → LCard lam) (b b' : B) :
    ((((term (iota (lam := lam)) x b : ↥(FreeL lam B)) : B → LCard lam) b' : LCard lam) :
        Cardinal.{u})
      = (x b : Cardinal.{u}) * ((iotaFun (lam := lam) b b' : LCard lam) : Cardinal.{u}) :=
  LCard.val_lcmul hfact.out _ (x b).2 _

/-- The value of `lift ι x` at `b'`: the sum collapses to its `b'`-th term. -/
theorem lift_iota_apply (x : ↥(FreeL lam B)) (b' : B) :
    ((lift (lam := lam) (X := ↥(FreeL lam B)) iota x : ↥(FreeL lam B)) : B → LCard lam) b'
      = (x : B → LCard lam) b' := by
  -- the coordinate of a sum in `F_{λ⁻}(B)` is the sum of the coordinates
  have key : ((lift (lam := lam) (X := ↥(FreeL lam B)) iota x : ↥(FreeL lam B)) : B → LCard lam) b'
      = LMonoid.lsumOf (lam := lam) x.2 (fun b : csupport (x : B → LCard lam) =>
          ((term (iota (lam := lam)) (x : B → LCard lam) (b : B) : ↥(FreeL lam B)) :
            B → LCard lam) b') := rfl
  -- off the diagonal every coordinate vanishes, since `ι(b)` is `0` at `b' ≠ b`
  have hzero : ∀ b ∈ csupport (x : B → LCard lam), b ≠ b' →
      ((term (iota (lam := lam)) (x : B → LCard lam) b : ↥(FreeL lam B)) : B → LCard lam) b'
        = (0 : LCard lam) := by
    intro b _ hb
    apply Subtype.ext
    rw [val_term_iota_apply, val_iotaFun_of_ne (lam := lam) (Ne.symm hb), mul_zero,
      LCard.val_zero hfact.out]
  rw [key]
  by_cases hmem : b' ∈ csupport (x : B → LCard lam)
  · -- restrict the sum to the singleton `{b'}` inside the support
    have hsing : #({b'} : Set B) < lam := by rw [Cardinal.mk_singleton]; exact one_lt
    have hsub : ({b'} : Set B) ⊆ csupport (x : B → LCard lam) := by rintro c rfl; exact hmem
    rw [LMonoid.lsumOf_of_subset x.2 hsing hsub _ hzero]
    let : Unique ↥({b'} : Set B) := Set.uniqueSingleton b'
    rw [LMonoid.lsumOf_unique]
    apply Subtype.ext
    have hdef : ((default : ↥({b'} : Set B)) : B) = b' := rfl
    rw [val_term_iota_apply, hdef, val_iotaFun_self, mul_one]
  · -- every term vanishes at `b'`
    apply Subtype.ext
    rw [LMonoid.lsumOf_eq_zero_of_forall x.2
      (fun b => hzero (b : B) b.2 fun hc => hmem (hc ▸ b.2)), LCard.val_zero hfact.out,
      notMem_csupport.mp hmem]

/-- Every element of `F_{λ⁻}(B)` is the sum of its coordinates times the generators. -/
theorem lift_iota_eq_self (x : ↥(FreeL lam B)) :
    lift (lam := lam) (X := ↥(FreeL lam B)) iota x = x :=
  Subtype.ext (funext fun b' => lift_iota_apply x b')

/-- **Proposition 2.9(2)**, uniqueness: a homomorphism out of `F_{λ⁻}(B)` is determined by its
values on the generators. -/
theorem hom_ext {g₁ g₂ : ↥(FreeL lam B) → X} (h₁ : IsLMonoidHom lam g₁)
    (h₂ : IsLMonoidHom lam g₂) (h : ∀ b, g₁ (iota b) = g₂ (iota b)) : g₁ = g₂ := by
  funext x
  have key : ∀ g : ↥(FreeL lam B) → X, IsLMonoidHom lam g →
      g x = LMonoid.lsumOf (lam := lam) x.2 fun b : csupport (x : B → LCard lam) =>
        LMonoid.lcmul (lam := lam) (((x : B → LCard lam) (b : B) : LCard lam) : Cardinal.{u})
          ((x : B → LCard lam) (b : B)).2 (g (iota (b : B))) := by
    intro g hg
    conv_lhs => rw [← lift_iota_eq_self x]
    rw [lift_def, hg x.2]
    congr 1
    funext b
    exact hg.map_lcmul _ (iota (b : B))
  rw [key g₁ h₁, key g₂ h₂]
  congr 1
  funext b
  rw [h (b : B)]

/-- **Proposition 2.9(2)**: `F_{λ⁻}(B)` is the free `λ⁻`-monoid on `B`.  For every `λ⁻`-monoid `X`
and every map `f : B → X` there is a unique homomorphism `F_{λ⁻}(B) → X` extending `f`. -/
theorem exists_unique_lift (f : B → X) :
    ∃! g : ↥(FreeL lam B) → X, IsLMonoidHom lam g ∧ ∀ b, g (iota b) = f b :=
  ⟨lift f, ⟨isLMonoidHom_lift f, lift_iota f⟩, fun _g hg =>
    hom_ext hg.1 (isLMonoidHom_lift f) fun b => (hg.2 b).trans (lift_iota f b).symm⟩

/-- `F_{λ⁻}(B)` is generated by the image of `ι`: that is `lift_iota_eq_self` again, read as a
statement about the `λ⁻`-submonoid generated by the `ι(b)`. -/
theorem lsumOf_mem_of_forall_mem {S : Set ↥(FreeL lam B)} (hS : IsLSubmonoid lam S)
    {ι : Type u} (h : #ι < lam) {y : ι → ↥(FreeL lam B)} (hy : ∀ i, y i ∈ S) :
    LMonoid.lsumOf (lam := lam) h y ∈ S := hS.lsumOf_mem h y hy

end KappaMonoid

/-! ## Definition 2.10 in the paper's form

The paper defines `α`-generated by the existence of a surjection from `F_κ(B)` with `#B ≤ α`, and
observes that it is equivalent to the existence of `α` many generators — which is how
`KMonoid.IsAlphaGenerated` is stated.  Here the two are identified. -/

namespace KappaMonoid

open KMonoid

variable {κ : Cardinal.{u}} {B : Type u}

/-- `F_κ(B)` is a `κ`-monoid. -/
@[instance_reducible]
noncomputable def instKMonoidFreeK (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (B : Type u) :
    KMonoid κ ↥(FreeK κ B) :=
  letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  { toLMonoid := instLMonoidFreeL (Order.succ κ) B
    aleph0_le := hκ }

/-- A `λ⁻`-homomorphism at `λ = κ⁺` is a `κ`-homomorphism. -/
theorem isKHom_of_isLMonoidHom {H : Type v} [KMonoid κ H] (hκ : ℵ₀ ≤ κ)
    {g : ↥(FreeK κ B) → H}
    (hg : letI := instKMonoidFreeK κ hκ B
      IsLMonoidHom (Order.succ κ) g) :
    letI := instKMonoidFreeK κ hκ B
    IsKHom κ g := by
  let := instKMonoidFreeK κ hκ B
  exact ⟨hg.map_zero, fun x => hg (KMonoid.lt_succ (le_of_eq (mk_Idx κ))) x⟩

/-- `F_κ(B)` is generated, as a `κ`-monoid, by the generators `ι(b)`.

Every `x` is `Σ_{b ∈ supp x} λ_b · ι(b)` (`lift_iota_eq_self`), and each `λ_b · ι(b)` is itself a
`κ`-sum of copies of `ι(b)`. -/
theorem kGenerates_range_iota (hκ : ℵ₀ ≤ κ) :
    letI : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
    letI := instKMonoidFreeK κ hκ B
    KGenerates κ (Set.range (iota (lam := Order.succ κ) (B := B))) := by
  let : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  let := instKMonoidFreeK κ hκ B
  set S : Set ↥(FreeK κ B) := kclosure κ (Set.range (iota (lam := Order.succ κ) (B := B))) with hS
  have hSsub : IsKSubmonoid κ S := isKSubmonoid_kclosure κ _
  have hiota : ∀ b : B, iota (lam := Order.succ κ) b ∈ S := fun b => subset_kclosure ⟨b, rfl⟩
  -- each `λ_b · ι(b)` is a `κ`-sum of copies of `ι(b)`
  have hterm : ∀ (x : ↥(FreeK κ B)) (b : B),
      term (iota (lam := Order.succ κ)) (x : B → LCard (Order.succ κ)) b ∈ S := by
    intro x b
    exact hSsub.sumOf_mem
      (le_of_eq_of_le (mk_Idx _)
        (Order.lt_succ_iff.mp ((x : B → LCard (Order.succ κ)) b).2))
      (fun _ => iota (lam := Order.succ κ) b) fun _ => hiota b
  refine Set.eq_univ_of_forall fun x => ?_
  have hx := lift_iota_eq_self (lam := Order.succ κ) x
  rw [← hx, lift_def]
  exact hSsub.sumOf_mem (KMonoid.le_of_lt_succ x.2) _ fun b => hterm x (b : B)

/-- **Definition 2.10(1)**, the paper's form: `H` is `α`-generated exactly when it is the image of
a `κ`-homomorphism from a free `κ`-monoid `F_κ(B)` with `#B ≤ α`. -/
theorem isAlphaGenerated_iff {H : Type u} [KMonoid κ H] (hκ : ℵ₀ ≤ κ) {α : Cardinal.{u}} :
    IsAlphaGenerated κ α H ↔
      ∃ (B : Type u) (g : ↥(FreeK κ B) → H), #B ≤ α ∧
        (letI := instKMonoidFreeK κ hκ B; IsKHom κ g) ∧ Function.Surjective g := by
  let : Fact (Order.succ κ).IsRegular := ⟨Cardinal.isRegular_succ hκ⟩
  constructor
  · rintro ⟨ι, gen, hι, hgen⟩
    let := instKMonoidFreeK κ hκ ι
    refine ⟨ι, lift (lam := Order.succ κ) gen, hι,
      isKHom_of_isLMonoidHom hκ (isLMonoidHom_lift gen), ?_⟩
    -- the image is a `κ`-submonoid containing the generators, hence everything
    have hhom := isKHom_of_isLMonoidHom (B := ι) hκ (isLMonoidHom_lift (X := H) gen)
    have hrange : IsKSubmonoid κ (Set.range (lift (lam := Order.succ κ) gen)) :=
      isKSubmonoid_range hhom
    have hsub : Set.range gen ⊆ Set.range (lift (lam := Order.succ κ) gen) := by
      rintro _ ⟨i, rfl⟩
      exact ⟨iota (lam := Order.succ κ) i, lift_iota gen i⟩
    intro y
    exact kclosure_le hsub hrange (kGenerates_iff.mp hgen y)
  · rintro ⟨B, g, hB, hg, hsurj⟩
    let := instKMonoidFreeK κ hκ B
    refine ⟨B, fun b => g (iota (lam := Order.succ κ) b), hB, ?_⟩
    have := KGenerates.map hg hsurj (kGenerates_range_iota (B := B) hκ)
    rwa [show g '' Set.range (iota (lam := Order.succ κ) (B := B))
        = Set.range fun b => g (iota (lam := Order.succ κ) b) from
      (Set.range_comp g _).symm] at this

end KappaMonoid
