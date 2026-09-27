/-
**Definition 2.18 verbatim.**  `PaperLMonoid` transcribes the paper's definition of a
`λ⁻`-monoid literally - a `Zero`, a map `Σ : H^(λ) → H` on the `λ`-indexed families of support
`< λ`, (B1) at one distinguished index, (B2) for families with fewer than `λ` nonzero rows and
columns and every bijection `λ × λ ≃ λ` - and `toLMonoid` / `LMonoid.toPaper` show that it agrees
with the `LMonoid` the development uses.  Nothing else depends on this file; it exists so that the
working definition can be checked against the paper's, as `Paper/Definition21.lean` does for
Definition 2.1.
-/
import KappaMonoid.Core.Bare
import KappaMonoid.Core.Compatible

universe u v

open Cardinal Function Set

namespace KappaMonoid

/-! ## Definition 2.18 verbatim

`LMonoid` deviates from Definition 2.18 in the same three ways as `KMonoid` does from
Definition 2.1 (sums over arbitrary index types of size `< λ` rather than over `λ`-indexed
families of support `< λ`; (B1) as the one-point law; the commutative monoid carried along), see
`Paper/Definition21.lean`.  The one feature special to Definition 2.18 is that `Σ` is *partial*:
it is only defined on `H^(λ)`, the families `λ → H` whose support has cardinality `< λ`. -/

/-- **Definition 2.18**, verbatim: for a regular cardinal `λ`, a set `H` with an element `0` and
a map `Σ : H^(λ) → H`, where `H^(λ)` is the set of families `λ → H` of support `< λ`, such that

* (B1) if `x ∈ H^(λ)` has `x i = 0` for all `i ≠ 0`, then `Σ x = x 0`;
* (B2) if `x ∈ H^{λ×λ}` has fewer than `λ` rows containing a nonzero entry and fewer than `λ`
  columns containing a nonzero entry, and `π : λ × λ → λ` is a bijection, then
  `Σᵢ Σⱼ x i j = Σₖ x (π⁻¹ k)`.

`Σ` takes the family together with a proof that it lies in `H^(λ)`.  In (B2) the three families
that are summed - the rows `x i`, the family of row sums, and `x ∘ π⁻¹` - lie in `H^(λ)` because
of the two hypotheses on `x` (and, for the row sums, because a zero row sums to `0` by (B1)); the
paper leaves this implicit, here the three memberships are universally quantified arguments
`hin`, `hout`, `hπ`.  Since `Σ` is irrelevant in its proof argument this adds no assumption.

The distinguished element `0 ∈ λ` is an arbitrary index `i₀ : Idx λ`, and (B1) is assumed at `i₀`
only, exactly as in the paper. -/
structure PaperLMonoid (lam : Cardinal.{u}) (H : Type v) [Zero H] where
  /-- `λ` is a regular cardinal. -/
  isRegular : lam.IsRegular
  /-- The distinguished index, playing the role of `0 ∈ λ`. -/
  i₀ : Idx lam
  /-- The summation `Σ : H^(λ) → H`. -/
  sigma : ∀ x : Idx lam → H, #(support x) < lam → H
  /-- (B1), at the distinguished index. -/
  B1 : ∀ (x : Idx lam → H) (hx : #(support x) < lam), (∀ i, i ≠ i₀ → x i = 0) → sigma x hx = x i₀
  /-- (B2). -/
  B2 : ∀ (x : Idx lam → Idx lam → H), #{i | ∃ j, x i j ≠ 0} < lam → #{j | ∃ i, x i j ≠ 0} < lam →
      ∀ (π : Idx lam × Idx lam ≃ Idx lam) (hin : ∀ i, #(support (x i)) < lam)
        (hout : #(support fun i => sigma (x i) (hin i)) < lam)
        (hπ : #(support fun k => x (π.symm k).1 (π.symm k).2) < lam),
        sigma (fun i => sigma (x i) (hin i)) hout = sigma (fun k => x (π.symm k).1 (π.symm k).2) hπ

namespace PaperLMonoid

variable {lam : Cardinal.{u}} {H : Type v} [Zero H] (P : PaperLMonoid lam H)

include P in
theorem aleph0_le : ℵ₀ ≤ lam := P.isRegular.aleph0_le

include P in
theorem mk_singleton_lt (a : Idx lam) : #(↥({a} : Set (Idx lam))) < lam := by
  rw [Cardinal.mk_singleton]
  exact Cardinal.one_lt_aleph0.trans_le P.aleph0_le

/-- `Σ` does not depend on the proof of membership in `H^(λ)`. -/
theorem sigma_congr {x y : Idx lam → H} (hxy : x = y) (hx : #(support x) < lam)
    (hy : #(support y) < lam) : P.sigma x hx = P.sigma y hy := by
  subst hxy
  rfl

open Classical in
/-- `Σ` extended by `0` to all of `H^λ`; this only removes the proof arguments. -/
noncomputable def tot (x : Idx lam → H) : H :=
  if h : #(support x) < lam then P.sigma x h else 0

theorem tot_eq {x : Idx lam → H} (h : #(support x) < lam) : P.tot x = P.sigma x h := dif_pos h

theorem tot_single {x : Idx lam → H} (hx : ∀ i, i ≠ P.i₀ → x i = 0) : P.tot x = x P.i₀ := by
  have hs : #(support x) < lam :=
    mk_lt_of_subset' (T := {P.i₀}) (fun i hi => by_contra fun h => hi (hx i h))
      (P.mk_singleton_lt _)
  exact (P.tot_eq hs).trans (P.B1 x hs hx)

theorem tot_zero : P.tot (fun _ => 0) = 0 := P.tot_single fun _ _ => rfl

/-- (B2) for `tot`: only the hypotheses on rows and columns remain. -/
theorem tot_B2 (x : Idx lam → Idx lam → H) (hrows : #{i | ∃ j, x i j ≠ 0} < lam)
    (hcols : #{j | ∃ i, x i j ≠ 0} < lam) (π : Idx lam × Idx lam ≃ Idx lam) :
    P.tot (fun i => P.tot (x i)) = P.tot (fun k => x (π.symm k).1 (π.symm k).2) := by
  have hin : ∀ i, #(support (x i)) < lam := fun i =>
    mk_lt_of_subset' (T := {j | ∃ i, x i j ≠ 0}) (fun j hj => ⟨i, hj⟩) hcols
  have hinner : (fun i => P.tot (x i)) = fun i => P.sigma (x i) (hin i) :=
    funext fun i => P.tot_eq (hin i)
  have hout : #(support fun i => P.sigma (x i) (hin i)) < lam := by
    refine mk_lt_of_subset' (fun i hi => by_contra fun hni => hi ?_) hrows
    have h0 : x i = fun _ => 0 := funext fun j => by_contra fun hj => hni ⟨j, hj⟩
    show P.sigma (x i) (hin i) = 0
    rw [← P.tot_eq (hin i), h0, P.tot_zero]
  have hπ : #(support fun k => x (π.symm k).1 (π.symm k).2) < lam := by
    refine mk_lt_of_subset'
      (T := range fun p : ↥{i | ∃ j, x i j ≠ 0} × ↥{j | ∃ i, x i j ≠ 0} => π (p.1.1, p.2.1))
      (fun k hk => ⟨(⟨(π.symm k).1, (π.symm k).2, hk⟩, ⟨(π.symm k).2, (π.symm k).1, hk⟩), ?_⟩)
      (Cardinal.mk_range_le.trans_lt (mk_prod_lt P.isRegular hrows hcols))
    simp
  rw [hinner, P.tot_eq hout, P.tot_eq hπ]
  exact P.B2 x hrows hcols π hin hout hπ

/-- The paper's data as a summation of `Idx λ`-indexed families (`μ = λ`), extended by `0` to
the families outside `H^(λ)`, which are never summed. -/
noncomputable def toIdxSumData : IdxSumData lam lam H where
  isRegular := P.isRegular
  aleph0_le := P.aleph0_le
  le_succ := Order.le_succ lam
  i₀ := P.i₀
  tot := P.tot
  tot_single := fun _ hx => P.tot_single hx
  tot_sigma := P.tot_B2

/-- **Every `λ⁻`-monoid in the sense of the paper is one in the sense of `LMonoid`.** -/
@[instance_reducible]
noncomputable def toLMonoid : LMonoid lam H := P.toIdxSumData.toLMonoid

/-- The reconstructed sums are zero-padded `Σ`'s, along any embedding into `λ`. -/
theorem toLMonoid_lsumOf {ι : Type u} (h : #ι < lam) (e : ι ↪ Idx lam) (x : ι → H) :
    letI := P.toLMonoid
    LMonoid.lsumOf (lam := lam) h x = P.sigma (extend e x 0) (IdxSumData.small_extend h e x) := by
  let := P.toLMonoid
  exact (P.toIdxSumData.tot_extend_eq h e x).symm.trans (P.tot_eq _)

end PaperLMonoid

/-! ## Every `LMonoid` is a `λ⁻`-monoid in the sense of the paper -/

namespace LMonoid

variable {lam : Cardinal.{u}} {H : Type v} [LMonoid lam H]

/-- (B1) for the sum over the support. -/
theorem paper_B1 (a : Idx lam) (x : Idx lam → H) (hx : #(support x) < lam)
    (h1 : ∀ i, i ≠ a → x i = 0) : lsumOf hx (fun i : support x => x i) = x a := by
  have hsub : support x ⊆ {a} := fun i hi => by_contra fun h => hi (h1 i h)
  have hsing : #(↥({a} : Set (Idx lam))) < lam := by
    rw [Cardinal.mk_singleton]
    exact Cardinal.one_lt_aleph0.trans_le (aleph0_le (lam := lam) (X := H))
  rw [← lsumOf_of_subset (hS := ⟨hsing⟩) (hT := ⟨hx⟩) hsub x
    fun i _ hi => Function.notMem_support.mp hi]
  exact lsumOf_unique (h := ⟨hsing⟩) _

/-- (B2) for the sum over the support. -/
theorem paper_B2 (x : Idx lam → Idx lam → H) (hrows : #{i | ∃ j, x i j ≠ 0} < lam)
    (hcols : #{j | ∃ i, x i j ≠ 0} < lam) (π : Idx lam × Idx lam ≃ Idx lam)
    (hin : ∀ i, #(support (x i)) < lam)
    (hout : #(support fun i => lsumOf (hin i) fun j : support (x i) => x i j) < lam)
    (hπ : #(support fun k => x (π.symm k).1 (π.symm k).2) < lam) :
    lsumOf hout (fun i : support (fun i => lsumOf (hin i) fun j : support (x i) => x i j) =>
        lsumOf (hin i) fun j : support (x i) => x i j)
      = lsumOf hπ (fun k : support (fun k => x (π.symm k).1 (π.symm k).2) =>
          x (π.symm k).1 (π.symm k).2) := by
  have hreg := isRegular' (lam := lam) (X := H)
  set R : Set (Idx lam) := {i | ∃ j, x i j ≠ 0} with hR
  set C : Set (Idx lam) := {j | ∃ i, x i j ≠ 0} with hC
  set F : Idx lam → H := fun i => lsumOf (hin i) fun j : support (x i) => x i j with hFdef
  have hF : ∀ i, F i = lsumOf hcols (fun j : C => x i j) := fun i =>
    (lsumOf_of_subset (hS := ⟨hcols⟩) (hT := ⟨hin i⟩) (fun j hj => ⟨i, hj⟩) (x i)
      fun j _ hj => Function.notMem_support.mp hj).symm
  have hsuppF : support F ⊆ R := fun i hi => by
    by_contra hni
    apply hi
    rw [hF i]
    exact lsumOf_eq_zero (hT := ⟨hcols⟩) (x i) fun j _ => by_contra fun hj => hni ⟨j, hj⟩
  have hprod : #(R × C) < lam := mk_prod_lt hreg hrows hcols
  have hsig : #((_ : R) × C) < lam := mk_sigma_lt hreg hrows fun _ => hcols
  set G : Idx lam → H := fun k => x (π.symm k).1 (π.symm k).2 with hGdef
  set φ : R × C → Idx lam := fun p => π (p.1, p.2) with hφdef
  have hφ : Function.Injective φ := fun p q hpq => by
    have h := π.injective hpq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hT : #(range φ) < lam := Cardinal.mk_range_le.trans_lt hprod
  have hsuppG : support G ⊆ range φ := fun k hk =>
    ⟨(⟨(π.symm k).1, (π.symm k).2, hk⟩, ⟨(π.symm k).2, (π.symm k).1, hk⟩), by simp [hφdef]⟩
  calc lsumOf hout (fun i : support F => F i)
      = lsumOf hrows (fun i : R => F i) :=
        (lsumOf_of_subset (hS := ⟨hrows⟩) (hT := ⟨hout⟩) hsuppF F fun i _ hi =>
            Function.notMem_support.mp hi).symm
    _ = lsumOf hrows (fun i : R => lsumOf hcols (fun j : C => x i j)) := by
        congr 1; funext i; exact hF i
    _ = lsumOf hsig (fun p : (_ : R) × C => x p.1 p.2) :=
        lsumOf_sigma (h := ⟨hrows⟩) (hρ := fun _ => ⟨hcols⟩) (fun (i : R) (j : C) => x i j)
    _ = lsumOf hprod (fun p : R × C => x p.1 p.2) :=
        lsumOf_equiv (h := ⟨hsig⟩) (h' := ⟨hprod⟩) (Equiv.sigmaEquivProd R C).symm _
    _ = lsumOf hprod ((fun k : range φ => G k) ∘ Equiv.ofInjective φ hφ) := by
        congr 1; funext p; simp [hGdef, hφdef]
    _ = lsumOf hT (fun k : range φ => G k) := by
        rw [lsumOf_equiv (h := ⟨hT⟩) (h' := ⟨hprod⟩) (Equiv.ofInjective φ hφ)]
        rfl
    _ = lsumOf hπ (fun k : support G => G k) :=
        lsumOf_of_subset (hS := ⟨hT⟩) (hT := ⟨hπ⟩) hsuppG G fun k _ hk =>
            Function.notMem_support.mp hk

/-- **Conversely, every `LMonoid` is a `λ⁻`-monoid in the sense of the paper**: `Σ` sums a
family of `H^(λ)` over its support.  Any index may be taken as the distinguished one. -/
noncomputable def toPaper (lam : Cardinal.{u}) (H : Type v) [LMonoid lam H] :
    PaperLMonoid lam H where
  isRegular := isRegular' (lam := lam) (X := H)
  i₀ := (nonempty_Idx (aleph0_le (lam := lam) (X := H))).some
  sigma := fun x hx => lsumOf hx (fun i : support x => x i)
  B1 := fun x hx h1 => paper_B1 _ x hx h1
  B2 := fun x hrows hcols π hin hout hπ => paper_B2 x hrows hcols π hin hout hπ

@[simp] theorem toPaper_sigma (x : Idx lam → H) (hx : #(support x) < lam) :
    (toPaper lam H).sigma x hx = lsumOf hx (fun i : support x => x i) := rfl

/-- The round trip `toPaper` then `toLMonoid` gives back the same `λ⁻`-monoid: not only the same
sums, but the same structure. -/
theorem toPaper_toLMonoid (lam : Cardinal.{u}) (H : Type v) [M : LMonoid lam H] :
    (toPaper lam H).toLMonoid = M := by
  have hsupp : ∀ {ι : Type u} (h : #ι < lam) (e : ι ↪ Idx lam) (x : ι → H)
      (hS : #(support (extend e x 0)) < lam),
      lsumOf hS (fun i : support (extend e x 0) => extend e x 0 i) = lsumOf h x := by
    intro ι h e x hS
    have hR : #(range e) < lam := Cardinal.mk_range_le.trans_lt h
    rw [← lsumOf_of_subset (hS := ⟨hR⟩) (hT := ⟨hS⟩)
      (fun k hk => by_contra fun hk' => hk (extend_apply' _ _ _ fun ⟨i, hi⟩ => hk' ⟨i, hi⟩))
      (extend e x 0) fun k _ hk => Function.notMem_support.mp hk,
      lsumOf_equiv (h := ⟨hR⟩) (h' := ⟨h⟩) (Equiv.ofInjective e e.injective) _]
    congr 1
    funext i
    exact e.injective.extend_apply x 0 i
  have hsum : ∀ {ι : Type u} (h : #ι < lam) (x : ι → H),
      (toPaper lam H).toIdxSumData.lsum h x = lsumOf h x := by
    intro ι h x
    rw [← (toPaper lam H).toIdxSumData.tot_extend_eq h (emb h.le) x]
    show (toPaper lam H).tot (extend (emb h.le) x 0) = _
    rw [(toPaper lam H).tot_eq (IdxSumData.small_extend h (emb h.le) x)]
    exact hsupp h (emb h.le) x _
  refine LMonoid.ext_of_lsumOf ?_ (fun h x => hsum h x)
  funext a b
  have hPP : #(PUnit.{u + 1} ⊕ PUnit.{u + 1}) < lam :=
    mk_sum_lt (isRegular' (X := H)) (mk_lt_finite (X := H) _) (mk_lt_finite (X := H) _)
  show (toPaper lam H).toIdxSumData.sumData.add a b = a + b
  exact (hsum hPP _).trans (LMonoid.add_eq_lsumOf hPP a b).symm

end LMonoid

/-- The round trip `toLMonoid` then `toPaper` gives back the paper's `Σ`. -/
theorem PaperLMonoid.toLMonoid_toPaper_sigma {lam : Cardinal.{u}} {H : Type v} [Zero H]
    (P : PaperLMonoid lam H) (x : Idx lam → H) (hx : #(support x) < lam) :
    letI := P.toLMonoid
    (LMonoid.toPaper lam H).sigma x hx = P.sigma x hx := by
  let := P.toLMonoid
  show LMonoid.lsumOf hx (fun i : support x => x i) = _
  rw [P.toLMonoid_lsumOf hx (Function.Embedding.subtype _)]
  apply P.sigma_congr
  funext i
  by_cases hi : i ∈ support x
  · exact (Function.Embedding.subtype _).injective.extend_apply (fun i : support x => x i) 0
      ⟨i, hi⟩
  · rw [extend_apply' _ _ _ (by rintro ⟨j, rfl⟩; exact hi j.2)]
    exact (Function.notMem_support.mp hi).symm

end KappaMonoid
