import Comparator.Defs
import KappaMonoid

/-!
# Bridge, part 1: the challenge's `κ`- and `λ⁻`-monoids against the library's

A challenge `KMonoid κ H` (Definition 2.1 verbatim) gives a library `KappaMonoid.KMonoid κ H`
with the same `0` and `Σ` (`KMonoid.toLib`), and conversely (`KMonoid.ofLib`).  `Compat C L`
records that a challenge structure `C` and a library structure `L` agree; under it every derived
operation of the challenge (`sumOf`, `+`, `•`, homomorphisms, generation, `add(x)`,
`λ⁻`-submonoids) is the library's.  The same for `λ⁻`-monoids (`LMonoid.toLib`).

In a context holding both structures, `+` would elaborate to the challenge's, so the bridge
erases the challenge's `0`, `+` and `•` instances: `+` is always the library's, and the challenge's
operations are written against an explicit structure (`a +[C] b`, `𝟎[C]`, `a •[C] x`).
-/

universe u v w

open Cardinal Function Set
open scoped KappaMonoid

namespace KappaChallenge

attribute [-instance] KMonoid.instAdd KMonoid.instSMul LMonoid.instAdd KMonoid.toZero LMonoid.toZero

/-- The challenge's `+` for the structure `C`. -/
scoped notation:65 a:65 " +[" C "] " b:66 => @HAdd.hAdd _ _ _ (@instHAdd _ (@KMonoid.instAdd _ _ C)) a b
/-- The challenge's `0` for the structure `C`. -/
scoped notation "𝟎[" C "]" => @OfNat.ofNat _ 0 (@Zero.toOfNat0 _ (@KMonoid.toZero _ _ C))
/-- The challenge's `•` for the structure `C`. -/
scoped notation:73 a:74 " •[" C "] " x:73 => @HSMul.hSMul ℕ∞ _ _ (@instHSMul ℕ∞ _ (@KMonoid.instSMul _ _ C)) a x

theorem Idx.exists_isMin {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) : ∃ i : Idx κ, IsMin i := by
  obtain ⟨i⟩ := KappaMonoid.nonempty_Idx hκ
  obtain ⟨m, -, hm⟩ := wellFounded_lt.has_min univ ⟨i, trivial⟩
  exact ⟨m, fun j _ => not_lt.mp (hm j trivial)⟩

theorem card_lt (a : ℕ∞) : #(ULift.{u} {n : ℕ // (n : ℕ∞) < a}) = Cardinal.ofENat a := by
  induction a using ENat.recTopCoe with
  | top =>
    rw [Cardinal.mk_uLift, Cardinal.ofENat_top,
      Cardinal.mk_congr (Equiv.subtypeUnivEquiv fun n => ENat.natCast_lt_top n)]
    simp
  | coe n =>
    rw [Cardinal.mk_uLift, Cardinal.ofENat_nat]
    have : {m : ℕ // (m : ℕ∞) < n} ≃ Fin n :=
      (Equiv.subtypeEquivRight fun m => Nat.cast_lt).trans (Fin.equivSubtype.symm)
    rw [Cardinal.mk_congr this]
    simp

theorem card_lt_le {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (a : ℕ∞) :
    #(ULift.{u} {n : ℕ // (n : ℕ∞) < a}) ≤ κ := by
  rw [card_lt]; exact (Cardinal.ofENat_le_aleph0 a).trans hκ

/-! ## `κ`-monoids -/

namespace KMonoid

variable {κ : Cardinal.{u}} {H : Type v}

/-- The data of Definition 2.1 behind a challenge `κ`-monoid, as the library's `BareKMonoid`. -/
noncomputable def toBare (C : KMonoid κ H) : @KappaMonoid.BareKMonoid κ H C.toZero :=
  letI := C.toZero
  { aleph0_le := C.aleph0_le
    i₀ := (Idx.exists_isMin C.aleph0_le).choose
    ksum := C.sum
    ksum_single := fun x hx => C.sum_single x _ (Idx.exists_isMin C.aleph0_le).choose_spec hx
    ksum_sigma := C.sum_sum }

/-- The library `κ`-monoid of a challenge `κ`-monoid. -/
@[instance_reducible] noncomputable def toLib (C : KMonoid κ H) : KappaMonoid.KMonoid κ H :=
  @KappaMonoid.KMonoid.ofBare κ H C.toZero C.toBare

/-- The challenge `κ`-monoid of a library `κ`-monoid. -/
@[instance_reducible] noncomputable def ofLib (L : KappaMonoid.KMonoid κ H) : KMonoid κ H :=
  letI := L
  { zero := 0
    aleph0_le := KappaMonoid.KMonoid.aleph0_le (H := H)
    sum := KappaMonoid.KMonoid.ksum (κ := κ)
    sum_single := fun x i₀ _ hx => KappaMonoid.KMonoid.ksum_single i₀ x hx
    sum_sum := KappaMonoid.KMonoid.ksum_sigma }

/-- A challenge structure `C` and a library structure `L` with the same `0` and `Σ`. -/
structure Compat (C : KMonoid κ H) (L : KappaMonoid.KMonoid κ H) : Prop where
  zero : 𝟎[C] = (letI := L; (0 : H))
  sum : ∀ x : Idx κ → H, C.sum x = (letI := L; KappaMonoid.KMonoid.ksum (κ := κ) x)

theorem compat_ofLib (L : KappaMonoid.KMonoid κ H) : Compat (ofLib L) L := ⟨rfl, fun _ => rfl⟩

theorem compat_toLib (C : KMonoid κ H) : Compat C C.toLib :=
  ⟨rfl, fun x => by
    have := (@KappaMonoid.KMonoid.ofBare_ksum κ H C.toZero C.toBare x).symm
    exact this⟩

section Compat

variable [L : KappaMonoid.KMonoid κ H] {C : KMonoid κ H} (hc : Compat C L)
include hc

theorem Compat.zero_fun {ι : Type*} : (0 : ι → H) = fun _ => 𝟎[C] :=
  funext fun _ => hc.zero.symm

/-- `sumOf` is the library's `∑[≤ κ]`. -/
theorem Compat.sumOf {ι : Type u} [h : KappaMonoid.CardLE ι κ] (x : ι → H) :
    ∑[≤ κ] i, x i = @KMonoid.sumOf κ H C ι x := by
  classical
  have hne : Nonempty (ι ↪ Idx κ) :=
    (Cardinal.le_def ι (Idx κ)).mp (by rw [KappaMonoid.mk_Idx]; exact h.le)
  rw [KMonoid.sumOf, dif_pos hne, hc.sum, KappaMonoid.KMonoid.sumOf_eq_extend hne.some x,
    hc.zero_fun]
  rfl

theorem Compat.sumOf' {ι : Type u} (h : #ι ≤ κ) (x : ι → H) :
    ∑[≤ κ] i, x i = @KMonoid.sumOf κ H C ι x :=
  @Compat.sumOf _ _ _ C hc ι (KappaMonoid.CardLE.mk' h) x

/-- `+` is the library's. -/
theorem Compat.add (a b : H) : a + b = a +[C] b := by
  rw [← KappaMonoid.KMonoid.sumOf_two,
    hc.sumOf' (Cardinal.mk_le_aleph0.trans (KappaMonoid.KMonoid.aleph0_le (H := H)))]
  rfl

/-- `a • x` is the library's cardinal multiple `(a : Cardinal) x`. -/
theorem Compat.smul (a : ℕ∞) (x : H) :
    KappaMonoid.KMonoid.cmul (κ := κ) (Cardinal.ofENat a)
        ((card_lt a).symm.trans_le (card_lt_le C.aleph0_le a)) x = a •[C] x := by
  rw [KappaMonoid.KMonoid.cmul_congr (card_lt a).symm _ (card_lt_le C.aleph0_le a),
    KappaMonoid.KMonoid.cmul_eq_sumOf, hc.sumOf' (card_lt_le C.aleph0_le a)]
  rfl

/-- `n • x` is the library's `nsmul`. -/
theorem Compat.smul_natCast (n : ℕ) (x : H) : n • x = (n : ℕ∞) •[C] x := by
  rw [← hc.smul, ← KappaMonoid.KMonoid.cmul_natCast]
  exact KappaMonoid.KMonoid.cmul_congr (by simp) _ _ x

/-- Generation is the library's. -/
theorem Compat.generates (S : Set H) :
    @Generates κ H C S ↔ KappaMonoid.KMonoid.KGenerates κ S := by
  rw [KappaMonoid.KMonoid.kGenerates_iff]
  constructor
  · intro hg h
    obtain ⟨x, hx, rfl⟩ := hg h
    rw [hc.sum]
    refine (KappaMonoid.KMonoid.isKSubmonoid_kclosure κ S).ksum_mem x fun i => ?_
    rcases hx i with hi | hi
    · exact KappaMonoid.KMonoid.subset_kclosure hi
    · rw [hi, hc.zero]; exact (KappaMonoid.KMonoid.isKSubmonoid_kclosure κ S).zero_mem
  · intro hg h
    have hmem : h ∈ KappaMonoid.KMonoid.kclosure κ (insert 0 S) :=
      KappaMonoid.KMonoid.kclosure_mono (subset_insert _ _) (hg h)
    obtain ⟨x, hx, rfl⟩ := (KappaMonoid.KMonoid.mem_kclosure_iff (mem_insert _ _) h).mp hmem
    refine ⟨x, fun i => ?_, hc.sum x⟩
    rcases hx i with hi | hi
    · exact Or.inr (hi.trans hc.zero.symm)
    · exact Or.inl hi

/-- `λ⁻`-submonoids are the library's `IsLSubset`. -/
theorem Compat.isLSubmonoid {lam : Cardinal.{u}} (hlk : lam ≤ Order.succ κ) (X : Set H) :
    @IsLSubmonoid κ H C lam X ↔ KappaMonoid.IsLSubset lam hlk X := by
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨hc.zero ▸ h0, fun {ι} hι x hx => ?_⟩
    rw [hc.sumOf' (Order.le_of_lt_succ (hι.trans_le hlk))]
    exact hs ι x hι hx
  · rintro ⟨h0, hs⟩
    refine ⟨hc.zero.symm ▸ h0, fun ι x hι hx => ?_⟩
    rw [← hc.sumOf' (Order.le_of_lt_succ (hι.trans_le hlk))]
    exact hs hι x hx

end Compat

/-- `add(x)` is the library's. -/
theorem Compat.addOf {H : Type u} [L : KappaMonoid.KMonoid κ H] {C : KMonoid κ H}
    (hc : Compat C L) (x : H) : @KMonoid.addOf κ H C x = KappaMonoid.KMonoid.addOf (κ := κ) x := by
  ext y
  simp only [KMonoid.addOf, KappaMonoid.KMonoid.addOf, mem_setOf_eq]
  refine exists_congr fun z => exists_congr fun n => ?_
  rw [← hc.add, KappaMonoid.KMonoid.cmul_natCast, hc.smul_natCast]

/-- Homomorphisms are the library's. -/
theorem Compat.isHom {K : Type w} [L : KappaMonoid.KMonoid κ H] [L' : KappaMonoid.KMonoid κ K]
    {C : KMonoid κ H} {C' : KMonoid κ K} (hc : Compat C L) (hc' : Compat C' L') (f : H → K) :
    @IsHom κ H C K C' f ↔ KappaMonoid.KMonoid.IsKHom κ f := by
  unfold IsHom KappaMonoid.KMonoid.IsKHom
  rw [hc.zero, hc'.zero]
  refine and_congr Iff.rfl (forall_congr' fun x => ?_)
  rw [hc.sum, hc'.sum]

end KMonoid

/-! ## `λ⁻`-monoids -/

namespace LMonoid

variable {lam : Cardinal.{u}} {X : Type v}

/-- The data of Definition 2.18 behind a challenge `λ⁻`-monoid, as the library's `IdxSumData`. -/
noncomputable def toIdxSumData (C : LMonoid lam X) : @KappaMonoid.IdxSumData lam lam X C.toZero :=
  letI := C.toZero
  { isRegular := C.isRegular
    aleph0_le := C.isRegular.aleph0_le
    le_succ := Order.le_succ lam
    i₀ := (Idx.exists_isMin C.isRegular.aleph0_le).choose
    tot := C.sum
    tot_single := fun x hx =>
      C.sum_single x _ (Idx.exists_isMin C.isRegular.aleph0_le).choose_spec hx
    tot_sigma := C.sum_sum }

/-- The library `λ⁻`-monoid of a challenge `λ⁻`-monoid. -/
@[instance_reducible] noncomputable def toLib (C : LMonoid lam X) : KappaMonoid.LMonoid lam X :=
  @KappaMonoid.LMonoid.ofIdxSumData lam lam X C.toZero C.toIdxSumData

variable (C : LMonoid lam X)

theorem toLib_zero : @OfNat.ofNat X 0 (@Zero.toOfNat0 X C.toZero) = (letI := C.toLib; (0 : X)) :=
  rfl

/-- The library's sums are the challenge's `sumOf`. -/
theorem toLib_lsumOf {ι : Type u} (h : #ι < lam) (x : ι → X) :
    @KappaMonoid.LMonoid.lsumOf lam X C.toLib ι h x = @LMonoid.sumOf lam X C ι x := by
  classical
  have hne : Nonempty (ι ↪ Idx lam) :=
    (Cardinal.le_def ι (Idx lam)).mp (by rw [KappaMonoid.mk_Idx]; exact h.le)
  rw [LMonoid.sumOf, dif_pos hne]
  exact (@KappaMonoid.IdxSumData.tot_extend_eq lam lam X C.toZero C.toIdxSumData ι h hne.some x).symm

/-- The library's `+` is the challenge's. -/
theorem toLib_add (a b : X) :
    (letI := C.toLib; a + b) = @HAdd.hAdd X X X (@instHAdd X (@LMonoid.instAdd _ _ C)) a b := by
  let := C.toLib
  have := KappaMonoid.LMonoid.factRegular (lam := lam) (X := X)
  rw [← KappaMonoid.LMonoid.lsumOf_two, toLib_lsumOf]
  rfl

end LMonoid

end KappaChallenge
