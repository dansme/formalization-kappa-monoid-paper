/-
**Definition 2.1 verbatim.**  The paper's definition — a `Zero`, a map `Σ : H^κ → H`, (A1) at one
distinguished index, (A2) for every bijection `κ × κ ≃ κ` — is `BareKMonoid`, in `Core/Bare.lean`,
the input of the constructor `KMonoid.ofBare`.  This file shows that the two notions agree:
`KMonoid.ofBare` and `KMonoid.toBare` are mutually inverse.  Nothing else depends on it.
-/
import KappaMonoid.Core.Bare
import KappaMonoid.Core.Compatible

universe u v w

open Cardinal Function Set

namespace KappaMonoid

/-! ## Definition 2.1 and `KMonoid`

`KMonoid` differs from Definition 2.1 of the paper in three ways: sums are taken over an
arbitrary index type rather than over `κ` itself, (A1) appears as "a sum over a one-point index
type is its unique entry" rather than as a statement about the distinguished element `0 ∈ κ`, and
the commutative monoid structure is carried along rather than reconstructed.  The paper's
definition is `BareKMonoid`; the two round trips below show that nothing is lost or added. -/

/-- **Remark 2.2(1)**: commutativity is automatic.  In terms of the paper's own data, a two-term
`Σ` does not depend on the order of its terms, although neither (A1) nor (A2) says so.

Paper proof: (A3) of Lemma 2.5 (`BareKMonoid.ksum_perm`), applied to the transposition of the two
indices; here it is read off from the reconstructed `κ`-monoid, whose addition is the two-term
`Σ` (`KMonoid.ofBare_add`) and is commutative. -/
theorem BareKMonoid.ksum_pair_comm {κ : Cardinal.{u}} {H : Type v} [Zero H] (B : BareKMonoid κ H)
    (a b : H) {i₀ i₁ : Idx κ} (hne : i₀ ≠ i₁) :
    B.ksum (fun i => if i = i₀ then a else if i = i₁ then b else 0)
      = B.ksum (fun i => if i = i₀ then b else if i = i₁ then a else 0) := by
  let := KMonoid.ofBare B
  rw [← KMonoid.ofBare_add B a b hne, ← KMonoid.ofBare_add B b a hne, add_comm]

/-- The round trip `toBare` then `ofBare` gives back the same `κ`-indexed `Σ`.  The equality of
the whole structures is `KMonoid.ofBare_toBare`, below. -/
theorem KMonoid.ofBare_toBare_ksum (κ : Cardinal.{u}) (H : Type v) [inst : KMonoid κ H]
    (x : Idx κ → H) :
    @KMonoid.ksum κ H (KMonoid.ofBare (KMonoid.toBare κ H)) x = @KMonoid.ksum κ H inst x :=
  KMonoid.ofBare_ksum (KMonoid.toBare κ H) x

/-- **The round trip `KMonoid → Definition 2.1 → KMonoid` is the identity**, as an equality of
structures: sums over every index type and the addition come back unchanged, so a `κ`-monoid is
exactly the data of Definition 2.1. -/
theorem KMonoid.ofBare_toBare (κ : Cardinal.{u}) (H : Type v) [inst : KMonoid κ H] :
    KMonoid.ofBare (KMonoid.toBare κ H) = inst := by
  obtain ⟨i₀, i₁, hne⟩ := (nontrivial_Idx (KMonoid.aleph0_le (κ := κ) (H := H))).exists_pair_ne
  refine KMonoid.ext_of_sumOf ?_ ?_
  · funext a b
    exact (KMonoid.ofBare_add (KMonoid.toBare κ H) a b hne).trans (KMonoid.ksum_two a b i₀ i₁ hne)
  · intro ι h x
    exact (KMonoid.ofBare_sumOf (KMonoid.toBare κ H) h x).trans
      (KMonoid.sumOf_eq_extend (h := CardLE.mk' h) (emb h) x).symm

end KappaMonoid
