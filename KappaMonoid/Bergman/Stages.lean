/-
**`V` of the finite stages of the realising algebra.**

A closed stage `s` (`Bergman/StageRing.lean`) arises from the stage `(∅, ∅)`, whose ring is `k`,
by adjoining its universal idempotents one at a time (`isIdemExt_step`) and then its universal
isomorphisms one at a time (`isIsoExt_step`).  By **Bergman 1974, Theorems 5.1 and 5.2**
(`PresentedBy.idemExt`, `PresentedBy.isoExt`), `V` of the ring of `s` is presented by the atoms
of `s` subject to the relations of `s` (`stage_presentedBy`), provided some model of the
relations sees that `R`, and both sides of every relation, are nonzero.
-/
import KappaMonoid.Bergman.StageRing
import KappaMonoid.Bergman.Steps

universe u

namespace Bergman

open Matrix

namespace RingPres

variable {G J : Type u} (P : RingPres G J) (k : Type u) [Field k]


/-! ## Adjoining generators to a stage -/

section Steps

variable {s s' : Finset G × Finset J}

/-- The relations of a larger stage, from those of a closed smaller one and the new ones. -/
theorem sholds_extend {T : Type u} [Ring T] (hs : P.Closed s) {x₀ x : P.Gen → T}
    (h₀ : P.SHolds s x₀) (hagree : ∀ y, P.Active s y → x y = x₀ y)
    (hkill : ∀ y, ¬ P.Active s' y → x y = 0)
    (hidem : ∀ g ∈ s'.1, g ∉ s.1 → P.emat x g * P.emat x g = P.emat x g)
    (hrel : ∀ j ∈ s'.2, j ∉ s.2 →
      P.dmat x (P.lhs j) * P.amat x j * P.dmat x (P.rhs j) = P.amat x j ∧
      P.dmat x (P.rhs j) * P.bmat x j * P.dmat x (P.lhs j) = P.bmat x j ∧
      P.amat x j * P.bmat x j = P.dmat x (P.lhs j) ∧ P.bmat x j * P.amat x j = P.dmat x (P.rhs j)) :
    P.SHolds s' x := by
  have hd : ∀ j ∈ s.2, P.dmat x (P.lhs j) = P.dmat x₀ (P.lhs j) ∧
      P.dmat x (P.rhs j) = P.dmat x₀ (P.rhs j) := fun j hj =>
    ⟨P.dmat_congr_of_mem (G₀ := s.1) (fun g hg a b => hagree (.e g a b) hg) (hs j hj).1,
      P.dmat_congr_of_mem (G₀ := s.1) (fun g hg a b => hagree (.e g a b) hg) (hs j hj).2⟩
  have ha : ∀ j ∈ s.2, P.amat x j = P.amat x₀ j := fun j hj => by
    ext a b; exact hagree (.fwd j a b) hj
  have hb : ∀ j ∈ s.2, P.bmat x j = P.bmat x₀ j := fun j hj => by
    ext a b; exact hagree (.bwd j a b) hj
  refine ⟨fun g hg => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, hkill⟩
  · by_cases hg0 : g ∈ s.1
    · rw [P.emat_congr_of_mem (fun a b => hagree (.e g a b) hg0)]; exact h₀.idem g hg0
    · exact hidem g hg hg0
  · by_cases hj0 : j ∈ s.2
    · rw [(hd j hj0).1, (hd j hj0).2, ha j hj0]; exact h₀.cornerA j hj0
    · exact (hrel j hj hj0).1
  · by_cases hj0 : j ∈ s.2
    · rw [(hd j hj0).1, (hd j hj0).2, hb j hj0]; exact h₀.cornerB j hj0
    · exact (hrel j hj hj0).2.1
  · by_cases hj0 : j ∈ s.2
    · rw [(hd j hj0).1, ha j hj0, hb j hj0]; exact h₀.mulAB j hj0
    · exact (hrel j hj hj0).2.2.1
  · by_cases hj0 : j ∈ s.2
    · rw [(hd j hj0).2, ha j hj0, hb j hj0]; exact h₀.mulBA j hj0
    · exact (hrel j hj hj0).2.2.2

theorem slift_comp_incl {T : Type u} [Ring T] [Algebra k T] (hs : P.Closed s) (hle : s ≤ s')
    (φ : P.sring k s →ₐ[k] T) {x : P.Gen → T} (hx : P.SHolds s' x)
    (hagree : ∀ y, P.Active s y → x y = φ (P.sgen k s y)) :
    (P.slift k s' x hx).comp (P.incl k hs hle) = φ := by
  refine P.shom_ext k s _ _ fun y => ?_
  rw [AlgHom.comp_apply, P.incl_sgen]
  by_cases hy : P.Active s y
  · rw [restr_of_active _ hy, P.slift_sgen, hagree y hy]
  · rw [restr_of_not_active _ hy, map_zero, P.sgen_kill k s hy, map_zero]

theorem stage_ext {T : Type u} [Ring T] [Algebra k T] (hs : P.Closed s) (hle : s ≤ s')
    (ψ ψ' : P.sring k s' →ₐ[k] T)
    (hc : ψ.comp (P.incl k hs hle) = ψ'.comp (P.incl k hs hle))
    (hnew : ∀ y, P.Active s' y → ¬ P.Active s y → ψ (P.sgen k s' y) = ψ' (P.sgen k s' y)) :
    ψ = ψ' := by
  refine P.shom_ext k s' _ _ fun y => ?_
  by_cases hy : P.Active s y
  · have e : P.sgen k s' y = P.incl k hs hle (P.sgen k s y) := by
      rw [P.incl_sgen, restr_of_active _ hy]
    rw [e]; exact AlgHom.congr_fun hc _
  · by_cases hy' : P.Active s' y
    · exact hnew y hy' hy
    · rw [P.sgen_kill k s' hy', map_zero, map_zero]

theorem le_insert_fst [DecidableEq G] (s : Finset G × Finset J) (g : G) :
    s ≤ (insert g s.1, s.2) :=
  ⟨Finset.subset_insert _ _, le_rfl⟩

theorem le_insert_snd [DecidableEq J] (s : Finset G × Finset J) (j : J) :
    s ≤ (s.1, insert j s.2) :=
  ⟨le_rfl, Finset.subset_insert _ _⟩

theorem Closed.insert_fst [DecidableEq G] {s : Finset G × Finset J} (hs : P.Closed s) (g : G) :
    P.Closed (insert g s.1, s.2) := fun j hj =>
  ⟨fun α hα => ((hs j hj).1 α hα).mono (Finset.subset_insert _ _),
    fun α hα => ((hs j hj).2 α hα).mono (Finset.subset_insert _ _)⟩

/-- **Adjoining a generator** to a closed stage adjoins a universal idempotent. -/
theorem isIdemExt_step [DecidableEq G] (hs : P.Closed s) {g : G} (hg : g ∉ s.1) :
    IsIdemExt (P.incl k hs (le_insert_fst s g)) (P.size g)
      (P.emat (P.sgen k (insert g s.1, s.2)) g) := by
  set s' : Finset G × Finset J := (insert g s.1, s.2) with hs'def
  have hle : s ≤ s' := le_insert_fst s g
  refine ⟨(P.sholds_sgen k s').idem g (Finset.mem_insert_self g s.1), ?_, ?_⟩
  · intro T _ _ φ E' hE'
    let x : P.Gen → T := fun y => match y with
      | .e h a b => if hh : h = g then
          E' (Fin.cast (congrArg P.size hh) a) (Fin.cast (congrArg P.size hh) b)
        else φ (P.sgen k s (.e h a b))
      | y => φ (P.sgen k s y)
    have hxe : ∀ a b, x (.e g a b) = E' a b := fun a b => by simp [x]
    have hxs : ∀ y, P.Active s y → x y = φ (P.sgen k s y) := by
      rintro (⟨h, a, b⟩ | ⟨j, a, b⟩ | ⟨j, a, b⟩) hy
      · have hh : h ≠ g := fun e => hg (e ▸ hy)
        simp [x, hh]
      · rfl
      · rfl
    have hx0 : ∀ y, ¬ P.Active s' y → x y = 0 := by
      rintro (⟨h, a, b⟩ | ⟨j, a, b⟩ | ⟨j, a, b⟩) hy
      · have hh : h ≠ g := fun e => hy (e ▸ Finset.mem_insert_self g s.1)
        have hy' : ¬ P.Active s (.e h a b) := fun h' => hy (hle.1 h')
        simp only [x, hh, dite_false]
        rw [P.sgen_kill k s hy', map_zero]
      · show φ _ = 0; rw [P.sgen_kill k s (y := .fwd j a b) hy, map_zero]
      · show φ _ = 0; rw [P.sgen_kill k s (y := .bwd j a b) hy, map_zero]
    have hEx : P.emat x g = E' := by ext a b; exact hxe a b
    have hx : P.SHolds s' x := by
      refine P.sholds_extend hs (((P.sholds_sgen k s).map φ.toRingHom)) hxs hx0 ?_ ?_
      · intro h hh hh0
        have : h = g := by
          rcases Finset.mem_insert.1 hh with e | e
          · exact e
          · exact absurd e hh0
        subst this
        rw [hEx]; exact hE'
      · intro j hj hj0; exact absurd hj hj0
    refine ⟨P.slift k s' x hx, P.slift_comp_incl k hs hle φ hx hxs, ?_⟩
    ext a b
    show P.slift k s' x hx (P.sgen k s' (.e g a b)) = E' a b
    rw [P.slift_sgen, hxe]
  · intro T _ _ ψ ψ' hc hE
    refine P.stage_ext k hs hle ψ ψ' hc ?_
    rintro (⟨h, a, b⟩ | ⟨j, a, b⟩ | ⟨j, a, b⟩) hy hy0
    · have : h = g := by
        rcases Finset.mem_insert.1 hy with e | e
        · exact e
        · exact absurd e hy0
      subst this
      exact congrFun (congrFun hE a) b
    · exact absurd hy hy0
    · exact absurd hy hy0

/-- **Adjoining a relation** to a closed stage adjoins a universal isomorphism. -/
theorem isIsoExt_step [DecidableEq J] (hs : P.Closed s) {j : J} (hj : j ∉ s.2)
    (hs' : P.Closed (s.1, insert j s.2)) :
    IsIsoExt (P.incl k hs (le_insert_snd s j)) (P.dmat (P.sgen k s) (P.lhs j))
      (P.dmat (P.sgen k s) (P.rhs j)) (P.amat (P.sgen k (s.1, insert j s.2)) j)
      (P.bmat (P.sgen k (s.1, insert j s.2)) j) := by
  set s' : Finset G × Finset J := (s.1, insert j s.2) with hs'def
  have hle : s ≤ s' := le_insert_snd s j
  have hjs' : j ∈ s'.2 := Finset.mem_insert_self j s.2
  have hD : ∀ l : List (Atom G), (∀ α ∈ l, α.Mem s.1) →
      (P.dmat (P.sgen k s) l).map (P.incl k hs hle) = P.dmat (P.sgen k s') l := fun l hl => by
    rw [← AlgHom.coe_toRingHom, ← dmat_map]
    exact P.dmat_congr_of_mem (G₀ := s.1)
      (fun g hg a b => (P.incl_sgen k hs hle _).trans (restr_of_active _ (y := .e g a b) hg)) hl
  have hL := hD _ (hs' j hjs').1
  have hR := hD _ (hs' j hjs').2
  have h' := P.sholds_sgen k s'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL, hR]; exact h'.cornerA j hjs'
  · rw [hL, hR]; exact h'.cornerB j hjs'
  · rw [hL]; exact h'.mulAB j hjs'
  · rw [hR]; exact h'.mulBA j hjs'
  · intro T _ _ φ A' B' hA hB hAB hBA
    let x : P.Gen → T := fun y => match y with
      | .fwd j' a b => if hj' : j' = j then
          A' (cast (congrArg (fun j => P.Idx (P.lhs j)) hj') a)
            (cast (congrArg (fun j => P.Idx (P.rhs j)) hj') b)
        else φ (P.sgen k s (.fwd j' a b))
      | .bwd j' a b => if hj' : j' = j then
          B' (cast (congrArg (fun j => P.Idx (P.rhs j)) hj') a)
            (cast (congrArg (fun j => P.Idx (P.lhs j)) hj') b)
        else φ (P.sgen k s (.bwd j' a b))
      | y => φ (P.sgen k s y)
    have hxA : P.amat x j = A' := by ext a b; simp [x, amat]
    have hxB : P.bmat x j = B' := by ext a b; simp [x, bmat]
    have hxs : ∀ y, P.Active s y → x y = φ (P.sgen k s y) := by
      rintro (⟨h, a, b⟩ | ⟨j', a, b⟩ | ⟨j', a, b⟩) hy
      · rfl
      · have : j' ≠ j := fun e => hj (e ▸ hy)
        simp [x, this]
      · have : j' ≠ j := fun e => hj (e ▸ hy)
        simp [x, this]
    have hx0 : ∀ y, ¬ P.Active s' y → x y = 0 := by
      rintro (⟨h, a, b⟩ | ⟨j', a, b⟩ | ⟨j', a, b⟩) hy
      · show φ _ = 0; rw [P.sgen_kill k s (y := .e h a b) hy, map_zero]
      · have hne : j' ≠ j := fun e => hy (e ▸ hjs')
        have hy' : ¬ P.Active s (.fwd j' a b) := fun h' => hy (hle.2 h')
        simp only [x, hne, dite_false]
        rw [P.sgen_kill k s hy', map_zero]
      · have hne : j' ≠ j := fun e => hy (e ▸ hjs')
        have hy' : ¬ P.Active s (.bwd j' a b) := fun h' => hy (hle.2 h')
        simp only [x, hne, dite_false]
        rw [P.sgen_kill k s hy', map_zero]
    have hdx : ∀ l, P.dmat x l = (P.dmat (P.sgen k s) l).map φ := fun l => by
      rw [← AlgHom.coe_toRingHom, ← dmat_map]
      exact P.dmat_congr _ (fun _ _ _ => rfl) l
    have hx : P.SHolds s' x := by
      refine P.sholds_extend hs (((P.sholds_sgen k s).map φ.toRingHom)) hxs hx0 ?_ ?_
      · intro g hg hg0; exact absurd hg hg0
      · intro j' hj' hj0
        have : j' = j := by
          rcases Finset.mem_insert.1 hj' with e | e
          · exact e
          · exact absurd e hj0
        subst this
        rw [hdx, hdx, hxA, hxB]
        exact ⟨hA, hB, hAB, hBA⟩
    refine ⟨P.slift k s' x hx, P.slift_comp_incl k hs hle φ hx hxs, ?_, ?_⟩
    · ext a b
      show P.slift k s' x hx (P.sgen k s' (.fwd j a b)) = A' a b
      rw [P.slift_sgen, ← hxA]; rfl
    · ext a b
      show P.slift k s' x hx (P.sgen k s' (.bwd j a b)) = B' a b
      rw [P.slift_sgen, ← hxB]; rfl
  · intro T _ _ ψ ψ' hc hA hB
    refine P.stage_ext k hs hle ψ ψ' hc ?_
    rintro (⟨h, a, b⟩ | ⟨j', a, b⟩ | ⟨j', a, b⟩) hy hy0
    · exact absurd hy hy0
    · have : j' = j := by
        rcases Finset.mem_insert.1 hy with e | e
        · exact e
        · exact absurd e hy0
      subst this
      exact congrFun (congrFun hA a) b
    · have : j' = j := by
        rcases Finset.mem_insert.1 hy with e | e
        · exact e
        · exact absurd e hy0
      subst this
      exact congrFun (congrFun hB a) b

end Steps

/-! ## The induction -/

section Induction

variable {X : Type u} [AddCommMonoid X] (ev : Atom G → X)
  (hev : ∀ x y, P.mrel x y → msum ev x = msum ev y) (hfree : ev .free ≠ 0)
  (hsize : ∀ g, 1 ≤ P.size g) (hl : ∀ j, msum ev ↑(P.lhs j) ≠ 0)
  (hr : ∀ j, msum ev ↑(P.rhs j) ≠ 0)

include hev in
/-- The model `ev` of the relations, on a stage. -/
theorem stage_lift {s : Finset G × Finset J} (h : PresentedBy (P.sγ k s) (P.srel s)) :
    ∃ f : V (P.sring k s) →+ X, ∀ a, f (P.sγ k s a) = ev a.1 :=
  h.exists_lift (ev ∘ Subtype.val) fun x y hxy => by
    rw [msum_comp, msum_comp]; exact hev _ _ (mrel_of_mrelOn hxy)

/-- The trivial atom of a stage. -/
def a₀ (G₀ : Finset G) : SAtom G₀ := ⟨.free, trivial⟩

theorem sγ_a₀ (s : Finset G × Finset J) : P.sγ k s (a₀ s.1) = V.one (P.sring k s) := rfl

/-- **The stage `(∅, ∅)`**: its ring is `k`, so `V` is `ℕ`, generated by `[R]`. -/
theorem presentedBy_empty : PresentedBy (P.sγ k (∅, ∅)) (P.srel (∅, ∅)) := by
  set s : Finset G × Finset J := (∅, ∅) with hsdef
  have hkill : ∀ y, ¬ P.Active s y := by
    rintro (⟨g, a, b⟩ | ⟨j, a, b⟩ | ⟨j, a, b⟩) <;> exact Finset.notMem_empty _
  have h0 : P.SHolds s (0 : P.Gen → k) :=
    ⟨fun g hg => absurd hg (Finset.notMem_empty g), fun j hj => absurd hj (Finset.notMem_empty j),
      fun j hj => absurd hj (Finset.notMem_empty j), fun j hj => absurd hj (Finset.notMem_empty j),
      fun j hj => absurd hj (Finset.notMem_empty j), fun _ _ => rfl⟩
  let π := P.slift k s 0 h0
  have h₁ : (Algebra.ofId k (P.sring k s)).comp π = AlgHom.id k (P.sring k s) := by
    refine P.shom_ext k s _ _ fun y => ?_
    rw [AlgHom.comp_apply, P.slift_sgen, AlgHom.id_apply, P.sgen_kill k s (hkill y)]
    exact map_zero _
  have hsub : ∀ a : SAtom s.1, a = a₀ s.1 := by
    rintro ⟨_ | g | g, h⟩
    · rfl
    · exact absurd h (Finset.notMem_empty g)
    · exact absurd h (Finset.notMem_empty g)
  have hmsum : ∀ x : Multiset (SAtom s.1),
      msum (P.sγ k s) x = Multiset.card x • V.one (P.sring k s) := fun x => by
    have : x.map (P.sγ k s) = x.map fun _ => V.one (P.sring k s) :=
      Multiset.map_congr rfl fun a _ => by rw [hsub a]; rfl
    rw [msum_apply, this, Multiset.map_const', Multiset.sum_replicate]
  have hrep : ∀ x : Multiset (SAtom s.1), x = Multiset.replicate (Multiset.card x) (a₀ s.1) :=
    fun x => Multiset.eq_replicate_card.2 fun b _ => hsub b
  refine ⟨fun v => ?_, fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩⟩
  · obtain ⟨n, hn⟩ := V.field_nsmul_one k (V.map π.toRingHom v)
    refine ⟨Multiset.replicate n (a₀ s.1), ?_⟩
    have hv : v = V.map (Algebra.ofId k (P.sring k s)).toRingHom (V.map π.toRingHom v) := by
      have e : (Algebra.ofId k (P.sring k s)).toRingHom.comp π.toRingHom = RingHom.id _ :=
        congrArg AlgHom.toRingHom h₁
      rw [← V.map_comp, e, V.map_id]
    rw [hmsum, Multiset.card_replicate, hv, hn, map_nsmul, V.map_one]
  · rw [hmsum, hmsum] at hxy
    have hc : Multiset.card x = Multiset.card y := by
      have := congrArg (V.map π.toRingHom) hxy
      rw [map_nsmul, map_nsmul, V.map_one] at this
      exact V.field_nsmul_one_injective k this
    rw [hrep x, hrep y, hc]
    exact (addConGen _).refl _
  · have hle : addConGen (P.srel s) ≤ AddCon.ker (msum (P.sγ k s)) :=
      AddCon.addConGen_le.2 fun x y h => by
        rcases h with ⟨g, hg, -⟩ | ⟨j, hj, -⟩
        · exact absurd hg (Finset.notMem_empty g)
        · exact absurd hj (Finset.notMem_empty j)
    exact (AddCon.ker_rel _).1 (hle hxy)

/-- The atoms after adjoining a generator. -/
def insAtom [DecidableEq G] (G₀ : Finset G) (g : G) : SAtom G₀ ⊕ Bool → SAtom (insert g G₀)
  | .inl a => ⟨a.1, a.2.mono (Finset.subset_insert _ _)⟩
  | .inr true => ⟨.img g, Finset.mem_insert_self g G₀⟩
  | .inr false => ⟨.coimg g, Finset.mem_insert_self g G₀⟩

theorem insAtom_val_injective [DecidableEq G] {G₀ : Finset G} {g : G} (hg : g ∉ G₀) :
    Function.Injective (Subtype.val ∘ insAtom G₀ g) := by
  rintro (a | b) (a' | b') h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exfalso
    have ha := a.2
    cases b' <;> simp only [Function.comp_apply, insAtom] at h <;> rw [h] at ha <;> exact hg ha
  · exfalso
    have ha := a'.2
    cases b <;> simp only [Function.comp_apply, insAtom] at h <;> rw [← h] at ha <;> exact hg ha
  · cases b <;> cases b' <;> simp_all [insAtom]

theorem insAtom_bijective [DecidableEq G] {G₀ : Finset G} {g : G} (hg : g ∉ G₀) :
    Function.Bijective (insAtom G₀ g) := by
  refine ⟨fun a b h => insAtom_val_injective hg (congrArg Subtype.val h), ?_⟩
  rintro ⟨_ | h | h, hh⟩
  · exact ⟨.inl ⟨.free, trivial⟩, rfl⟩
  · by_cases e : h = g
    · subst e; exact ⟨.inr true, rfl⟩
    · exact ⟨.inl ⟨.img h, (Finset.mem_insert.1 hh).resolve_left e⟩, rfl⟩
  · by_cases e : h = g
    · subst e; exact ⟨.inr false, rfl⟩
    · exact ⟨.inl ⟨.coimg h, (Finset.mem_insert.1 hh).resolve_left e⟩, rfl⟩

include hev hfree hsize in
/-- **Adjoining a generator** (Theorem 5.1). -/
theorem presentedBy_insert_gen [DecidableEq G] {s : Finset G × Finset J} (hs : P.Closed s)
    {g : G} (hg : g ∉ s.1) (h : PresentedBy (P.sγ k s) (P.srel s)) :
    PresentedBy (P.sγ k (insert g s.1, s.2)) (P.srel (insert g s.1, s.2)) := by
  set s' : Finset G × Finset J := (insert g s.1, s.2) with hs'def
  have hle : s ≤ s' := le_insert_fst s g
  obtain ⟨f, hf⟩ := P.stage_lift k ev hev h
  have hne : V.one (P.sring k s) ≠ 0 := fun h0 => hfree (by
    have := hf (a₀ s.1)
    rw [sγ_a₀, h0, map_zero] at this
    exact this.symm)
  have hS := P.isIdemExt_step k hs hg
  have h1 := h.idemExt (a₀ s.1) (P.sγ_a₀ k s) hne (hsize g) hS
  let v := insAtom s.1 g
  have hv := insAtom_bijective hg
  let σ := (Equiv.ofBijective v hv).symm
  have h2 := h1.comp_equiv σ
  have hvσ : ∀ b, v (σ b) = b := fun b => Equiv.ofBijective_apply_symm_apply v hv b
  have hgen : ∀ a, idemGen (P.incl k hs hle) (P.sγ k s) hS.idem a = P.sγ k s' (v a) := by
    rintro (a | _ | _)
    · exact P.map_sγ'_incl k hs hle a.2
    · rfl
    · rfl
  have hw := insAtom_val_injective hg
  -- the relations, read through `v`
  have hrel : ∀ X Y, (liftRel (P.srel s) ⊔ idemRel (a₀ s.1) (P.size g)) X Y ↔
      P.mrelOn s' (X.map (Subtype.val ∘ v)) (Y.map (Subtype.val ∘ v)) := by
    intro X Y
    have hinl : (Subtype.val ∘ v) ∘ Sum.inl = Subtype.val := rfl
    constructor
    · rintro (⟨x', y', hr, rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rw [Multiset.map_map, Multiset.map_map, hinl]
        exact mrelOn_mono hle hr
      · exact Or.inl ⟨g, Finset.mem_insert_self g s.1,
          by simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]; rfl,
          by rw [Multiset.map_nsmul, Multiset.map_singleton]; rfl⟩
    · rintro (⟨g', hg', hX, hY⟩ | ⟨j, hj, hX, hY⟩)
      · have hY' : Y = (P.size g' • {a₀ s.1} : Multiset (SAtom s.1)).map Sum.inl := by
          apply Multiset.map_injective hw
          rw [hY, Multiset.map_map, hinl, Multiset.map_nsmul, Multiset.map_singleton]; rfl
        rcases Finset.mem_insert.1 hg' with rfl | hg'
        · refine Or.inr ⟨Multiset.map_injective hw ?_, by rw [hY']; simp [Multiset.map_nsmul]⟩
          rw [hX]
          simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]; rfl
        · refine Or.inl ⟨{⟨.img g', hg'⟩, ⟨.coimg g', hg'⟩}, P.size g' • {a₀ s.1},
            Or.inl ⟨g', hg', by simp,
              by rw [Multiset.map_nsmul, Multiset.map_singleton]; rfl⟩, ?_, hY'⟩
          apply Multiset.map_injective hw
          rw [hX, Multiset.map_map, hinl]; simp
      · obtain ⟨x', hx'⟩ := exists_map_val (G₀ := s.1) (X := ↑(P.lhs j))
          fun α hα => (hs j hj).1 α (Multiset.mem_coe.1 hα)
        obtain ⟨y', hy'⟩ := exists_map_val (G₀ := s.1) (X := ↑(P.rhs j))
          fun α hα => (hs j hj).2 α (Multiset.mem_coe.1 hα)
        refine Or.inl ⟨x', y', Or.inr ⟨j, hj, hx', hy'⟩, ?_, ?_⟩
        · apply Multiset.map_injective hw
          rw [hX, Multiset.map_map, hinl, hx']
        · apply Multiset.map_injective hw
          rw [hY, Multiset.map_map, hinl, hy']
  have hfun : idemGen (P.incl k hs hle) (P.sγ k s) hS.idem ∘ σ = P.sγ k s' := by
    funext b
    show idemGen _ _ _ (σ b) = _
    rw [hgen, hvσ]
  have hrel' : (fun x y => (liftRel (P.srel s) ⊔ idemRel (a₀ s.1) (P.size g))
      (x.map σ) (y.map σ)) = P.srel s' := by
    funext x y
    rw [hrel, Multiset.map_map, Multiset.map_map]
    have : (Subtype.val ∘ v) ∘ σ = Subtype.val := funext fun b => by
      simp only [Function.comp, hvσ]
    rw [this]; rfl
  rw [hfun, hrel'] at h2
  exact h2

include hev hl hr in
/-- **Adjoining a relation** (Theorem 5.2). -/
theorem presentedBy_insert_rel [DecidableEq J] {s : Finset G × Finset J} (hs : P.Closed s)
    {j : J} (hj : j ∉ s.2) (hs' : P.Closed (s.1, insert j s.2))
    (h : PresentedBy (P.sγ k s) (P.srel s)) :
    PresentedBy (P.sγ k (s.1, insert j s.2)) (P.srel (s.1, insert j s.2)) := by
  set s' : Finset G × Finset J := (s.1, insert j s.2) with hs'def
  have hle : s ≤ s' := le_insert_snd s j
  have hjs' : j ∈ s'.2 := Finset.mem_insert_self j s.2
  obtain ⟨f, hf⟩ := P.stage_lift k ev hev h
  obtain ⟨x, hx⟩ := exists_map_val (G₀ := s.1) (X := ↑(P.lhs j))
    fun α hα => (hs' j hjs').1 α (Multiset.mem_coe.1 hα)
  obtain ⟨y, hy⟩ := exists_map_val (G₀ := s.1) (X := ↑(P.rhs j))
    fun α hα => (hs' j hjs').2 α (Multiset.mem_coe.1 hα)
  have hid := (P.sholds_sgen k s).idem_all
  have hmsum : ∀ (z : Multiset (SAtom s.1)) (l : List (Atom G)), z.map Subtype.val = ↑l →
      cls (P.dmat (P.sgen k s) l) (P.dmat_idem _ hid l) = msum (P.sγ k s) z := fun z l hz => by
    rw [P.cls_dmat, ← hz, ← msum_comp]; rfl
  have hfz : ∀ (z : Multiset (SAtom s.1)) (l : List (Atom G)), z.map Subtype.val = ↑l →
      f (msum (P.sγ k s) z) = msum ev ↑l := fun z l hz => by
    rw [map_msum, ← hz, ← msum_comp]
    rw [show (⇑f ∘ P.sγ k s) = ev ∘ Subtype.val from funext hf]
  have hx0 : msum (P.sγ k s) x ≠ 0 := fun h0 => hl j (by rw [← hfz x _ hx, h0, map_zero])
  have hy0 : msum (P.sγ k s) y ≠ 0 := fun h0 => hr j (by rw [← hfz y _ hy, h0, map_zero])
  have h1 := h.isoExt (P.dmat_idem _ hid _) (P.dmat_idem _ hid _) x y (hmsum x _ hx)
    (hmsum y _ hy) hx0 hy0 (P.isIsoExt_step k hs hj hs')
  have hfun : (fun a => V.map (P.incl k hs (le_insert_snd s j)).toRingHom (P.sγ k s a)) =
      P.sγ k s' := funext fun a => P.map_sγ'_incl k hs hle a.2
  have hinj : Function.Injective (Multiset.map (Subtype.val : SAtom s.1 → Atom G)) :=
    Multiset.map_injective Subtype.val_injective
  have hrel : (P.srel s ⊔ fun x' y' => x' = x ∧ y' = y) = P.srel s' := by
    funext x' y'
    apply propext
    show (P.srel s x' y' ∨ (x' = x ∧ y' = y)) ↔ P.mrelOn s' _ _
    constructor
    · rintro (hr' | ⟨rfl, rfl⟩)
      · exact mrelOn_mono hle hr'
      · exact Or.inr ⟨j, hjs', hx, hy⟩
    · rintro (⟨g, hg, hX⟩ | ⟨j', hj', hX, hY⟩)
      · exact Or.inl (Or.inl ⟨g, hg, hX⟩)
      · rcases Finset.mem_insert.1 hj' with rfl | hj'
        · exact Or.inr ⟨hinj (hX.trans hx.symm), hinj (hY.trans hy.symm)⟩
        · exact Or.inl (Or.inr ⟨j', hj', hX, hY⟩)
  rw [hfun, hrel] at h1
  exact h1

include hev hfree hsize hl hr in
/-- **`V` of a closed stage** is presented by its atoms and relations. -/
theorem stage_presentedBy [DecidableEq G] [DecidableEq J] (s : Finset G × Finset J)
    (hs : P.Closed s) : PresentedBy (P.sγ k s) (P.srel s) := by
  obtain ⟨G₀, J₀⟩ := s
  have hG : ∀ G₀ : Finset G, PresentedBy (P.sγ k (G₀, ∅)) (P.srel (G₀, ∅)) := by
    intro G₀
    induction G₀ using Finset.induction_on with
    | empty => exact P.presentedBy_empty k
    | insert g G₀ hg ih =>
      exact P.presentedBy_insert_gen k ev hev hfree hsize
        (s := (G₀, ∅)) (fun j hj => absurd hj (Finset.notMem_empty j)) hg ih
  induction J₀ using Finset.induction_on with
  | empty => exact hG G₀
  | insert j J₀ hj ih =>
    have hs₀ : P.Closed (G₀, J₀) := fun j' hj' => hs j' (Finset.mem_insert_of_mem hj')
    exact P.presentedBy_insert_rel k ev hev hl hr (s := (G₀, J₀)) hs₀ hj hs (ih hs₀)

end Induction

end RingPres

end Bergman
