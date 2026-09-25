/-
**Finite stages of the realising algebra, and compactness.**

A *stage* `s = (G₀, J₀)` of a presentation `P : RingPres G J` is a pair of finite sets of
generators and relations.  Its ring `P.sring k s` is the free algebra on *all* generators of `P`
modulo the relations indexed by `G₀` and `J₀`, and modulo the generators outside the stage.  So it
is the ring of the restricted presentation, but no reindexing of generators is needed: the maps
between stages, and to `P.ring k`, send a generator to itself when it is active and to `0`
otherwise (`restr`).

Compactness: every element of the free algebra only involves the generators of some stage
(`eventually_lift_restr`), and an equality in `P.ring k` holds in all large enough stages
(`eventually_smk_eq`).  "Large enough" is `Filter.atTop` on `Finset G × Finset J`.
-/
import KappaMonoid.Bergman.RingPres
import KappaMonoid.Bergman.Presentation

universe u

namespace Bergman

open Matrix Filter

/-- The atom only involves generators in `G₀`. -/
def Atom.Mem {G : Type u} (G₀ : Finset G) : Atom G → Prop
  | .free => True
  | .img g => g ∈ G₀
  | .coimg g => g ∈ G₀

theorem Atom.Mem.mono {G : Type u} {G₀ G₁ : Finset G} (h : G₀ ⊆ G₁) :
    ∀ {α : Atom G}, α.Mem G₀ → α.Mem G₁
  | .free, _ => trivial
  | .img _, hα => h hα
  | .coimg _, hα => h hα

/-- The generator of an atom, if any. -/
def Atom.idx {G : Type u} : Atom G → Option G
  | .free => none
  | .img g => some g
  | .coimg g => some g

/-- The generators occurring in a list of atoms. -/
def atomsOf {G : Type u} [DecidableEq G] (l : List (Atom G)) : Finset G :=
  (l.filterMap Atom.idx).toFinset

theorem Atom.mem_atomsOf {G : Type u} [DecidableEq G] {l : List (Atom G)} {α : Atom G}
    (h : α ∈ l) : α.Mem (atomsOf l) := by
  cases α with
  | free => trivial
  | img g =>
    show g ∈ atomsOf l
    simp only [atomsOf, List.mem_toFinset, List.mem_filterMap]
    exact ⟨_, h, rfl⟩
  | coimg g =>
    show g ∈ atomsOf l
    simp only [atomsOf, List.mem_toFinset, List.mem_filterMap]
    exact ⟨_, h, rfl⟩

namespace RingPres

variable {G J : Type u} (P : RingPres G J)

/-! ## Stages -/

/-- The generator is active in the stage `s`. -/
def Active (s : Finset G × Finset J) : P.Gen → Prop
  | .e g _ _ => g ∈ s.1
  | .fwd j _ _ => j ∈ s.2
  | .bwd j _ _ => j ∈ s.2

/-- The stage is closed: the atoms of its relations are in it. -/
def Closed (s : Finset G × Finset J) : Prop :=
  ∀ j ∈ s.2, (∀ α ∈ P.lhs j, α.Mem s.1) ∧ ∀ α ∈ P.rhs j, α.Mem s.1

theorem Active.mono {s s' : Finset G × Finset J} (h : s ≤ s') :
    ∀ {y : P.Gen}, P.Active s y → P.Active s' y
  | .e _ _ _, hy => h.1 hy
  | .fwd _ _ _, hy => h.2 hy
  | .bwd _ _ _, hy => h.2 hy

open Classical in
/-- Restrict an assignment of the generators to a stage. -/
noncomputable def restr (s : Finset G × Finset J) {T : Type u} [Zero T] (x : P.Gen → T) :
    P.Gen → T :=
  fun y => if P.Active s y then x y else 0

variable {P}

theorem restr_of_active {s : Finset G × Finset J} {T : Type u} [Zero T] (x : P.Gen → T)
    {y : P.Gen} (hy : P.Active s y) : P.restr s x y = x y := if_pos hy

theorem restr_of_not_active {s : Finset G × Finset J} {T : Type u} [Zero T] (x : P.Gen → T)
    {y : P.Gen} (hy : ¬ P.Active s y) : P.restr s x y = 0 := if_neg hy

variable (P)

/-- The closure of a stage: add the atoms of its relations. -/
def closure [DecidableEq G] (s : Finset G × Finset J) : Finset G × Finset J :=
  (s.1 ∪ s.2.biUnion fun j => atomsOf (P.lhs j ++ P.rhs j), s.2)

theorem le_closure [DecidableEq G] (s : Finset G × Finset J) : s ≤ P.closure s :=
  ⟨Finset.subset_union_left, le_rfl⟩

theorem closed_closure [DecidableEq G] (s : Finset G × Finset J) : P.Closed (P.closure s) := by
  intro j hj
  have hsub : atomsOf (P.lhs j ++ P.rhs j) ⊆ (P.closure s).1 := fun g hg =>
    Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, hj, hg⟩)
  exact ⟨fun α hα => (Atom.mem_atomsOf (List.mem_append_left _ hα)).mono hsub,
    fun α hα => (Atom.mem_atomsOf (List.mem_append_right _ hα)).mono hsub⟩

/-! ## Matrices of atoms, and their classes -/

section Matrices

variable {T : Type u} [Ring T]

omit [Ring T] in
theorem emat_congr_of_mem {x x' : P.Gen → T} {g : G}
    (h : ∀ a b, x (.e g a b) = x' (.e g a b)) : P.emat x g = P.emat x' g := by
  ext a b; exact h a b

theorem atomMat_congr_of_mem {G₀ : Finset G} {x x' : P.Gen → T}
    (h : ∀ g ∈ G₀, ∀ a b, x (.e g a b) = x' (.e g a b)) {α : Atom G} (hα : α.Mem G₀) :
    P.atomMat x α = P.atomMat x' α := by
  cases α with
  | free => rfl
  | img g => exact P.emat_congr_of_mem (h g hα)
  | coimg g =>
    show (1 : Matrix (Fin (P.size g)) (Fin (P.size g)) T) - P.emat x g = 1 - P.emat x' g
    rw [P.emat_congr_of_mem (h g hα)]

theorem dmat_congr_of_mem {G₀ : Finset G} {x x' : P.Gen → T}
    (h : ∀ g ∈ G₀, ∀ a b, x (.e g a b) = x' (.e g a b)) {l : List (Atom G)}
    (hl : ∀ α ∈ l, α.Mem G₀) : P.dmat x l = P.dmat x' l := by
  simp only [dmat]
  congr 1
  funext t
  exact P.atomMat_congr_of_mem h (hl _ (List.getElem_mem _))

theorem atomMat_idem' (x : P.Gen → T) (hx : ∀ g, P.emat x g * P.emat x g = P.emat x g)
    (α : Atom G) : P.atomMat x α * P.atomMat x α = P.atomMat x α := by
  cases α with
  | free => simp [atomMat]
  | img g => exact hx g
  | coimg g => exact one_sub_idem (hx g)

/-- The class of an atom, for an assignment whose matrices `E_g` are idempotent. -/
noncomputable def acls (x : P.Gen → T) (hx : ∀ g, P.emat x g * P.emat x g = P.emat x g)
    (α : Atom G) : V T :=
  cls (P.atomMat x α) (P.atomMat_idem' x hx α)

theorem cls_dmat (x : P.Gen → T) (hx : ∀ g, P.emat x g * P.emat x g = P.emat x g)
    (l : List (Atom G)) : cls (P.dmat x l) (P.dmat_idem x hx l) = msum (P.acls x hx) ↑l := by
  have h := cls_blockDiagonal' (fun t : Fin l.length => P.atomMat x l[t])
    (fun t => P.atomMat_idem' x hx l[t])
  refine h.trans ?_
  rw [msum_apply, Multiset.map_coe, Multiset.sum_coe]
  exact Fin.sum_univ_fun_getElem l (P.acls x hx)

theorem map_acls {T' : Type u} [Ring T'] (f : T →+* T') (x : P.Gen → T)
    (hx : ∀ g, P.emat x g * P.emat x g = P.emat x g)
    (hx' : ∀ g, P.emat (f ∘ x) g * P.emat (f ∘ x) g = P.emat (f ∘ x) g) (α : Atom G) :
    V.map f (P.acls x hx α) = P.acls (f ∘ x) hx' α := by
  rw [acls, V.map_cls]
  exact cls_congr (P.atomMat_map x f α).symm _ _

theorem acls_congr_of_mem {G₀ : Finset G} {x x' : P.Gen → T}
    (hx : ∀ g, P.emat x g * P.emat x g = P.emat x g)
    (hx' : ∀ g, P.emat x' g * P.emat x' g = P.emat x' g)
    (h : ∀ g ∈ G₀, ∀ a b, x (.e g a b) = x' (.e g a b)) {α : Atom G} (hα : α.Mem G₀) :
    P.acls x hx α = P.acls x' hx' α :=
  cls_congr (P.atomMat_congr_of_mem h hα) _ _

end Matrices

/-! ## The relations of a stage -/

section SHolds

variable {T : Type u} [Ring T] (s : Finset G × Finset J)

/-- The relations of the stage `s` hold for `x`, and `x` kills the generators outside `s`. -/
structure SHolds (x : P.Gen → T) : Prop where
  idem : ∀ g ∈ s.1, P.emat x g * P.emat x g = P.emat x g
  cornerA : ∀ j ∈ s.2, P.dmat x (P.lhs j) * P.amat x j * P.dmat x (P.rhs j) = P.amat x j
  cornerB : ∀ j ∈ s.2, P.dmat x (P.rhs j) * P.bmat x j * P.dmat x (P.lhs j) = P.bmat x j
  mulAB : ∀ j ∈ s.2, P.amat x j * P.bmat x j = P.dmat x (P.lhs j)
  mulBA : ∀ j ∈ s.2, P.bmat x j * P.amat x j = P.dmat x (P.rhs j)
  kill : ∀ y, ¬ P.Active s y → x y = 0

variable {P s}

theorem SHolds.idem_all {x : P.Gen → T} (hx : P.SHolds s x) (g : G) :
    P.emat x g * P.emat x g = P.emat x g := by
  by_cases hg : g ∈ s.1
  · exact hx.idem g hg
  · have : P.emat x g = 0 := by
      ext a b; exact hx.kill (.e g a b) hg
    rw [this, zero_mul]

theorem SHolds.map {T' : Type u} [Ring T'] {x : P.Gen → T} (hx : P.SHolds s x)
    (f : T →+* T') : P.SHolds s (f ∘ x) := by
  refine ⟨fun g hg => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun y hy => ?_⟩
  · rw [emat_map, ← Matrix.map_mul, hx.idem g hg]
  · rw [dmat_map, dmat_map, amat_map, ← Matrix.map_mul, ← Matrix.map_mul, hx.cornerA j hj]
  · rw [dmat_map, dmat_map, bmat_map, ← Matrix.map_mul, ← Matrix.map_mul, hx.cornerB j hj]
  · rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, hx.mulAB j hj]
  · rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, hx.mulBA j hj]
  · simp [hx.kill y hy]

theorem emat_restr (x : P.Gen → T) {g : G} (hg : g ∈ s.1) :
    P.emat (P.restr s x) g = P.emat x g :=
  P.emat_congr_of_mem fun a b => restr_of_active x (y := .e g a b) hg

theorem dmat_restr (x : P.Gen → T) {l : List (Atom G)} (hl : ∀ α ∈ l, α.Mem s.1) :
    P.dmat (P.restr s x) l = P.dmat x l :=
  P.dmat_congr_of_mem (G₀ := s.1) (fun g hg a b => restr_of_active x (y := .e g a b) hg) hl

theorem amat_restr (x : P.Gen → T) {j : J} (hj : j ∈ s.2) :
    P.amat (P.restr s x) j = P.amat x j := by
  ext a b; exact restr_of_active x (y := .fwd j a b) hj

theorem bmat_restr (x : P.Gen → T) {j : J} (hj : j ∈ s.2) :
    P.bmat (P.restr s x) j = P.bmat x j := by
  ext a b; exact restr_of_active x (y := .bwd j a b) hj

/-- Restricting an assignment satisfying all relations to a closed stage. -/
theorem Holds.restr {x : P.Gen → T} (hx : P.Holds x) (hs : P.Closed s) :
    P.SHolds s (P.restr s x) := by
  refine ⟨fun g hg => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun y hy => restr_of_not_active x hy⟩
  · rw [emat_restr x hg]; exact hx.idem g
  · rw [dmat_restr x (hs j hj).1, dmat_restr x (hs j hj).2, amat_restr x hj]; exact hx.cornerA j
  · rw [dmat_restr x (hs j hj).1, dmat_restr x (hs j hj).2, bmat_restr x hj]; exact hx.cornerB j
  · rw [dmat_restr x (hs j hj).1, amat_restr x hj, bmat_restr x hj]; exact hx.mulAB j
  · rw [dmat_restr x (hs j hj).2, amat_restr x hj, bmat_restr x hj]; exact hx.mulBA j

/-- Restricting an assignment satisfying the relations of a larger stage to a closed stage. -/
theorem SHolds.restr {s' : Finset G × Finset J} {x : P.Gen → T} (hx : P.SHolds s' x)
    (hs : P.Closed s) (hle : s ≤ s') : P.SHolds s (P.restr s x) := by
  refine ⟨fun g hg => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun y hy => restr_of_not_active x hy⟩
  · rw [emat_restr x hg]; exact hx.idem g (hle.1 hg)
  · rw [dmat_restr x (hs j hj).1, dmat_restr x (hs j hj).2, amat_restr x hj]
    exact hx.cornerA j (hle.2 hj)
  · rw [dmat_restr x (hs j hj).1, dmat_restr x (hs j hj).2, bmat_restr x hj]
    exact hx.cornerB j (hle.2 hj)
  · rw [dmat_restr x (hs j hj).1, amat_restr x hj, bmat_restr x hj]
    exact hx.mulAB j (hle.2 hj)
  · rw [dmat_restr x (hs j hj).2, amat_restr x hj, bmat_restr x hj]
    exact hx.mulBA j (hle.2 hj)

end SHolds

/-! ## The ring of a stage -/

variable (k : Type u) [Field k]

/-- The relations of a stage, entrywise, in the free algebra on all generators. -/
inductive SRel (s : Finset G × Finset J) : FreeAlgebra k P.Gen → FreeAlgebra k P.Gen → Prop
  | idem (g) (hg : g ∈ s.1) (a b) :
      SRel s ((P.emat (FreeAlgebra.ι k) g * P.emat (FreeAlgebra.ι k) g) a b)
      (P.emat (FreeAlgebra.ι k) g a b)
  | cornerA (j) (hj : j ∈ s.2) (a b) : SRel s ((P.dmat (FreeAlgebra.ι k) (P.lhs j) *
      P.amat (FreeAlgebra.ι k) j * P.dmat (FreeAlgebra.ι k) (P.rhs j)) a b)
      (P.amat (FreeAlgebra.ι k) j a b)
  | cornerB (j) (hj : j ∈ s.2) (a b) : SRel s ((P.dmat (FreeAlgebra.ι k) (P.rhs j) *
      P.bmat (FreeAlgebra.ι k) j * P.dmat (FreeAlgebra.ι k) (P.lhs j)) a b)
      (P.bmat (FreeAlgebra.ι k) j a b)
  | mulAB (j) (hj : j ∈ s.2) (a b) :
      SRel s ((P.amat (FreeAlgebra.ι k) j * P.bmat (FreeAlgebra.ι k) j) a b)
      (P.dmat (FreeAlgebra.ι k) (P.lhs j) a b)
  | mulBA (j) (hj : j ∈ s.2) (a b) :
      SRel s ((P.bmat (FreeAlgebra.ι k) j * P.amat (FreeAlgebra.ι k) j) a b)
      (P.dmat (FreeAlgebra.ι k) (P.rhs j) a b)
  | kill (y : P.Gen) (hy : ¬ P.Active s y) : SRel s (FreeAlgebra.ι k y) 0

/-- **The ring of a stage.** -/
def sring (s : Finset G × Finset J) : Type u := RingQuot (P.SRel k s)

instance (s : Finset G × Finset J) : Ring (P.sring k s) :=
  inferInstanceAs (Ring (RingQuot (P.SRel k s)))

instance (s : Finset G × Finset J) : Algebra k (P.sring k s) :=
  inferInstanceAs (Algebra k (RingQuot (P.SRel k s)))

/-- The quotient map onto the ring of a stage. -/
noncomputable def smk (s : Finset G × Finset J) : FreeAlgebra k P.Gen →ₐ[k] P.sring k s :=
  RingQuot.mkAlgHom k (P.SRel k s)

/-- The generators, in the ring of a stage. -/
noncomputable def sgen (s : Finset G × Finset J) : P.Gen → P.sring k s :=
  fun y => P.smk k s (FreeAlgebra.ι k y)

variable (s : Finset G × Finset J)

theorem sholds_comp_iff {T : Type u} [Ring T] (f : FreeAlgebra k P.Gen →+* T) :
    P.SHolds s (f ∘ FreeAlgebra.ι k) ↔ ∀ a b, P.SRel k s a b → f a = f b := by
  have entry : ∀ {m n : Type} (M N : Matrix m n (FreeAlgebra k P.Gen)),
      M.map f = N.map f ↔ ∀ a b, f (M a b) = f (N a b) := fun M N =>
    ⟨fun h a b => congrFun (congrFun h a) b, fun h => by ext a b; exact h a b⟩
  constructor
  · intro hx a b h
    cases h with
    | idem g hg a b =>
      have := hx.idem g hg
      rw [emat_map, ← Matrix.map_mul, entry] at this
      exact this a b
    | cornerA j hj a b =>
      have := hx.cornerA j hj
      rw [dmat_map, dmat_map, amat_map, ← Matrix.map_mul, ← Matrix.map_mul, entry] at this
      exact this a b
    | cornerB j hj a b =>
      have := hx.cornerB j hj
      rw [dmat_map, dmat_map, bmat_map, ← Matrix.map_mul, ← Matrix.map_mul, entry] at this
      exact this a b
    | mulAB j hj a b =>
      have := hx.mulAB j hj
      rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, entry] at this
      exact this a b
    | mulBA j hj a b =>
      have := hx.mulBA j hj
      rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, entry] at this
      exact this a b
    | kill y hy =>
      rw [map_zero]
      exact hx.kill y hy
  · intro hf
    refine ⟨fun g hg => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
      fun y hy => ?_⟩
    · rw [emat_map, ← Matrix.map_mul, entry]; exact fun a b => hf _ _ (.idem g hg a b)
    · rw [dmat_map, dmat_map, amat_map, ← Matrix.map_mul, ← Matrix.map_mul, entry]
      exact fun a b => hf _ _ (.cornerA j hj a b)
    · rw [dmat_map, dmat_map, bmat_map, ← Matrix.map_mul, ← Matrix.map_mul, entry]
      exact fun a b => hf _ _ (.cornerB j hj a b)
    · rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, entry]
      exact fun a b => hf _ _ (.mulAB j hj a b)
    · rw [dmat_map, amat_map, bmat_map, ← Matrix.map_mul, entry]
      exact fun a b => hf _ _ (.mulBA j hj a b)
    · have := hf _ _ (.kill y hy)
      rw [map_zero] at this
      exact this

theorem sholds_sgen : P.SHolds s (P.sgen k s) :=
  (P.sholds_comp_iff k s (P.smk k s).toRingHom).2 fun _ _ h => RingQuot.mkAlgHom_rel k h

theorem sgen_kill {y : P.Gen} (hy : ¬ P.Active s y) : P.sgen k s y = 0 :=
  (P.sholds_sgen k s).kill y hy

theorem lift_sgen : FreeAlgebra.lift k (P.sgen k s) = P.smk k s :=
  FreeAlgebra.hom_ext (funext fun y => FreeAlgebra.lift_ι_apply _ y)

theorem lift_gen : FreeAlgebra.lift k (P.gen k) = RingQuot.mkAlgHom k (P.Rel k) :=
  FreeAlgebra.hom_ext (funext fun y => FreeAlgebra.lift_ι_apply _ y)

/-- The universal property of the ring of a stage. -/
noncomputable def slift {T : Type u} [Ring T] [Algebra k T] (x : P.Gen → T)
    (hx : P.SHolds s x) : P.sring k s →ₐ[k] T :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k x, fun a b h =>
    (P.sholds_comp_iff k s (FreeAlgebra.lift k x).toRingHom).1
      (by
        have : ((FreeAlgebra.lift k x).toRingHom : FreeAlgebra k P.Gen → T) ∘
            FreeAlgebra.ι k = x := funext fun y => FreeAlgebra.lift_ι_apply x y
        rw [this]; exact hx) a b h⟩

theorem slift_smk {T : Type u} [Ring T] [Algebra k T] (x : P.Gen → T) (hx : P.SHolds s x)
    (a : FreeAlgebra k P.Gen) : P.slift k s x hx (P.smk k s a) = FreeAlgebra.lift k x a := by
  exact RingQuot.liftAlgHom_mkAlgHom_apply k _ _ a

theorem slift_sgen {T : Type u} [Ring T] [Algebra k T] (x : P.Gen → T) (hx : P.SHolds s x)
    (y : P.Gen) : P.slift k s x hx (P.sgen k s y) = x y := by
  rw [sgen, slift_smk, FreeAlgebra.lift_ι_apply]

theorem shom_ext {T : Type u} [Ring T] [Algebra k T] (ψ ψ' : P.sring k s →ₐ[k] T)
    (h : ∀ y, ψ (P.sgen k s y) = ψ' (P.sgen k s y)) : ψ = ψ' := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext y
  exact h y

/-- The classes of the atoms in the ring of a stage. -/
noncomputable def sγ' : Atom G → V (P.sring k s) :=
  P.acls (P.sgen k s) (P.sholds_sgen k s).idem_all

theorem γ_eq_acls : P.γ k = P.acls (P.gen k) (P.holds_gen k).idem := rfl

/-! ## Maps between stages -/

variable {s}

/-- The map from a closed stage to the realising algebra. -/
noncomputable def toRing (hs : P.Closed s) : P.sring k s →ₐ[k] P.ring k :=
  P.slift k s (P.restr s (P.gen k)) ((P.holds_gen k).restr hs)

theorem toRing_sgen (hs : P.Closed s) (y : P.Gen) :
    P.toRing k hs (P.sgen k s y) = P.restr s (P.gen k) y :=
  P.slift_sgen k s _ _ y

/-- The map from a closed stage to a larger one. -/
noncomputable def incl (hs : P.Closed s) {s' : Finset G × Finset J} (hle : s ≤ s') :
    P.sring k s →ₐ[k] P.sring k s' :=
  P.slift k s (P.restr s (P.sgen k s')) ((P.sholds_sgen k s').restr hs hle)

theorem incl_sgen (hs : P.Closed s) {s' : Finset G × Finset J} (hle : s ≤ s') (y : P.Gen) :
    P.incl k hs hle (P.sgen k s y) = P.restr s (P.sgen k s') y :=
  P.slift_sgen k s _ _ y

theorem map_sγ'_toRing (hs : P.Closed s) {α : Atom G} (hα : α.Mem s.1) :
    V.map (P.toRing k hs).toRingHom (P.sγ' k s α) = P.γ k α := by
  rw [sγ', map_acls _ _ _ _ (((P.sholds_sgen k s).map _).idem_all), γ_eq_acls]
  refine P.acls_congr_of_mem _ _ (fun g hg a b => ?_) hα
  exact (P.toRing_sgen k hs _).trans (restr_of_active _ (y := .e g a b) hg)

theorem map_sγ'_incl (hs : P.Closed s) {s' : Finset G × Finset J} (hle : s ≤ s') {α : Atom G}
    (hα : α.Mem s.1) :
    V.map (P.incl k hs hle).toRingHom (P.sγ' k s α) = P.sγ' k s' α := by
  rw [sγ', map_acls _ _ _ _ (((P.sholds_sgen k s).map _).idem_all), sγ']
  refine P.acls_congr_of_mem _ _ (fun g hg a b => ?_) hα
  exact (P.incl_sgen k hs hle _).trans (restr_of_active _ (y := .e g a b) hg)

/-! ## Compactness -/

theorem eventually_mem_fst (g : G) : ∀ᶠ s in (atTop : Filter (Finset G × Finset J)), g ∈ s.1 :=
  (eventually_ge_atTop (({g} : Finset G), (∅ : Finset J))).mono fun _ hs =>
    hs.1 (Finset.mem_singleton_self g)

theorem eventually_mem_snd (j : J) : ∀ᶠ s in (atTop : Filter (Finset G × Finset J)), j ∈ s.2 :=
  (eventually_ge_atTop ((∅ : Finset G), ({j} : Finset J))).mono fun _ hs =>
    hs.2 (Finset.mem_singleton_self j)

/-- Every element of the free algebra only involves the generators of a stage. -/
theorem eventually_lift_restr {T : Type u} [Ring T] [Algebra k T] (x : P.Gen → T)
    (a : FreeAlgebra k P.Gen) :
    ∀ᶠ s in (atTop : Filter (Finset G × Finset J)),
      FreeAlgebra.lift k (P.restr s x) a = FreeAlgebra.lift k x a := by
  classical
  induction a using FreeAlgebra.induction with
  | grade0 r => exact Eventually.of_forall fun s => by simp
  | grade1 y =>
    have hy : ∀ᶠ s in (atTop : Filter (Finset G × Finset J)), P.Active s y := by
      cases y with
      | e g a b => exact eventually_mem_fst g
      | fwd j a b => exact eventually_mem_snd j
      | bwd j a b => exact eventually_mem_snd j
    exact hy.mono fun s hs => by
      rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, restr_of_active x hs]
  | mul a b ha hb => exact (ha.and hb).mono fun s h => by rw [map_mul, map_mul, h.1, h.2]
  | add a b ha hb => exact (ha.and hb).mono fun s h => by rw [map_add, map_add, h.1, h.2]

/-- Equality in all large enough stages, as a ring congruence on the free algebra. -/
def eventuallyCon : RingCon (FreeAlgebra k P.Gen) where
  r a b := ∀ᶠ s in (atTop : Filter (Finset G × Finset J)), P.smk k s a = P.smk k s b
  iseqv :=
    { refl := fun _ => Eventually.of_forall fun _ => rfl
      symm := fun h => h.mono fun _ h => h.symm
      trans := fun h h' => (h.and h').mono fun _ h => h.1.trans h.2 }
  add' := fun h h' => (h.and h').mono fun _ h => by rw [map_add, map_add, h.1, h.2]
  mul' := fun h h' => (h.and h').mono fun _ h => by rw [map_mul, map_mul, h.1, h.2]

/-- **Compactness**: an equality in the realising algebra holds in all large enough stages. -/
theorem eventually_smk_eq {a b : FreeAlgebra k P.Gen}
    (h : RingQuot.mkAlgHom k (P.Rel k) a = RingQuot.mkAlgHom k (P.Rel k) b) :
    ∀ᶠ s in (atTop : Filter (Finset G × Finset J)), P.smk k s a = P.smk k s b := by
  classical
  let c := P.eventuallyCon k
  have hrel : ∀ ⦃a b⦄, P.Rel k a b → c.mk' a = c.mk' b := by
    intro a b hab
    rw [RingCon.coe_mk', RingCon.eq]
    have hmk : ∀ s, P.SRel k s a b → P.smk k s a = P.smk k s b := fun s h =>
      RingQuot.mkAlgHom_rel k h
    cases hab with
    | idem g a b => exact (eventually_mem_fst g).mono fun s hs => hmk s (.idem g hs a b)
    | cornerA j a b => exact (eventually_mem_snd j).mono fun s hs => hmk s (.cornerA j hs a b)
    | cornerB j a b => exact (eventually_mem_snd j).mono fun s hs => hmk s (.cornerB j hs a b)
    | mulAB j a b => exact (eventually_mem_snd j).mono fun s hs => hmk s (.mulAB j hs a b)
    | mulBA j a b => exact (eventually_mem_snd j).mono fun s hs => hmk s (.mulBA j hs a b)
  have e : ∀ a, RingQuot.mkAlgHom k (P.Rel k) a = RingQuot.mkRingHom (P.Rel k) a := fun a => by
    rw [← RingQuot.mkAlgHom_coe k]; rfl
  have key := congrArg (RingQuot.lift ⟨c.mk', hrel⟩) h
  rw [e, e, RingQuot.lift_mkRingHom_apply, RingQuot.lift_mkRingHom_apply, RingCon.coe_mk',
    RingCon.eq] at key
  exact key

/-! ## Atoms and relations of a stage -/

/-- The atoms of a stage. -/
abbrev SAtom (G₀ : Finset G) : Type u := {α : Atom G // α.Mem G₀}

/-- The relations of a stage, among all atoms. -/
def mrelOn (s : Finset G × Finset J) (x y : Multiset (Atom G)) : Prop :=
  (∃ g ∈ s.1, x = {.img g, .coimg g} ∧ y = P.size g • {.free}) ∨
    (∃ j ∈ s.2, x = ↑(P.lhs j) ∧ y = ↑(P.rhs j))

/-- The relations of a stage, among its atoms. -/
def srel (s : Finset G × Finset J) (x y : Multiset (SAtom s.1)) : Prop :=
  P.mrelOn s (x.map Subtype.val) (y.map Subtype.val)

/-- The classes of the atoms of a stage. -/
noncomputable def sγ (s : Finset G × Finset J) (a : SAtom s.1) : V (P.sring k s) :=
  P.sγ' k s a.1

variable {P}

theorem mrelOn_mono {s s' : Finset G × Finset J} (hle : s ≤ s') {x y : Multiset (Atom G)} :
    P.mrelOn s x y → P.mrelOn s' x y := by
  rintro (⟨g, hg, h⟩ | ⟨j, hj, h⟩)
  · exact Or.inl ⟨g, hle.1 hg, h⟩
  · exact Or.inr ⟨j, hle.2 hj, h⟩

theorem mrel_of_mrelOn {s : Finset G × Finset J} {x y : Multiset (Atom G)} :
    P.mrelOn s x y → P.mrel x y := by
  rintro (⟨g, -, h⟩ | ⟨j, -, h⟩)
  · exact Or.inl ⟨g, h⟩
  · exact Or.inr ⟨j, h⟩

theorem exists_map_val {G₀ : Finset G} {X : Multiset (Atom G)} (h : ∀ α ∈ X, α.Mem G₀) :
    ∃ x : Multiset (SAtom G₀), x.map Subtype.val = X :=
  ⟨X.attach.map fun a => ⟨a.1, h a.1 a.2⟩, by simp [Multiset.map_map]⟩

theorem msum_comp {A B X : Type*} [AddCommMonoid X] (f : B → X) (g : A → B) (x : Multiset A) :
    msum (f ∘ g) x = msum f (x.map g) := by
  simp [Multiset.map_map]

theorem map_msum {A X Y : Type*} [AddCommMonoid X] [AddCommMonoid Y] (f : X →+ Y) (γ : A → X)
    (x : Multiset A) : f (msum γ x) = msum (f ∘ γ) x := by
  simp [map_multiset_sum, Multiset.map_map]

variable (P)


/-! ## From the stages to the realising algebra -/

theorem toRing_smk (hs : P.Closed s) (a : FreeAlgebra k P.Gen) :
    P.toRing k hs (P.smk k s a) = FreeAlgebra.lift k (P.restr s (P.gen k)) a :=
  P.slift_smk k s _ _ a

theorem addConGen_map {A B : Type*} (f : A → B) {r : Multiset A → Multiset A → Prop}
    {r' : Multiset B → Multiset B → Prop} (h : ∀ x y, r x y → r' (x.map f) (y.map f))
    {x y : Multiset A} (hxy : addConGen r x y) : addConGen r' (x.map f) (y.map f) := by
  have hxy' : AddConGen.Rel r x y := hxy
  clear hxy
  induction hxy' with
  | of x y hr => exact AddConGen.Rel.of _ _ (h x y hr)
  | refl x => exact (addConGen r').refl _
  | symm _ ih => exact (addConGen r').symm ih
  | trans _ _ ih ih' => exact (addConGen r').trans ih ih'
  | add _ _ ih ih' =>
    rw [Multiset.map_add, Multiset.map_add]
    exact (addConGen r').add ih ih'

theorem map_msum_sγ (hs : P.Closed s) (x : Multiset (SAtom s.1)) :
    V.map (P.toRing k hs).toRingHom (msum (P.sγ k s) x) = msum (P.γ k) (x.map Subtype.val) := by
  rw [map_msum, ← msum_comp]
  congr 1
  exact congrArg msum (funext fun a => P.map_sγ'_toRing k hs a.2)

/-- **Compactness**: if `V` of every closed stage is presented by its atoms and relations, then
`V` of the realising algebra is presented by all atoms and relations. -/
theorem presentedBy_of_stages
    (hst : ∀ s : Finset G × Finset J, P.Closed s → PresentedBy (P.sγ k s) (P.srel s)) :
    PresentedBy (P.γ k) P.mrel := by
  classical
  have hmk := RingQuot.mkAlgHom_surjective k (P.Rel k)
  -- the relations hold
  have hrel : ∀ x y, P.mrel x y → msum (P.γ k) x = msum (P.γ k) y := by
    rintro x y (⟨g, rfl, rfl⟩ | ⟨j, rfl, rfl⟩)
    · let s : Finset G × Finset J := ({g}, ∅)
      have hs : P.Closed s := fun j hj => absurd hj (Finset.notMem_empty j)
      have hg : g ∈ s.1 := Finset.mem_singleton_self g
      let x₀ : Multiset (SAtom s.1) := {⟨.img g, hg⟩, ⟨.coimg g, hg⟩}
      let y₀ : Multiset (SAtom s.1) := P.size g • {⟨.free, trivial⟩}
      have ex : x₀.map Subtype.val = {.img g, .coimg g} := by simp [x₀]
      have ey : y₀.map Subtype.val = P.size g • {.free} := by simp [y₀, Multiset.map_nsmul]
      have h := ((hst s hs).2 x₀ y₀).2 (AddConGen.Rel.of _ _ (Or.inl ⟨g, hg, ex, ey⟩))
      have := congrArg (V.map (P.toRing k hs).toRingHom) h
      rwa [P.map_msum_sγ, P.map_msum_sγ, ex, ey] at this
    · let s : Finset G × Finset J := (atomsOf (P.lhs j ++ P.rhs j), {j})
      have hs : P.Closed s := fun j' hj' => by
        rw [Finset.mem_singleton.1 hj']
        exact ⟨fun α hα => Atom.mem_atomsOf (List.mem_append_left _ hα),
          fun α hα => Atom.mem_atomsOf (List.mem_append_right _ hα)⟩
      obtain ⟨x₀, ex⟩ := exists_map_val (G₀ := s.1) (X := ↑(P.lhs j))
        fun α hα => Atom.mem_atomsOf (List.mem_append_left _ (Multiset.mem_coe.1 hα))
      obtain ⟨y₀, ey⟩ := exists_map_val (G₀ := s.1) (X := ↑(P.rhs j))
        fun α hα => Atom.mem_atomsOf (List.mem_append_right _ (Multiset.mem_coe.1 hα))
      have h := ((hst s hs).2 x₀ y₀).2
        (AddConGen.Rel.of _ _ (Or.inr ⟨j, Finset.mem_singleton_self j, ex, ey⟩))
      have := congrArg (V.map (P.toRing k hs).toRingHom) h
      rwa [P.map_msum_sγ, P.map_msum_sγ, ex, ey] at this
  refine ⟨fun v => ?_, fun x y => ⟨fun hxy => ?_, fun h => ?_⟩⟩
  · -- surjectivity: an idempotent matrix comes from a stage
    obtain ⟨n, e, he, rfl⟩ := cls_surjective v
    choose a ha using fun i j => hmk (e i j)
    have hQ : ∀ᶠ s in (atTop : Filter (Finset G × Finset J)), ∀ i j,
        FreeAlgebra.lift k (P.restr s (P.gen k)) (a i j) = FreeAlgebra.lift k (P.gen k) (a i j) ∧
        P.smk k s (∑ l, a i l * a l j) = P.smk k s (a i j) := by
      rw [eventually_all]; intro i; rw [eventually_all]; intro j
      refine (P.eventually_lift_restr k _ _).and (P.eventually_smk_eq k ?_)
      rw [map_sum]
      simp only [map_mul, ha]
      have := congrFun (congrFun he i) j
      rw [Matrix.mul_apply] at this
      exact this
    obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 hQ
    have hs := P.closed_closure s₀
    have hQs := hs₀ _ (P.le_closure s₀)
    set s := P.closure s₀
    let e₀ : Matrix (Fin n) (Fin n) (P.sring k s) := Matrix.of fun i j => P.smk k s (a i j)
    have he₀ : e₀ * e₀ = e₀ := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [e₀, Matrix.of_apply]
      rw [← (hQs i j).2, map_sum]
      simp only [map_mul]
    have hmap₀ : e₀.map (P.toRing k hs).toRingHom = e := by
      ext i j
      rw [Matrix.map_apply]
      show P.toRing k hs (P.smk k s (a i j)) = e i j
      rw [P.toRing_smk, (hQs i j).1, lift_gen]; exact ha i j
    obtain ⟨x₀, hx₀⟩ := (hst s hs).1 (cls e₀ he₀)
    refine ⟨x₀.map Subtype.val, ?_⟩
    rw [← P.map_msum_sγ k hs, hx₀, V.map_cls]
    exact cls_congr hmap₀ _ _
  · -- injectivity: an equivalence of idempotents comes from a stage
    obtain ⟨lx, rfl⟩ : ∃ l : List (Atom G), (l : Multiset (Atom G)) = x :=
      Quotient.exists_rep x
    obtain ⟨ly, rfl⟩ : ∃ l : List (Atom G), (l : Multiset (Atom G)) = y :=
      Quotient.exists_rep y
    have hid := (P.holds_gen k).idem
    rw [γ_eq_acls, ← P.cls_dmat _ hid, ← P.cls_dmat _ hid, cls_eq_cls] at hxy
    obtain ⟨A, B, hAB, hBA⟩ := hxy
    choose a ha using fun i j => hmk (A i j)
    choose b hb using fun i j => hmk (B i j)
    have hd : ∀ l, P.dmat (P.gen k) l =
        (P.dmat (FreeAlgebra.ι k) l).map (RingQuot.mkAlgHom k (P.Rel k)) := fun l => by
      rw [← AlgHom.coe_toRingHom, ← dmat_map]; rfl
    have hsd : ∀ (s : Finset G × Finset J) l, P.dmat (P.sgen k s) l =
        (P.dmat (FreeAlgebra.ι k) l).map (P.smk k s) := fun s l => by
      rw [← AlgHom.coe_toRingHom, ← dmat_map]; rfl
    have hQ : ∀ᶠ s in (atTop : Filter (Finset G × Finset J)),
        (∀ i j, P.smk k s (∑ t, a i t * b t j) = P.smk k s (P.dmat (FreeAlgebra.ι k) lx i j)) ∧
        (∀ i j, P.smk k s (∑ t, b i t * a t j) = P.smk k s (P.dmat (FreeAlgebra.ι k) ly i j)) ∧
        atomsOf (lx ++ ly) ⊆ s.1 := by
      refine Eventually.and ?_ (Eventually.and ?_ ?_)
      · rw [eventually_all]; intro i; rw [eventually_all]; intro j
        refine P.eventually_smk_eq k ?_
        rw [map_sum]
        simp only [map_mul, ha, hb]
        have := congrFun (congrFun hAB i) j
        rw [Matrix.mul_apply, hd] at this
        exact this
      · rw [eventually_all]; intro i; rw [eventually_all]; intro j
        refine P.eventually_smk_eq k ?_
        rw [map_sum]
        simp only [map_mul, ha, hb]
        have := congrFun (congrFun hBA i) j
        rw [Matrix.mul_apply, hd] at this
        exact this
      · exact (eventually_ge_atTop ((atomsOf (lx ++ ly) : Finset G), (∅ : Finset J))).mono
          fun s hs => hs.1
    obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 hQ
    have hs := P.closed_closure s₀
    have hQs := hs₀ _ (P.le_closure s₀)
    set s := P.closure s₀
    have hid' := (P.sholds_sgen k s).idem_all
    have hMvN : MvN (P.dmat (P.sgen k s) lx) (P.dmat (P.sgen k s) ly) := by
      refine ⟨Matrix.of fun i j => P.smk k s (a i j), Matrix.of fun i j => P.smk k s (b i j),
        ?_, ?_⟩
      · ext i j
        rw [hsd, Matrix.map_apply, ← hQs.1 i j, Matrix.mul_apply, map_sum]
        simp only [map_mul, Matrix.of_apply]
      · ext i j
        rw [hsd, Matrix.map_apply, ← hQs.2.1 i j, Matrix.mul_apply, map_sum]
        simp only [map_mul, Matrix.of_apply]
    have hc := (cls_eq_cls (P.dmat_idem _ hid' lx) (P.dmat_idem _ hid' ly)).2 hMvN
    rw [P.cls_dmat, P.cls_dmat] at hc
    obtain ⟨x₀, hx₀⟩ := exists_map_val (G₀ := s.1) (X := ↑lx)
      fun α hα => (Atom.mem_atomsOf (List.mem_append_left _ (Multiset.mem_coe.1 hα))).mono hQs.2.2
    obtain ⟨y₀, hy₀⟩ := exists_map_val (G₀ := s.1) (X := ↑ly)
      fun α hα => (Atom.mem_atomsOf (List.mem_append_right _ (Multiset.mem_coe.1 hα))).mono
        hQs.2.2
    have h₀ : msum (P.sγ k s) x₀ = msum (P.sγ k s) y₀ := by
      have e₁ : P.sγ k s = P.sγ' k s ∘ Subtype.val := rfl
      rw [e₁, msum_comp, msum_comp, hx₀, hy₀]
      exact hc
    have := addConGen_map Subtype.val (fun x y h => mrel_of_mrelOn h) (((hst s hs).2 x₀ y₀).1 h₀)
    rwa [hx₀, hy₀] at this
  · -- the relations hold
    have hle : addConGen P.mrel ≤ AddCon.ker (msum (P.γ k)) :=
      AddCon.addConGen_le.2 fun x y h => (AddCon.ker_rel _).2 (hrel x y h)
    exact (AddCon.ker_rel _).1 (hle h)

end RingPres

end Bergman
