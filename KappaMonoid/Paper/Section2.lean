/-
**Section 2 of the paper**: an index of its numbered results.

Each entry names the paper result, and the declaration that formalises it.  Unlike
`Paper/Section5.lean`, which restates §5 in the paper's own terms, this file is an index: the
`alias` checks only that the declaration exists — it copies the target's type, so it does not check
what that type is — and the docstring says which paper result it stands for.  Follow the name, or
`#check` the alias, to read the statement.

Results the development deliberately does not formalise are recorded at the foot of the file.
-/
import KappaMonoid.Modules.Corollary47
import KappaMonoid.Modules.Rings.Realisation
import KappaMonoid.Modules.Rings.Progenerator
import KappaMonoid.Core.Compatible
import KappaMonoid.Modules.Rings.Semisimple
import KappaMonoid.Examples
import KappaMonoid.Core.Cyclic
import KappaMonoid.Paper.Definition21

namespace KappaMonoid

namespace Paper

/-- **Definition 2.1** — `KappaMonoid.PaperKMonoid`, in `Paper/Definition21.lean`: the
definition transcribed literally, with `KappaMonoid.PaperKMonoid.toKMonoid` and
`KappaMonoid.KMonoid.toPaper` the two directions of its agreement with `KMonoid`. -/
alias definition_2_1_PaperKMonoid := KappaMonoid.PaperKMonoid

/-- **Remark 2.2(1)** — commutativity is automatic.  There is no separate statement: it is (A3) of
Lemma 2.5 (`KappaMonoid.PaperKMonoid.sigma_perm`, from (A1) and (A2) alone), and this is the
construction that uses it — `KappaMonoid.KMonoid.ofBare` builds the `κ`-monoid, whose addition
is commutative because of it. -/
alias remark_2_2_1_ofBare := KappaMonoid.KMonoid.ofBare

/-- **Remark 2.2(2)** — summing over an arbitrary index set of cardinality `κ`:
`KappaMonoid.KMonoid.sumOf` takes a family indexed by any type of the right size, and
`KappaMonoid.KMonoid.sumOf_equiv` is the independence of the chosen bijection.  See
`README.md`, "Index sets: arbitrary types, not the cardinal". -/
alias remark_2_2_2_sumOf_equiv := KappaMonoid.KMonoid.sumOf_equiv

/-- **Remark 2.2(2)**, the substance — `KappaMonoid.PaperKMonoid.toKMonoid_sumOf`, in
`Paper/Definition21.lean`: for a `κ`-monoid given as in Definition 2.1, the sum over an arbitrary
index type of size `≤ κ` is the `κ`-indexed `Σ` of any zero-padded transport, and so is
well defined; this rests on (A3), `PaperKMonoid.sigma_perm`.  (`sumOf_equiv` above is, inside
`KMonoid`, the reindexing field of the class.) -/
alias remark_2_2_2_toKMonoid_sumOf := KappaMonoid.PaperKMonoid.toKMonoid_sumOf

/-- **Examples 2.3(2)** — `KappaMonoid.ENNRealExample.instKMonoid`, in `Examples/ENNReal.lean`. -/

alias examples_2_3_2_instKMonoid := KappaMonoid.ENNRealExample.instKMonoid

/-- **Examples 2.3(3)** — `KappaMonoid.Fcard.instKMonoid`, in `Core/Cardinal.lean`. -/
alias examples_2_3_3_instKMonoid := KappaMonoid.Fcard.instKMonoid

/-- **Examples 2.3(1)** — `KappaMonoid.TrivExt.instKMonoid`, in `Examples/TrivExt.lean`. -/
alias examples_2_3_1_instKMonoid := KappaMonoid.TrivExt.instKMonoid

/-- **Examples 2.3(4)** — `KappaMonoid.ModuleClass.instKMonoid`, in `Modules/Class.lean`: a class
of modules closed under isomorphisms and `≤ κ`-indexed direct sums is a `κ`-monoid. -/
alias examples_2_3_4_instKMonoid := KappaMonoid.ModuleClass.instKMonoid

/-- **Definition 2.4(1)** — `KappaMonoid.ModuleClass`, in `Modules/Class.lean`: `V^κ(C)` is
`C.carrier` with the `κ`-monoid structure of `ModuleClass.instKMonoid`. -/
alias definition_2_4_1_ModuleClass := KappaMonoid.ModuleClass

/-- The class `𝓕^κ` of free modules, an instance of Definition 2.4(1) —
`KappaMonoid.FreeMod.freeClass`, in `Modules/Rings/FreeModules.lean`.  It is what
Proposition 2.16 realises. -/
alias freeClass := KappaMonoid.FreeMod.freeClass


/-- **Definition 2.4(2)** — `KappaMonoid.projClass`, in `Modules/Projective.lean`.  The scoped
notation `V(R)` abbreviates `projClass R ℵ₀ le_rfl`, which is the paper's `V^{ℵ₀}(R)`. -/
alias definition_2_4_2_projClass := KappaMonoid.projClass

/-- **Definition 2.4(3)** — the paper's `V(R)`, the monoid of finitely generated projective
modules, is `(projClass R κ hκ).lambdaGenPart ℵ₀` — `KappaMonoid.ModuleClass.lambdaGenPart` at
`λ = ℵ₀`.  `KappaMonoid.addOf_unitClass_eq` identifies it with `add [R]`. -/
alias definition_2_4_3_lambdaGenPart := KappaMonoid.ModuleClass.lambdaGenPart


/-- **Lemma 2.5**, (A3) from (A1) and (A2) — `KappaMonoid.PaperKMonoid.sigma_perm`, in
`Paper/Definition21.lean`: `Σ` is invariant under permutations of `κ`. -/
alias lemma_2_5_A3_sigma_perm := KappaMonoid.PaperKMonoid.sigma_perm

/-- **Lemma 2.5**, (A3) for bare summation data — `KappaMonoid.BareKMonoid.ksum_perm`, in
`Core/Bare.lean`. -/
alias lemma_2_5_A3_bare_ksum_perm := KappaMonoid.BareKMonoid.ksum_perm

/-- **Lemma 2.5**, (A4) — `KappaMonoid.KMonoid.ksum_comm`, in `Core/KMonoid.lean`: iterated sums
may be interchanged. -/
alias lemma_2_5_A4_ksum_comm := KappaMonoid.KMonoid.ksum_comm

/-- **After Lemma 2.5**: a `κ`-monoid is determined by its `κ`-indexed summation —
`KappaMonoid.KMonoid.ofBare`, in `Core/Bare.lean`, builds the whole structure from (A1) and (A2). -/
alias lemma_2_5_ofBare := KappaMonoid.KMonoid.ofBare

/-- **After Lemma 2.5**, second bullet: `(H, Σ²)` is a commutative monoid —
`KappaMonoid.SumData.addCommMonoid`, in `Core/SumData.lean`. -/
alias lemma_2_5_addCommMonoid := KappaMonoid.SumData.addCommMonoid

/-- **Definition 2.6** — `KappaMonoid.LMonoid.lcmul`, in `Core/LMonoid.lean`. -/
alias definition_2_6_lcmul := KappaMonoid.LMonoid.lcmul

/-- **Lemma 2.7(2) for a two-term sum of cardinals** — `KappaMonoid.KMonoid.cmul_add`, in `Core/KMonoid.lean`. -/
alias lemma_2_7_2_for_a_two_term_sum_of_cardinals_cmul_add := KappaMonoid.KMonoid.cmul_add

/-- **A companion of Lemma 2.7** — `KappaMonoid.KMonoid.cmul_cmul`, in `Core/KMonoid.lean`:
`α(βx) = (αβ)x`.  An auxiliary rule the paper does not state: Lemma 2.7 has three items and
this is not one of them. -/
alias lemma_2_7_companion_cmul_cmul := KappaMonoid.KMonoid.cmul_cmul

/-- **Lemma 2.7(1), first half** — `KappaMonoid.KMonoid.cmul_zero_cardinal`, in
`Core/KMonoid.lean`: `0x = 0`. -/
alias lemma_2_7_1_first_half_cmul_zero_cardinal := KappaMonoid.KMonoid.cmul_zero_cardinal

/-- **Lemma 2.7(1), second half** — `KappaMonoid.KMonoid.cmul_one`, in `Core/KMonoid.lean`. -/
alias lemma_2_7_1_second_half_cmul_one := KappaMonoid.KMonoid.cmul_one

/-- **Lemma 2.7(3)** — `KappaMonoid.KMonoid.cmul_sumOf`, in `Core/KMonoid.lean`. -/
alias lemma_2_7_3_cmul_sumOf := KappaMonoid.KMonoid.cmul_sumOf

/-- **Lemma 2.7(2)** — `KappaMonoid.KMonoid.cmul_sumOf_cardinal`, in `Core/KMonoid.lean`. -/
alias lemma_2_7_2_cmul_sumOf_cardinal := KappaMonoid.KMonoid.cmul_sumOf_cardinal

/-- **Lemma 2.7(2)** — `KappaMonoid.LMonoid.lcmul_add`, in `Core/LMonoid.lean`. -/
alias lemma_2_7_2_lcmul_add := KappaMonoid.LMonoid.lcmul_add

/-- **Lemma 2.7(3)** — `KappaMonoid.LMonoid.lcmul_lsumOf`, in `Core/LMonoid.lean`. -/
alias lemma_2_7_3_lcmul_lsumOf := KappaMonoid.LMonoid.lcmul_lsumOf

/-- **Lemma 2.7(2)** — `KappaMonoid.LMonoid.lcmul_lsumOf_cardinal`, in `Core/LMonoid.lean`. -/
alias lemma_2_7_2_lcmul_lsumOf_cardinal := KappaMonoid.LMonoid.lcmul_lsumOf_cardinal

/-- **Lemma 2.7(1)** — `KappaMonoid.LMonoid.lcmul_one`, in `Core/LMonoid.lean`. -/
alias lemma_2_7_1_lcmul_one := KappaMonoid.LMonoid.lcmul_one

/-- **Lemma 2.7(1)** — `KappaMonoid.LMonoid.lcmul_zero_cardinal`, in `Core/LMonoid.lean`. -/
alias lemma_2_7_1_lcmul_zero_cardinal := KappaMonoid.LMonoid.lcmul_zero_cardinal

/-- **Lemma 2.8(2)** — `KappaMonoid.KMonoid.add_cmul_top_eq`, in `Core/KMonoid.lean`. -/
alias lemma_2_8_2_add_cmul_top_eq := KappaMonoid.KMonoid.add_cmul_top_eq

/-- **Lemma 2.8**, the idempotence step `x + κx = κx` used in the proofs of both parts —
`KappaMonoid.KMonoid.add_cmul_top_self`, in `Core/KMonoid.lean`. -/
alias lemma_2_8_2_the_key_idempotence_step_of_the_swindle_add_cmul_top_self := KappaMonoid.KMonoid.add_cmul_top_self

/-- **Lemma 2.8(1)** — `KappaMonoid.KMonoid.isConical`, in `Core/KMonoid.lean`. -/
alias lemma_2_8_1_isConical := KappaMonoid.KMonoid.isConical

/-- **Lemma 2.8(2)** — `KappaMonoid.LMonoid.add_lcmul_eq`, in `Core/LMonoid.lean`. -/
alias lemma_2_8_2_add_lcmul_eq := KappaMonoid.LMonoid.add_lcmul_eq

/-- **Proposition 2.9(2)** — `KappaMonoid.exists_unique_lift`, in `Core/Free.lean`. -/
alias proposition_2_9_2_exists_unique_lift := KappaMonoid.exists_unique_lift

/-- **Proposition 2.9(2)** — `KappaMonoid.hom_ext`, in `Core/Free.lean`. -/
alias proposition_2_9_2_hom_ext := KappaMonoid.hom_ext

/-- **Proposition 2.9(2)** — `KappaMonoid.isLMonoidHom_lift`, in `Core/Free.lean`. -/
alias proposition_2_9_2_isLMonoidHom_lift := KappaMonoid.isLMonoidHom_lift

/-- **Proposition 2.9(1)** — `KappaMonoid.isLSubmonoid_FreeL`, in `Core/Free.lean`. -/
alias proposition_2_9_1_isLSubmonoid_FreeL := KappaMonoid.isLSubmonoid_FreeL

/-- **Proposition 2.9(2)** — `KappaMonoid.lift_iota`, in `Core/Free.lean`. -/
alias proposition_2_9_2_lift_iota := KappaMonoid.lift_iota

/-- **Definition 2.10(1)** — `KappaMonoid.KMonoid.IsAlphaGenerated`, in `Core/KMonoid.lean`. -/
alias definition_2_10_1_IsAlphaGenerated := KappaMonoid.KMonoid.IsAlphaGenerated

/-- **Definition 2.10(2)** — `KappaMonoid.KMonoid.IsCyclicKMonoid`, in `Core/KMonoid.lean`. -/
alias definition_2_10_2_IsCyclicKMonoid := KappaMonoid.KMonoid.IsCyclicKMonoid

/-- **Definition 2.10(1)** — `KappaMonoid.isAlphaGenerated_iff`, in `Core/Free.lean`. -/
alias definition_2_10_1_isAlphaGenerated_iff := KappaMonoid.isAlphaGenerated_iff

/-- **Definition 2.11** — `KappaMonoid.AddLe`, in `Core/OrderUnit.lean`. -/
alias definition_2_11_AddLe := KappaMonoid.AddLe

/-- **Definition 2.12(2)** — `KappaMonoid.KMonoid.IsFaithful`, in `Core/OrderUnit.lean`. -/
alias definition_2_12_2_IsFaithful := KappaMonoid.KMonoid.IsFaithful

/-- **Definition 2.12(1)** — `KappaMonoid.KMonoid.IsOrderUnit`, in `Core/OrderUnit.lean`. -/
alias definition_2_12_1_IsOrderUnit := KappaMonoid.KMonoid.IsOrderUnit

/-- **Example 2.13** — `KappaMonoid.Projective.isFaithful_unitClass`, in `Modules/Rings/ProjOrderUnit.lean`. -/
alias example_2_13_isFaithful_unitClass := KappaMonoid.Projective.isFaithful_unitClass

/-- **Example 2.13** — `KappaMonoid.Projective.isOrderUnit_unitClass`, in `Modules/Rings/ProjOrderUnit.lean`. -/
alias example_2_13_isOrderUnit_unitClass := KappaMonoid.Projective.isOrderUnit_unitClass

/-- **Lemma 2.14** — `KappaMonoid.KMonoid.eq_cmul_top_of_add`, in `Core/OrderUnit.lean`. -/
alias lemma_2_14_eq_cmul_top_of_add := KappaMonoid.KMonoid.eq_cmul_top_of_add

/-- **Lemma 2.15** — `KappaMonoid.KMonoid.lemma_2_15`, in `Core/Cyclic.lean`: the disjointness
and the parametrisation. -/
alias lemma_2_15_lemma_2_15 := KappaMonoid.KMonoid.lemma_2_15

/-- **Lemma 2.15**, the bijection — `KappaMonoid.KMonoid.equivFinitePartSumCard`. -/
alias lemma_2_15_equivFinitePartSumCard := KappaMonoid.KMonoid.equivFinitePartSumCard

/-- **Lemma 2.15**, *"with the obvious operation"* — `KappaMonoid.KMonoid.lemma_2_15_add`, the
three rules that determine the operation on `C₀ ⊎ {α : ℵ₀ ≤ α ≤ κ}`. -/
alias lemma_2_15_lemma_2_15_add := KappaMonoid.KMonoid.lemma_2_15_add

/-- **Proposition 2.16** — `KappaMonoid.prop_2_16`, in `Modules/Rings/Realisation.lean`. -/
alias proposition_2_16_prop_2_16 := KappaMonoid.prop_2_16

/-- **Proposition 2.17(1)** — `KappaMonoid.prop_2_17_one`, in `Modules/Rings/Semisimple.lean`. -/
alias proposition_2_17_1_prop_2_17_one := KappaMonoid.prop_2_17_one

/-- **Proposition 2.17(2)**, the auxiliary witness — `KappaMonoid.simpleListPi`, in
`Modules/Rings/Semisimple.lean`: the `n` simple classes of `Fin n → k`.  The statement of (2) is
`prop_2_17_two`, below. -/
alias proposition_2_17_2_simpleListPi := KappaMonoid.simpleListPi

/-- **Proposition 2.17(2)** — `KappaMonoid.prop_2_17_two`, in `Modules/Rings/Semisimple.lean`:
for every `n` there is a semisimple ring `R` with `V^κ(R) ≅ F_κ^n`. -/
alias proposition_2_17_2_prop_2_17_two := KappaMonoid.prop_2_17_two

/-- **Definition 2.18** — `KappaMonoid.LMonoid`, declared in `Core/SumData.lean` (its API is in
`Core/LMonoid.lean`): the class of `λ⁻`-monoids. -/
alias definition_2_18_LMonoid := KappaMonoid.LMonoid

/-- **Remark 2.19** — `KappaMonoid.LMonoid.ofLE`, in `Core/LMonoid.lean`: restriction of a `λ'⁻`-monoid
to a `λ⁻`-monoid for regular `λ ≤ λ'`.  Both halves of the remark's first paragraph are instances:
a `κ`-monoid is a `(κ⁺)⁻`-monoid by definition (`KMonoid` extends `LMonoid (Order.succ κ)`), and a
`κ⁻`-monoid is a `λ`-monoid for every `λ < κ` (`ofLE` at `λ⁺ ≤ κ`). -/
alias remark_2_19_ofLE := KappaMonoid.LMonoid.ofLE

/-- **Remark 2.19**, the converse — `KappaMonoid.LMonoid.ofCompatible`, in `Core/Compatible.lean`:
a compatible family of `λ`-monoid structures for all infinite `λ < κ` (`κ` regular) defines a
`κ⁻`-monoid structure.  It needs `κ > ℵ₀`, which the paper does not say: for `κ = ℵ₀` there is
no infinite `λ < κ`, so the family is empty and determines nothing. -/
alias remark_2_19_ofCompatible := KappaMonoid.LMonoid.ofCompatible

/-- **Remark 2.19** — `KappaMonoid.LMonoid.kMonoidOfLT_ofCompatible`, in `Core/Compatible.lean`:
restricting `ofCompatible` to `λ < κ` gives back the `λ`-monoid it was built from. -/
alias remark_2_19_kMonoidOfLT_ofCompatible := KappaMonoid.LMonoid.kMonoidOfLT_ofCompatible

/-- **Remark 2.19** — `KappaMonoid.LMonoid.ofCompatible_kMonoidOfLT`, in `Core/Compatible.lean`:
a `κ⁻`-monoid is rebuilt by `ofCompatible` from its restrictions. -/
alias remark_2_19_ofCompatible_kMonoidOfLT := KappaMonoid.LMonoid.ofCompatible_kMonoidOfLT

/-- **Example 2.13** — `KappaMonoid.Projective.isFaithful_of_isProgenerator`, in
`Modules/Rings/Progenerator.lean`: for a nonzero ring, the class of every progenerator is a
faithful order-unit of `V^κ(R)`. -/
alias example_2_13_isFaithful_of_isProgenerator :=
  KappaMonoid.Projective.isFaithful_of_isProgenerator

/-- **Example 2.13** (monoid half) — `KappaMonoid.KMonoid.IsFaithful.of_le_nsmul`, in
`Core/OrderUnitTransfer.lean`: `v` is a faithful order-unit if `u` is and `u ≼ n v`, `v ≼ m u`. -/
alias example_2_13_isFaithful_of_le_nsmul := KappaMonoid.KMonoid.IsFaithful.of_le_nsmul

/-- **§2.2, before Definition 2.12** — `KappaMonoid.Projective.exists_add_eq_nsmul_of_isProgenerator`,
in `Modules/Rings/Progenerator.lean`: in `V(R)` the class of every progenerator is an order-unit. -/
alias section_2_2_orderUnit_of_isProgenerator :=
  KappaMonoid.Projective.exists_add_eq_nsmul_of_isProgenerator

/-- **Example 2.13** — `KappaMonoid.Projective.part_unitClass_eq_of_aleph0_le`, in
`Modules/Rings/Progenerator.lean`: `H_α = V^α(R)` for every infinite `α ≤ κ`. -/
alias example_2_13_part_unitClass_eq_of_aleph0_le :=
  KappaMonoid.Projective.part_unitClass_eq_of_aleph0_le

/-- **Example 2.13** — `KappaMonoid.Projective.part_unitClass_zero`: `H_0 = V(R)`. -/
alias example_2_13_part_unitClass_zero := KappaMonoid.Projective.part_unitClass_zero

/-- **Example 2.13** — `KappaMonoid.Projective.part_unitClass_aleph0`: `H_{ℵ₀} = V^{ℵ₀}(R)`. -/
alias example_2_13_part_unitClass_aleph0 := KappaMonoid.Projective.part_unitClass_aleph0


/-! ## Unnumbered claims of §2 -/

/-- **§2.2.1**: every cyclic monoid is `ℕ₀` or `C_{m,n}` — `cyclicMonoidClassification`, in
`ForMathlib/CyclicMonoid.lean`. -/
alias section_2_2_1_cyclicMonoidClassification := cyclicMonoidClassification

/-- **§2.2.1**: Leavitt's theorem, a ring with `V(F) ≅ C_{m,n}` for `m, n ≥ 1` —
`KappaMonoid.leavittData`, in `Modules/Rings/Leavitt.lean`, derived from the Bergman–Dicks
axiom. -/
alias section_2_2_1_leavittData := KappaMonoid.leavittData

/-- **After Proposition 2.9**: `F_κ(B) = F_κ^B` when `#B ≤ κ` — the key step is
`KappaMonoid.mem_FreeL_of_mk_lt`, in `Examples/Diophantine.lean`: every family indexed by a basis
of size `< λ` lies in `F_{λ⁻}(B)`. -/
alias after_prop_2_9_mem_FreeL_of_mk_lt := KappaMonoid.mem_FreeL_of_mk_lt


/-! ## Not formalised

Every numbered item of §2 is above, including both halves of Remark 2.19 and all of Example 2.13.
Definition 2.1, Definition 2.18 (`λ⁻`-monoids) and the first half of Remark 2.19 are the classes
`KMonoid`/`LMonoid` and `LMonoid.ofLE` themselves, so they appear as definitions rather than as
results; `Paper/Definition21.lean` transcribes Definition 2.1 literally and proves it agrees with
`KMonoid`.  Remark 2.2(3) is a pointer to the literature.

Some unnumbered prose has no statement of its own:

* §2.2.1: the only-if half of the list of realisable cyclic monoids (`C_{0,n}` forces `R = 0` and
  `n = 1`), and "the generator of a cyclic `κ`-monoid is an order-unit" (tex 769).
* Around Proposition 2.16 (tex 778–781, 805): that not every cyclic `κ`-monoid is a
  `V^κ(𝓕^κ)`, and that the realisable ones are *precisely* those generated by a faithful
  order-unit.  The ingredients are `FreeMod.isFaithful_unit`, `FreeMod.exists_cmul_unit` and
  invariance of infinite rank; no single theorem packages them.
* The identity `add_λ(x) = add(⟨x⟩_λ)` in the definition of `add_λ` (tex 1783): `addOfCard` is
  defined directly and never compared with the `κ`-closure of `x`. -/

end Paper

end KappaMonoid
