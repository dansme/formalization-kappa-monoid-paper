/-
The classical results assumed by this development.

One theorem of ordinary mathematics is taken as an axiom rather than proved.  Assuming a true
statement cannot make the development inconsistent, but a *mis-stated* axiom is false and a
false axiom proves everything, so the statement in `Modules.lean` is accompanied by the standard
proof sketch it stands for and should be checked against the literature before it is relied on.

Audit their use with `#print axioms`, or with the `#assert_axioms` claims in
`KappaMonoid/Paper/AxiomAudit.lean`, which the build checks: every result outside §2.3 and
Corollary 4.7 must report only `propext`, `Quot.sound` and `Classical.choice`.

Universe conventions match the rest of the development — everything lives in `Type u`, so no
`Cardinal.lift` appears.

Five of the original seven have since been *proved*, and live in `ForMathlib/`, which depends on
nothing in this development:

* A1 — invariance of infinite rank — is `ForMathlib/FreeRank.lean`: for an infinite basis the rank
  condition Mathlib's `Basis.le_span` assumes is not needed, and the support argument goes through
  over any nontrivial ring;
* A3 — uniqueness of the multiplicities of simple modules — is `ForMathlib/SimpleMultiplicity.lean`,
  on top of `ForMathlib/HomDirectSum.lean`;
* A4 — the classification of cyclic monoids — is `ForMathlib/CyclicMonoid.lean`, which is also where
  `CyclicRel` now lives;
* A6 — Kaplansky's theorem — is `ForMathlib/Kaplansky.lean`;
* A7 — Albrecht's theorem — is `ForMathlib/Albrecht.lean`, on top of A6.

A2, Leavitt's realisation theorem, is a sixth: it is derived from A5 in
`Modules/Rings/Leavitt.lean`.
-/
import KappaMonoid.Axioms.Modules
