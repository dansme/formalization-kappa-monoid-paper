/-
The classical result assumed by this development.

One theorem of ordinary mathematics is taken as an axiom rather than proved.  Assuming a true
statement cannot make the development inconsistent, but a *mis-stated* axiom is false and a
false axiom proves everything, so the statement in `Modules.lean` is accompanied by the standard
proof sketch it stands for and should be checked against the literature before it is relied on.

Audit its use with `#print axioms`, or with the `#assert_axioms` claims in
`KappaMonoid/Paper/AxiomAudit.lean`, which the build checks: every result outside §2.3 and
Corollary 4.7 must report only `propext`, `Quot.sound` and `Classical.choice`.

Universe conventions match the rest of the development — everything lives in `Type u`, so no
`Cardinal.lift` appears.

The other classical results this development needs are proved, in `ForMathlib/`, which depends on
nothing else here: invariance of infinite rank (`FreeRank.lean`), uniqueness of the multiplicities
of simple modules (`SimpleMultiplicity.lean`, on top of `HomDirectSum.lean`), the classification of
cyclic monoids (`CyclicMonoid.lean`), Kaplansky's theorem (`Kaplansky.lean`) and Albrecht's theorem
(`Albrecht.lean`).  Leavitt's realisation theorem is a consequence of the axiom below, in
`Modules/Rings/Leavitt.lean`.
-/
import KappaMonoid.Axioms.Modules
