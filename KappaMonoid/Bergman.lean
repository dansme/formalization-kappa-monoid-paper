/-
**The Bergman–Dicks realisation theorem**, proved.

`Bergman/Realization.lean` states the result (`KappaMonoid.bergmanDicksData`) and explains the
route: a presentation of the monoid; the ring presented by the corresponding universal idempotents
and isomorphisms (`MainRing.lean`); heredity by quasi-freeness (`QuasiFree.lean`); `V` by
compactness, one generator or relation at a time (`Steps.lean`), each step a coproduct over `k^ι`
after passing to a matrix ring (`Morita.lean`); and Bergman's theorem on `V` of such a coproduct
(`Coprod.lean`, `Core/`), following *Modules over coproducts of rings* (1974), §§4–9.

`Bergman/Index.lean` maps Bergman's numbered results to their declarations.  The layer depends
only on Mathlib and `ForMathlib/`, and mentions no `κ`-monoid.
-/
import KappaMonoid.Bergman.Bridge
import KappaMonoid.Bergman.Coprod
import KappaMonoid.Bergman.Core.Basic
import KappaMonoid.Bergman.Core.Echelon
import KappaMonoid.Bergman.Core.Lemma81
import KappaMonoid.Bergman.Core.Main
import KappaMonoid.Bergman.Core.Mono
import KappaMonoid.Bergman.Core.Moves
import KappaMonoid.Bergman.Core.Pres
import KappaMonoid.Bergman.Core.Prop62
import KappaMonoid.Bergman.Core.Prop82
import KappaMonoid.Bergman.Core.Prop8
import KappaMonoid.Bergman.Core.Pure
import KappaMonoid.Bergman.Core.Std
import KappaMonoid.Bergman.Core.Support
import KappaMonoid.Bergman.Core.VBridge
import KappaMonoid.Bergman.Corner
import KappaMonoid.Bergman.Data
import KappaMonoid.Bergman.Idem
import KappaMonoid.Bergman.IdemModule
import KappaMonoid.Bergman.Index
import KappaMonoid.Bergman.IsCoprod
import KappaMonoid.Bergman.MainRing
import KappaMonoid.Bergman.Morita
import KappaMonoid.Bergman.Presentation
import KappaMonoid.Bergman.QuasiFree
import KappaMonoid.Bergman.Realization
import KappaMonoid.Bergman.RingPres
import KappaMonoid.Bergman.SqZero
import KappaMonoid.Bergman.StageRing
import KappaMonoid.Bergman.Stages
import KappaMonoid.Bergman.StepsAux
import KappaMonoid.Bergman.Steps
