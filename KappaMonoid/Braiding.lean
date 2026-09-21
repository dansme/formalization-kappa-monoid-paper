/-
Part 2 — Section 3: braiding of `κ`-indexed families over a `λ⁻`-monoid.

Modelling the "limit well-order" of Definition 3.1
-------------------------------------------------
The paper fixes a *limit well-order* on `κ`: a well-order in which every element has a
successor (equivalently, one with no maximum).  Such an order decomposes uniquely into
`ω`-blocks indexed by its limit elements, and for a limit well-order of cardinality `κ`
there are exactly `κ` many blocks (as `κ · ℵ₀ = κ`).  Conversely `ι × ℕ`, ordered
lexicographically, is a limit well-order of cardinality `#ι` whenever `ι` is infinite.

We therefore index braiding partitions and braiding families by `ι × ℕ`, with successor
`(a, n) ↦ (a, n + 1)` and limit elements `(a, 0)`.  This is *not* a loss of generality: it
is exactly the content of Lemma 3.4(2)(3) (a braiding decomposes into countable braidings)
together with Lemma 3.5 (independence of the chosen well-order), which is why those two
lemmas do not appear as separate results below — they are absorbed into the definition.

Entry point of the braiding layer: import it for all of `KappaMonoid/Braiding/`, which depends
on `KappaMonoid/Core/` alone — no module theory and no assumed result.
-/
import KappaMonoid.Braiding.Prelim
import KappaMonoid.Braiding.Defs
import KappaMonoid.Braiding.WellOrder
import KappaMonoid.Braiding.TransAleph0
import KappaMonoid.Braiding.Sums
import KappaMonoid.Braiding.TransUncountable
import KappaMonoid.Braiding.Over
import KappaMonoid.Braiding.UnivAux
import KappaMonoid.Braiding.Prop310
import KappaMonoid.Braiding.UnivExt
