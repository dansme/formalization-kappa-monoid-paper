/-
A formalisation of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*,

covering Sections 2–5.

The development is layered by subject, and each layer is an entry point of its own:

| Layer | Depends on | Contents |
|---|---|---|
| `ForMathlib/` | Mathlib | no `κ`-monoid content: trace ideals, `ℕ` blocks, `finsum` |
| `Core/` | ForMathlib | `LMonoid`, `KMonoid`, sums, homomorphisms, sub-objects, `add x`, order units, free and cyclic monoids |
| `Braiding/` | Core | braidings (Def. 3.1), Prop. 3.9, universal `κ`-extensions, Thm 3.11, Lemma 3.13 |
| `Modules/` | Braiding | `ModuleClass`, Thm 4.3, projectives, Cor. 4.5–4.7, the ring examples of §2.2–2.3 |
| `Examples/` | Braiding | the concrete monoids: `TrivExt`, `ℝ≥0∞`, linear systems, `ℝ≥0 ∪ ℝ̃>0 ∪ {∞}` |
| `TwoGen/` | Modules | §5: forms, Lemmas 5.1–5.2, Thm 5.3, Prop. 5.4, Cor. 5.5 |
| `Axioms/` | Mathlib | the six assumed classical results, split by layer |
| `Paper/` | everything | the paper's numbered statements, and nothing else |

`Core/` and the monoid-theoretic half of `Braiding/`, `Examples/` and `TwoGen/` mention no module
and use no axiom; `Paper/` is what to read against the PDF.
-/
import KappaMonoid.ForMathlib.CyclicMonoid
import KappaMonoid.ForMathlib.Finprod
import KappaMonoid.ForMathlib.FreeRank
import KappaMonoid.ForMathlib.FreeTrace
import KappaMonoid.ForMathlib.Leavitt
import KappaMonoid.ForMathlib.HomDirectSum
import KappaMonoid.ForMathlib.ModuleType
import KappaMonoid.ForMathlib.SimpleMultiplicity
import KappaMonoid.ForMathlib.NatBlocks
import KappaMonoid.ForMathlib.TraceIdeal
import KappaMonoid.Core
import KappaMonoid.Core.Cardinal
import KappaMonoid.Core.Free
import KappaMonoid.Core.OrderUnit
import KappaMonoid.Core.Cyclic
import KappaMonoid.Core.AddOf
import KappaMonoid.Braiding
import KappaMonoid.Braiding.Saturated
import KappaMonoid.Axioms
import KappaMonoid.Modules
import KappaMonoid.Modules.Rings.ProjOrderUnit
import KappaMonoid.Modules.Rings.FreeModules
import KappaMonoid.Modules.Rings.FreeUnit
import KappaMonoid.Modules.Rings.Realisation
import KappaMonoid.Modules.Rings.Semisimple
import KappaMonoid.Modules.Corollary47
import KappaMonoid.Examples
import KappaMonoid.TwoGen
import KappaMonoid.Paper
