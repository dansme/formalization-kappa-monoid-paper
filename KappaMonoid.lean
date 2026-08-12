/-
A formalisation of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*,

covering Sections 2–5.

The core — the definitions every section runs on — is at the top level; each section's own material
sits under `Section2/`, `Section3/`, `Section4/`, `Section5/`.  `ForMathlib/` holds the pieces with
no `κ`-monoid content and no dependence on the rest, so they compile once.
-/
import KappaMonoid.ForMathlib.Finprod
import KappaMonoid.ForMathlib.NatBlocks
import KappaMonoid.ForMathlib.TraceIdeal
import KappaMonoid.Basic
import KappaMonoid.Braiding
import KappaMonoid.Universal
import KappaMonoid.ModuleClass
import KappaMonoid.Axioms
import KappaMonoid.Section2.Examples
import KappaMonoid.Section2.Free
import KappaMonoid.Section2.OrderUnit
import KappaMonoid.Section2.Cyclic
import KappaMonoid.Section2.Rings.ProjOrderUnit
import KappaMonoid.Section2.Rings.FreeModules
import KappaMonoid.Section2.Rings.FreeUnit
import KappaMonoid.Section2.Rings.Realisation
import KappaMonoid.Section2.Rings.Semisimple
import KappaMonoid.Section3.Diophantine
import KappaMonoid.Section3.Reals
import KappaMonoid.Section4.AddOf
import KappaMonoid.Section5
