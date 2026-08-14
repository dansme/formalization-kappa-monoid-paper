/-
**The paper layer**: what to read against the PDF.

`Definition21.lean` transcribes Definition 2.1 literally and shows it agrees with the working
definition.  `Section5.lean` restates every numbered result of §5 in the paper's own terms, over a
`Setting5` bundling the section's standing assumptions.  `Section2.lean`, `Section3.lean` and
`Section4.lean` are indices: one entry per numbered result, naming the declaration that formalises
it, and a closing section listing what the development deliberately does not formalise.

Nothing else in the development depends on this layer.
-/
import KappaMonoid.Paper.Definition21
import KappaMonoid.Paper.Section2
import KappaMonoid.Paper.Section3
import KappaMonoid.Paper.Section4
import KappaMonoid.Paper.Section5
