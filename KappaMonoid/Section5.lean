/-
**Section 5** of

  Zahra Nazemian and Daniel Smertnig,
  *A monoid-theoretical approach to infinite direct-sum decompositions of modules*:

*Realization to hereditary rings for two-generated `ℵ₀`-monoids.*

Section 5 classifies the non-cyclic `ℵ₀`-monoids on two generators that arise as `V^{ℵ₀}(R)` for a
hereditary ring.  It is written throughout in terms of *forms* `α X₁ + β X₂` with coefficients in
`{0, 1, 2, …, ℵ₀}`, encoded as `ℕ∞` and pushed into `Cardinal` by `Cardinal.ofENat`.

| File | Contents |
|---|---|
| `Section5/Forms.lean` | the encoding: `Form`, `ecmul`, `eval`, `FormIdx`, `familyOfForm`, `slots`, `BraidedForms`, `exists_form` |
| `Section5/Braided.lean` | **Lemma 5.1** and **Lemma 5.2**(1)–(5), with the fibre and block machinery they run on |
| `Section5/Realization.lean` | **Theorem 5.3**, both directions |
| `Section5/Trace.lean` | **Proposition 5.4** and its hereditary half |
| `Section5/Corollary55.lean` | **Corollary 5.5**(1)(2)(3) |
| `Section5/Counterexample.lean` | `ℕ₀² ∪ {∞}`, the witness for the two "the converse is not true" claims |

Theorem 5.3 and Corollary 5.5 use no axiom beyond A5, which enters through Corollary 4.7(1);
Proposition 5.4 uses none.  The trace ideal itself, the `ℕ` block combinatorics and three `finsum`
facts are general and live in `KappaMonoid/ForMathlib/`.

See `SECTION5-PLAN.md` for the record of the work, and `README.md` for the statements that had to be
corrected on the way.
-/
import KappaMonoid.Section5.Forms
import KappaMonoid.Section5.Braided
import KappaMonoid.Section5.Realization
import KappaMonoid.Section5.Trace
import KappaMonoid.Section5.Corollary55
import KappaMonoid.Section5.Counterexample
