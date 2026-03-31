# Summary of changes
## Completed: Causal Order as Extra Relational Data on Emergent Metric Geometry

All definitions, theorems, and proofs have been formalized in Lean 4 with Mathlib, compiling with **zero sorries** and only standard axioms (propext, Classical.choice, Quot.sound).

### File Structure

- **`RequestProject/Defs.lean`** — Core definitions: `SymmetricKernel`, `emergentDist`, `CausalRelation`, `CausalMetric`, `AntisymmetricKernel`, `TimeSeparation`, `PropagationKernel`, causal diamonds, compatibility conditions (diamond boundedness, geodesic compatibility).

- **`RequestProject/Metric.lean`** — Proves that the emergent distance d(i,j) = −log I(i,j) from a symmetric kernel forms a pseudometric: nonnegativity, self-distance zero, symmetry, and triangle inequality (from supermultiplicativity).

- **`RequestProject/Negative.lean`** — **Negative theorems and toy models** proving metric alone cannot determine causality:
  - **Theorem 1**: Two-point space admits two distinct causal orders with the same metric.
  - **Theorem 2**: No strict total order on Fin 2 is invariant under the swap isometry (requires asymmetry).
  - **Theorem 3**: Symmetric kernels are invariant under causal reversal, so cannot encode orientation.
  - **Models A/B/C**: Two-point, three-point line, and four-point cycle examples all demonstrating underdetermination.

- **`RequestProject/Positive.lean`** — **Positive theorems** showing antisymmetric data suffices:
  - **Theorem 4**: An antisymmetric kernel (A(i,j) = −A(j,i)) has zero diagonal, irreflexive and asymmetric induced relation; under transitivity it yields a strict partial order.
  - **Theorem 5**: Any metric + causal relation packages into a well-defined CausalMetric.
  - **Theorem 6**: Diamond boundedness can fail — explicit counterexample with incompatible metric and order.
  - **Theorem 7**: Empty causal relation gives empty causal diamonds.
  - **Theorem 8**: No strict total order on the 4-point cycle satisfies geodesic compatibility.

- **`RequestProject/Lorentzian.lean`** — **Lorentzian structure and propagation**:
  - **Theorem 9**: Same metric supports different time-separations; same order coexists with different metrics.
  - **Theorem 10**: A metric alone is insufficient for Lorentzian structure — two distinct Lorentzian extensions share the same metric but differ in τ.
  - **Theorem 11**: Directed propagation induces a causal order under acyclicity and transitivity.

- **`RequestProject/Assumptions.lean`** — **Tests all five assumptions**:
  - **A** ("Geometry determines causality"): **FALSE** — proved via Theorem 1.
  - **B** ("Symmetric kernel determines time arrow"): **FALSE** — kernel is invariant under reversal.
  - **C** ("Antisymmetric data suffices for causal order"): **TRUE** under acyclicity/transitivity — via Theorem 4.
  - **D** ("Metric + order gives spacetime"): **PARTIALLY TRUE** — structure always exists, but compatibility conditions are nontrivial and can fail.
  - **E** ("Causal structure from propagation"): **CONDITIONALLY TRUE** — via Theorem 11.

### Key Conceptual Result
The formalization rigorously establishes: **geometry can emerge from symmetric correlations (via d = −log I), but causality requires additional directed structure (antisymmetric kernel, propagation kernel, or time-separation function) and is not determined by metric geometry alone.**