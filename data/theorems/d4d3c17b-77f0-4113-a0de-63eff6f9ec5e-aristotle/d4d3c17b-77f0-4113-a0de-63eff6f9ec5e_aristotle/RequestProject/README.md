# Deriving Causal Order from Propagation Kernels

A Lean 4 formalization establishing that:
- **Geometry** comes from symmetric correlations (correlation kernel → emergent metric)
- **Causality** comes from directed propagation (propagation kernel → causal order)
- **Compatibility** between the two requires extra physical constraints (finite speed)

## File Structure

### `Basic.lean` — Core Definitions
- `CorrelationKernel`: symmetric kernel I with positivity, normalization, symmetry, supermultiplicativity
- `CorrelationKernel.d`: emergent metric d(i,j) = -log I(i,j)
- Metric properties: `d_nonneg`, `d_self`, `d_symm`, `d_triangle`
- `PropagationKernel`: time-indexed kernel K with nonnegativity, identity at zero, semigroup composition
- `PropagationKernel.causal`: derived causal relation i ≺_K j ⟺ ∃ t > 0, K_t(i,j) > 0
- `PropagationKernel.Acyclic`: acyclicity condition
- `PropagationKernel.diamond`: causal diamonds
- `FiniteSpeedPropagation`, `MetricBoundedDiamonds`, `CausalMonotonicity`: compatibility conditions

### `CoreTheorems.lean` — Theorems 1–3
- **Theorem 1** (`causal_irrefl`): Under acyclicity, ≺_K is irreflexive
- **Theorem 2** (`causal_trans`): Under semigroup law, ≺_K is transitive
- **Theorem 3** (`causal_strictPartialOrder`): Under both, ≺_K is a strict partial order
- **Assumption A** (`assumption_A_false`): Without acyclicity, irreflexivity can fail
- **Assumption B** (`assumption_B_true`): Semigroup + acyclicity suffice for strict partial order

### `Diamonds.lean` — Theorems 4–5
- **Theorem 4** (`diamond_empty_of_not_causal`, `diamond_implies_causal`): Diamonds are well-defined
- **Theorem 5** (`trivial_acyclic_diamonds_empty`): Trivial propagation gives empty diamonds

### `Compatibility.lean` — Theorems 6–7
- **Theorem 6 / Assumption C** (`assumption_C_false`): Metric compatibility is NOT automatic (counterexample on Fin 3)
- **Theorem 7** (`causal_respects_metric_cones`, `diamond_metrically_bounded`): Finite-speed propagation implies metric-causal compatibility
- **Assumption D** (`assumption_D_true`): Finite speed suffices for cone-like compatibility

### `ToyModels.lean` — Models A, B, C and Theorem 9
- **Model A** (Directed chain): `chainPropKernel`, `chainCorrKernel` on Fin(n+1)
  - `chain_acyclic`: chain is acyclic
  - `chain_causal_iff`: causal order = usual order on naturals
  - `chain_finite_speed`: finite-speed condition holds with v=1
- **Model C** (`symmetric_propagation_has_self_loops`): Symmetric propagation breaks acyclicity
- **Theorem 9** (`same_metric_different_causality`): Same metric, different causal orders possible

### `Frontier.lean` — Theorems 8, 10 and Assumption E
- **Theorem 8** (`earliest_arrival_subadditive`): Earliest arrival time is subadditive on causal chains
- **Theorem 10** (`CommonOrigin`): Common-origin structure yielding both metric and causal order
  - `CommonOrigin.corrKernel`: correlation kernel from cost function D
  - `CommonOrigin.propKernel`: propagation kernel from same structure
  - `CommonOrigin.finite_speed_propagation`: finite-speed compatibility from common origin
- **Assumption E** (`assumption_E`): Geometry and causality CAN come from the same structure

## Summary of Results

| Assumption | Expected | Proved |
|---|---|---|
| A: Propagation auto-defines causal order | False without acyclicity | ✓ `assumption_A_false` |
| B: Semigroup + acyclicity → strict partial order | True | ✓ `assumption_B_true` |
| C: Metric emergence auto-compatible | False | ✓ `assumption_C_false` |
| D: Finite speed → compatibility | True | ✓ `assumption_D_true` |
| E: Geometry & causality from same structure | Possible | ✓ `assumption_E` |

All theorems are fully machine-verified with no `sorry` and only standard axioms.
