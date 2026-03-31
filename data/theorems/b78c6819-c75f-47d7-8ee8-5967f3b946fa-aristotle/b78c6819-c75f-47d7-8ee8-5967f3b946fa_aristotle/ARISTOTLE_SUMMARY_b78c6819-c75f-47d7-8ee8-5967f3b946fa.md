# Summary of changes
## Completed Formalization: Tensor-Network Kernels, Metric Emergence, Entropy Bounds, and Causal Compatibility

All theorems are fully machine-verified in Lean 4 with Mathlib — zero sorries remain, and all proofs use only standard axioms (propext, Classical.choice, Quot.sound).

### File Structure

#### 1. `RequestProject/KernelMetric.lean` — Core: Correlation Kernel → Pseudometric/Metric

Defines a **CorrKernel** structure with symmetric, supermultiplicative kernel I : V → V → ℝ with values in (0,1] and I(i,i) = 1. Proves:

- **`dist_self`**: d(i,i) = 0
- **`dist_symm`**: d(i,j) = d(j,i) 
- **`dist_nonneg`**: d(i,j) ≥ 0
- **`dist_triangle`**: d(i,j) ≤ d(i,k) + d(k,j) — the triangle inequality from supermultiplicativity
- **`dist_pos_of_ne`**: d(i,j) > 0 for i ≠ j under separation (I(i,j) < 1)
- **`toPseudoMetricSpace`**: Bundles as a Mathlib `PseudoMetricSpace` instance
- **`counterexample_no_triangle`**: Constructs a symmetric positive kernel (without supermultiplicativity) that violates the triangle inequality, proving supermultiplicativity is **essential**

#### 2. `RequestProject/GraphKernel.lean` — Graph/Tensor-Network Realizations

- **`WeightedGraph.toCorrKernel`**: Given a metric graph (edge costs satisfy triangle inequality), constructs the CorrKernel via I(i,j) = e^{−c(i,j)}. Proves all five kernel axioms including supermultiplicativity from the triangle inequality.
- **`toCorrKernel_dist_eq`**: The kernel distance d = −log(e^{−c}) = c recovers the original graph cost.
- **`maxProduct_is_supermult`**: Any max-product path kernel (axiomatized by concatenation property I(i,k)·I(k,j) ≤ I(i,j)) yields a valid CorrKernel.
- **`transfer_cauchy_schwarz_bound`**: For a symmetric PSD Green's function G = (I−T)⁻¹, proves G(i,j)² ≤ G(i,i)·G(j,j) — a Cauchy-Schwarz bound giving kernel control from transfer matrices.

#### 3. `RequestProject/EntropyObserver.lean` — Entropy Bounds → Finite Observer-Measure

- **`observer_measure_bounded`**: ∑ c(s) ≤ |S| · c_max (basic bound from uniform content bound)
- **`observer_measure_entropy_bound`**: If |S| ≤ e^{S_max} and c_max ≥ 0, then ∑ c(s) ≤ e^{S_max} · c_max
- **`area_law_state_count`**: With N ≤ D^A states and bounded content, observer-measure ≤ D^A · c_max
- **`area_law_entropy`**: exp(A · log D) = D^A — the area-law entropy identity
- **`holographic_observer_bound`**: Holographic entropy bound S ≤ Area/(4G_N) implies finite observer-measure ≤ exp(Area/(4G_N)) · c_max
- **`unbounded_without_entropy_bound`**: Without entropy bounds, observer-measure can be arbitrarily large (counterexample)

#### 4. `RequestProject/CausalCounter.lean` — Causal Compatibility and Counterexamples

- **`metric_does_not_determine_order`**: The discrete metric on Fin 2 admits two distinct strict total orders (0 < 1 and 1 < 0), proving **metric alone cannot determine causal structure**.
- **`isometry_prevents_canonical_order`**: Any metric space with a nontrivial isometry σ cannot have an isometry-compatible strict linear order — proved via the cycle argument (σ^n = id on finite types creates contradictory chains).
- **`CausalMetric` structure**: Defines metric + partial order as a "Lorentzian-style" structure.
- **`diamond_in_ball`**: Causal diamonds are metrically bounded under a geodesic compatibility condition.
- **`lorentzian_needs_nontrivial_order`**: If the causal order is trivial, all causal diamonds are singletons.

### Key Mathematical Insights Formalized

1. **Metric emergence is generic**: Any supermultiplicative symmetric kernel on (0,1] yields a pseudometric via d = −log I. This works for shortest-path kernels, max-product path kernels, and transfer-matrix Green's functions.
2. **Supermultiplicativity is necessary**: Without it, the triangle inequality fails (explicit counterexample on 3 points).
3. **Holographic entropy bounds regularize observer counting**: Area-law bounds (N ≤ D^A) combined with bounded observer content give finite observer-measure. This formalizes "holographic-style entropy bounds regularize observer counting."
4. **Metric ≠ causality**: Metric emergence gives spatial/kinematic structure only. Causal order requires additional antisymmetric data. Isometry symmetry fundamentally prevents canonical causal ordering.