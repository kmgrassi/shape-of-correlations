This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Correlation → Geometry → Locality

A Lean 4 formalization framework studying how geometry and locality can emerge
from purely informational/correlational structure, without presupposing
background space.

## Project Structure

All Lean files are in `RequestProject/CorrGeom/`:

| File | Contents |
|------|----------|
| `Defs.lean` | Core definitions: `CorrKernel`, `emergentDist`, coupling kernels, metric balls |
| `MetricEmergence.lean` | Theorems A1–A3, D1: pseudometric/metric axioms, coupling = kernel |
| `Counterexamples.lean` | Theorems B1–B3: triangle inequality not automatic, equivalence result, non-separating kernels |
| `ToyModels.lean` | Theorems C1–C2, E2–E3: chain kernel, grid kernel, embedding recovery |
| `Embedding.lean` | Theorems C3–C5, E4: no low-dimensional embedding, equilateral/star kernels |
| `Locality.lean` | Theorems D2–D3: locality requires monotone coupling, exponential decay locality |
| `Wave.lean` | Theorems F1, F3: relational interference, two-path model |

The main import file is `RequestProject/CorrGeom.lean`.

## Summary of Results

### ✅ All 30+ theorems are fully machine-verified (zero sorries)

### Part I: Core Definitions
- **`CorrKernel S`**: Symmetric correlation kernel I : S → S → ℝ with 0 < I(i,j) ≤ 1, I(i,i) = 1
- **`emergentDist K i j`**: d(i,j) = -log(I(i,j))
- **`expCoupling`**, **`ratCoupling`**: Interaction strength from emergent distance

### Part II: Metric Emergence (Positive Theorems)
- **A1** (`emergentDist_nonneg`, `emergentDist_self`, `emergentDist_symm`): d ≥ 0, d(i,i) = 0, d(i,j) = d(j,i)
- **A2** (`emergentDist_triangle`): Multiplicative triangle I(i,k) ≥ I(i,j)·I(j,k) ⟹ d(i,k) ≤ d(i,j) + d(j,k)
- **A3** (`emergentDist_eq_zero_iff`): I(i,j) = 1 ↔ i = j ⟹ d(i,j) = 0 ↔ i = j (metric)
- **D1** (`expCoupling_eq_kernel`, `expCoupling_monotone`): exp(-d) recovers I, and is monotone

### Part III: Counterexamples / Stress Tests
- **B1** (`triangle_not_automatic`): Explicit kernel on Fin 3 where d fails triangle inequality, showing the multiplicative assumption is needed
- **B2** (`mult_triangle_iff_triangle`): **Surprising result**: The multiplicative triangle inequality is not just sufficient but *equivalent* to the metric triangle inequality. This means B2 as originally posed (find a metric that violates multiplicative triangle) is impossible.
- **B3** (`non_separating_not_metric`): Constant-1 kernel gives d ≡ 0, a pseudometric but not a metric

### Part IV: Embedding / Emergent Geometry
- **C1** (`line_embedding_recovers_dist`): I = exp(-|x_i - x_j|) ⟹ d = |x_i - x_j|
- **C2** (`euclidean_embedding_recovers_dist`): I = exp(-‖x_i - x_j‖) ⟹ d = ‖x_i - x_j‖
- **C3** (`no_line_embedding_equilateral`): Equilateral kernel on Fin 3 cannot embed in ℝ¹
- **C4** (`no_plane_embedding_equilateral`): Equilateral kernel on Fin 4 cannot embed in ℝ²
- **C5** (`finite_metric_is_graph_metric`): Every finite metric trivially embeds in a complete weighted graph

### Part V: Toy Models
- **E2** (`chainKernel_dist`, `chainKernel_mult_triangle`, `chain_coupling_decreases_with_dist`): Chain kernel I = exp(-α|i-j|) recovers exact line geometry; coupling decreases with distance
- **E3** (`gridKernel_dist`, `gridKernel_mult_triangle`): Grid kernel recovers Manhattan geometry
- **E4** (`star_dist_center`, `star_dist_nonzero`, `star_ball_jump`): Star kernel has bizarre ball growth (jumps from 1 to n+1 at radius 1)

### Part VI: Locality
- **D2** (`locality_requires_monotone_coupling`): Non-monotone couplings exist, so geometry alone doesn't force locality
- **D3** (`expCoupling_locality`): Exponential coupling gives effective locality (interactions bounded by exp(-R) beyond radius R)
- (`perverse_coupling_anti_local`): Explicit anti-local coupling showing locality is not automatic

### Part VII: Wave / Interference
- **F1** (`interference_relational`): |ψ₁+ψ₂|² = |ψ₁|² + |ψ₂|² + 2Re(ψ₁·conj(ψ₂)) — NO geometric assumptions needed
- **F3** (`both_paths_cross_term`, `single_path_no_cross_term`): Two-path model shows cross terms appear/disappear based on path availability, not space

## Key Mathematical Insights Discovered

1. **Multiplicative ↔ Metric Triangle**: The multiplicative correlation inequality I(i,k) ≥ I(i,j)·I(j,k) is not just sufficient but *exactly equivalent* to the triangle inequality for d = -log(I). This means there is no weaker condition on I that still gives a metric.

2. **Geometry is not automatic**: The counterexample (B1) shows that natural-looking correlation kernels can fail the triangle inequality. The multiplicative condition is genuinely restrictive.

3. **Low-dimensional space is not guaranteed**: Equilateral kernels produce valid metrics that cannot embed in ℝ¹ or ℝ², showing that "metric from information" ≠ "ordinary physical space."

4. **Locality requires coupling assumptions**: Having a good metric is necessary but not sufficient for local physics. The dynamics must respect the geometry (monotone coupling).

5. **Interference is purely relational**: The interference identity is a consequence of complex algebra alone, requiring no spatial structure whatsoever.

## Tested Assumptions (Part VIII)

| # | Assumption | Verdict |
|---|-----------|---------|
| 1 | "Correlation always induces a physically meaningful metric" | **FALSE** without multiplicative triangle (B1) |
| 2 | "Metricity implies Euclidean or low-dimensional geometry" | **FALSE** — equilateral simplices refute this (C3, C4) |
| 3 | "Geometry alone implies locality" | **FALSE** without monotone coupling (D2) |
| 4 | "Interference requires background space" | **FALSE** — purely algebraic (F1) |
| 5 | "A relational information model naturally gives ordinary physical space" | **FALSE** without extra regularity — star kernel gives non-geometric ball growth (E4) |

## Building

```bash
lake build RequestProject.CorrGeom
```

All proofs compile with Lean 4.28.0 and Mathlib v4.28.0. No sorry statements remain.
