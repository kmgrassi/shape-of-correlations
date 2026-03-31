/-
# Correlation → Geometry → Locality

A formalization framework studying how geometry and locality can emerge
from purely informational/correlational structure, without presupposing
background space.

## Main Results

### Part I: Core Definitions (Defs.lean)
- `CorrKernel`: Symmetric correlation kernel with positivity, normalization, boundedness
- `emergentDist`: d(i,j) = -log(I(i,j))
- `expCoupling`, `ratCoupling`: Interaction strength from emergent distance

### Part II: Metric Emergence (MetricEmergence.lean)
- **A1**: d is nonneg, symmetric, zero on diagonal (pseudometric axioms)
- **A2**: Multiplicative triangle inequality ⟹ d satisfies triangle inequality
- **A3**: Separation axiom ⟹ d is a metric
- **D1**: exp(-d) = I (coupling recovers kernel), monotonicity

### Part III: Counterexamples (Counterexamples.lean)
- **B1**: Triangle inequality is NOT automatic from basic axioms
- **B2**: Multiplicative triangle is equivalent to metric triangle (not just sufficient!)
- **B3**: Non-separating kernels give pseudometrics, not metrics

### Part IV: Embedding (Embedding.lean)
- **C3/C4**: Metrics need not embed into ℝ¹ or ℝ² (equilateral counterexample)
- **E4**: Non-geometric kernel with bizarre ball growth (star kernel)

### Part V: Toy Models (ToyModels.lean)
- **C1/E2**: Chain kernel I = exp(-α|i-j|) recovers exact line geometry
- **C2/E3**: Grid kernel recovers Manhattan geometry
- Line/Euclidean embedding recovery theorems

### Part VI: Locality (Locality.lean)
- **D2**: Locality fails without monotone coupling
- **D3**: Exponential coupling gives effective locality

### Part VII: Wave (Wave.lean)
- **F1**: Interference identity is purely relational (no space needed)
- **F3**: Two-path model: cross terms present/absent based on paths
-/
import RequestProject.CorrGeom.Defs
import RequestProject.CorrGeom.MetricEmergence
import RequestProject.CorrGeom.Counterexamples
import RequestProject.CorrGeom.ToyModels
import RequestProject.CorrGeom.Embedding
import RequestProject.CorrGeom.Locality
import RequestProject.CorrGeom.Wave
