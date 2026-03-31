# Summary of changes
## Emergent Space from Correlations — Fully Formalized

Created `RequestProject/EmergentSpace.lean` with a complete, sorry-free Lean 4 formalization of the "space lives inside the wave" framework. Everything compiles cleanly with only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

### What's formalized

**1. Correlation Structure** (`CorrStructure S`)  
A structure packaging a correlation function `corr : S → S → ℝ` with axioms:
- Strict positivity (`0 < corr i j`)
- Bounded by 1 (`corr i j ≤ 1`)
- Self-correlation is maximal (`corr i i = 1`)
- Symmetry (`corr i j = corr j i`)
- Submultiplicativity (`corr i k * corr k j ≤ corr i j`) — the key axiom

**2. Emergent Distance** (`d(i,j) = -log(corr(i,j))`)  
Proven to satisfy all four pseudometric axioms:
- `dist_nonneg`: non-negativity
- `dist_self`: `d(i,i) = 0`
- `dist_symm`: symmetry
- `dist_triangle`: triangle inequality (from submultiplicativity under `-log`)

**3. Metric Upgrade**  
`dist_eq_zero_iff_eq`: Under the *separation axiom* (`corr(i,j) = 1 → i = j`), the pseudometric becomes a genuine metric.

**4. Locality & Interaction Strength**  
- `isLocal_iff_corr_ge`: ε-locality ↔ `exp(-ε) ≤ corr(i,j)`
- `interaction_decreases_with_distance`: Any monotone function of correlation decreases with emergent distance
- `exp_interaction_eq_corr_pow`: Exponential decay `exp(-α·d) = corr^α`

**5. Metric Embedding**  
- `IsLowDistortionEmbedding`: Definition of (1+ε)-distortion embedding into ℝⁿ
- `embedding_preserves_locality`: If such an embedding exists, ε-local degrees of freedom map to Euclidean-nearby points — the formal statement of **"space lives inside the wave."**