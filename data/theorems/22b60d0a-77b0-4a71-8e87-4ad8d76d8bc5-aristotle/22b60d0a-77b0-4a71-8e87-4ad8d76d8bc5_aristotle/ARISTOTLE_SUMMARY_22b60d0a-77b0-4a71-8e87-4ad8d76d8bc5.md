# Summary of changes
# Classification of Common-Origin Kernels: Complete Formalization

## Summary

I have formalized and **fully proved** (zero sorries, standard axioms only) a comprehensive classification theory for normalized PSD relational kernels, studying the interplay between metric emergence and Bell violation.

## Files Created

- **`RequestProject/Defs.lean`** — Core definitions:
  - Common-origin kernel properties (`IsSymmetric`, `IsNormalized`, `IsPSD`, `IsCommonOriginKernel`)
  - Geometry predicates (`GlobalGeometry`, `SectorGeometry`, `GlobalSubmult`, `AllPositive`)
  - Bell predicates (`CHSH_value`, `BellViolating`, `TrivialBell`, `eta`)
  - Concrete kernel families (`constKernel`, `rank1Kernel`, `chshKernel`)
  - Structural predicates (`IsRank1`, `GlobalCoexistence`, `SectoralCoexistence`)

- **`RequestProject/Theorems.lean`** — All theorems, fully proved:

- **`RequestProject/README.md`** — Detailed documentation with tables of results

## Proven Theorems

### Main Classification (Theorems 1–3)
- **Theorem 1**: ∃ G with BellViolating(G) ∧ ¬GlobalGeometry(G) — *CHSH kernel witnesses this*
- **Theorem 2**: ∃ G with GlobalGeometry(G) ∧ TrivialBell(G) — *constant kernel witnesses this*
- **Theorem 3**: ∃ G, T with SectorGeometry(G,T) ∧ BellViolating(G) — *CHSH kernel with T={A₀,B₀}*

### Failure Structure (Theorem 4)
- Complete **iff-characterization** of all submultiplicativity failure triples in the CHSH kernel (exactly 8 triples, all crossing through orthogonal pairs)

### Rank-1 Obstruction (Theorem 6)
- **Rank-1 kernels are always Bell-trivial**: if G(i,j) = v(i)·v(j) with v(i)²=1, then |CHSH| ≤ 2
- Rank-1 sign kernels always satisfy GlobalGeometry
- Rank-1 kernels are provably in the "geometry only" class

### Sector Decomposition (Theorem 8)
- The CHSH kernel admits a sector decomposition with geometric and Bell sectors

### Necessary Conditions (Theorem 10)
- GlobalCoexistence (both geometry and Bell) requires rank > 1

### Maximal CHSH No-Go (Theorem 11) — *Deepest result*
- **Weak form**: The CHSH-optimal kernel achieves CHSH = 2√2 and ¬GlobalGeometry
- **Structural form**: **Any** normalized PSD kernel with CHSH = 2√2 must have G(A₀,A₁) = 0, preventing GlobalGeometry. This is proved via a Tsirelson-bound argument decomposed into:
  - PSD discriminant bounds: (G(0,2)+G(1,2))² ≤ 2+2α, (G(0,3)−G(1,3))² ≤ 2−2α
  - √(2+2α) + √(2−2α) ≤ 2√2 with equality iff α = 0

### Assumption Verification
- **A (FALSE)**: Bell + geometry are NOT automatically compatible
- **B (FALSE sectorally)**: Sector coexistence IS possible
- **C (TRUE)**: Rank-1 kernels cannot support Bell violation
- **D (TRUE)**: Maximal CHSH incompatible with global geometry (proved structurally for all PSD kernels)
- **E (EVIDENCE)**: Bell and geometry are indeed different sectors of one object

## Mathematical Conclusion

The formalization establishes that **only sectoral coexistence is robust**: geometry and Bell nonlocality are different sectors of one common-origin kernel, rather than the same feature. Maximal quantum nonlocality structurally competes with global metric emergence.