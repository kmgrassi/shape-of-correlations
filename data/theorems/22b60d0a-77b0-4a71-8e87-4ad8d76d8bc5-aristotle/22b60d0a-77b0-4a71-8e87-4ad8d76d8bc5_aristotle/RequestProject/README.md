# Classification of Common-Origin Kernels Supporting Both Geometry and Bell Violation

## Overview

This project formalizes and proves a classification theory for **normalized PSD relational kernels** `G : S → S → ℝ`, studying which such kernels can simultaneously support:

1. **Metric emergence** via global or sectoral submultiplicativity of `|G(i,j)|` and `d_G(i,j) = -log|G(i,j)|`
2. **Bell violation** via CHSH correlations `E(a,b) = G(Aₐ, Bᵦ)` with `|CHSH| > 2`

## File Structure

- **`Defs.lean`**: Core definitions
  - Common-origin kernel properties (symmetric, normalized, PSD)
  - Geometry predicates (GlobalGeometry, SectorGeometry)
  - Bell predicates (BellViolating, TrivialBell, CHSH value)
  - Concrete kernel families (constant, rank-1, CHSH-optimal)

- **`Theorems.lean`**: All proven theorems (100% sorry-free)

## Proven Theorems

### Part III: Main Classification (Theorems 1-3)

| Theorem | Statement | Status |
|---------|-----------|--------|
| **Theorem 1** | ∃ G with BellViolating ∧ ¬GlobalGeometry | ✅ Proved |
| **Theorem 2** | ∃ G with GlobalGeometry ∧ TrivialBell | ✅ Proved |
| **Theorem 3** | ∃ G, T with SectorGeometry(G,T) ∧ BellViolating(G) | ✅ Proved |

### Part IV: Failure Structure (Theorem 4)

| Theorem | Statement | Status |
|---------|-----------|--------|
| **Theorem 4** | Complete characterization of submultiplicativity failure triples in CHSH kernel (8 specific triples identified, proved as iff) | ✅ Proved |

### Part V: Rank-1 Obstruction (Theorem 6)

| Theorem | Statement | Status |
|---------|-----------|--------|
| **Theorem 6** | Rank-1 normalized PSD kernels are always Bell-trivial | ✅ Proved |
| **Rank-1 GlobalGeometry** | Rank-1 sign kernels always satisfy GlobalGeometry | ✅ Proved |
| **Rank-1 classification** | Rank-1 kernels are in the "geometry only" class | ✅ Proved |

### Part VI: Sector Decomposition (Theorem 8)

| Theorem | Statement | Status |
|---------|-----------|--------|
| **Theorem 8** | CHSH kernel admits sector decomposition: T_geom = {A₀,B₀} has SectorGeometry, Bell violation via standard indices | ✅ Proved |

### Part VII: Necessary Conditions (Theorem 10)

| Theorem | Statement | Status |
|---------|-----------|--------|
| **Theorem 10** | GlobalCoexistence implies rank > 1 | ✅ Proved |

### Part VIII: Maximal CHSH No-Go (Theorem 11)

| Theorem | Statement | Status |
|---------|-----------|--------|
| **Theorem 11 (weak)** | CHSH-optimal kernel has CHSH = 2√2 and ¬GlobalGeometry | ✅ Proved |
| **Theorem 11 (structural)** | **Any** normalized PSD kernel with CHSH = 2√2 must have G(A₀,A₁) = 0, preventing GlobalGeometry | ✅ Proved |

The structural form of Theorem 11 is the deepest result: it proves via a Tsirelson-bound argument that maximal quantum nonlocality is incompatible with global metric emergence for **any** common-origin kernel, not just the specific CHSH-optimal construction.

### Part IX: Assumption Verification

| Assumption | Verdict | Status |
|------------|---------|--------|
| **A**: Bell + geometry automatically compatible | **FALSE** | ✅ Proved |
| **B**: No kernel can support both | **FALSE** (sectorally) | ✅ Proved |
| **C**: Rank-1 kernels cannot support Bell violation | **TRUE** | ✅ Proved |
| **D**: Maximal CHSH incompatible with global submultiplicativity | **TRUE** (for the standard construction, and structurally for any PSD kernel) | ✅ Proved |
| **E**: Bell and geometry are different sectors | **EVIDENCE** (sector decomposition exists) | ✅ Proved |

### Part X: Family Analysis

| Family | Geometry? | Bell violation? | Status |
|--------|-----------|----------------|--------|
| **A (constant)** | GlobalGeometry ✓ | TrivialBell ✓ | ✅ Proved |
| **A (rank-1 sign)** | GlobalGeometry ✓ | TrivialBell ✓ | ✅ Proved |
| **C (CHSH Gram)** | ¬GlobalGeometry ✗ | BellViolating ✓ | ✅ Proved |

## Key Mathematical Results

### The Classification Picture

The formalization establishes that:

1. **Global coexistence is obstructed**: Maximal CHSH = 2√2 forces zero entries in the kernel (G(A₀,A₁) = 0), which is structurally incompatible with GlobalGeometry. This is proved for arbitrary normalized PSD kernels, not just specific constructions.

2. **Sectoral coexistence is possible**: The same kernel (CHSH-optimal) can support both SectorGeometry on a subset and Bell violation globally.

3. **Low-rank obstruction**: Rank-1 kernels are necessarily in the "geometry only" class — they always satisfy GlobalGeometry and never violate Bell.

4. **Failure structure is characterized**: The exact set of triples where submultiplicativity fails in the CHSH kernel is completely determined (8 triples, all crossing through orthogonal pairs).

### Interpretation

The answer to the classification question is:
> **Only sectoral coexistence is robust.** Geometry and Bell nonlocality are different sectors of one deeper relational object (the common-origin kernel), rather than the same feature. Maximal nonlocality structurally competes with global metric emergence.

## Verification

All proofs compile without sorry, using only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
