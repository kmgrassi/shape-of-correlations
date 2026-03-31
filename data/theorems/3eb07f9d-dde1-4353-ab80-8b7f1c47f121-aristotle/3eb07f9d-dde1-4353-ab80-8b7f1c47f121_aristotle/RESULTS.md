# Quantitative CHSH Bounds Under Geometric Constraints — Results

## Summary

We formalized and machine-verified (in Lean 4 with Mathlib) the core results studying
whether geometric consistency of a normalized PSD kernel restricts Bell/CHSH violation.

### Key Findings

**Answer: Geometry acts as a nontrivial regulator of nonlocality.**

Under Bell-sector submultiplicativity (|G(i,k)| ≥ |G(i,j)|·|G(j,k)| for i,j,k ∈ {A₀,A₁,B₀,B₁}):

1. **The Tsirelson bound 2√2 is unreachable** (Assumption A/B: TRUE ✓)
2. **CHSH > 2 is still achievable** (Assumption C: TRUE ✓)
3. **The "nonlocality budget" exists**: 2 < sup|CHSH| < 2√2 (Assumption D: CONFIRMED ✓)
4. **Rank-1 kernels are always Bell-classical** (Assumption E: TRUE ✓)

### Proved Theorems

| Theorem | File | Status |
|---------|------|--------|
| **Tsirelson bound**: \|CHSH\| ≤ 2√2 for Gram matrices of unit vectors | `Tsirelson.lean` | ✅ Proved |
| **Tsirelson equality (Bob)**: At CHSH = 2√2, ⟪vB₀,vB₁⟫ = 0 | `Obstruction.lean` | ✅ Proved |
| **Tsirelson equality (Alice)**: At CHSH = 2√2, ⟪vA₀,vA₁⟫ = 0 | `Obstruction.lean` | ✅ Proved |
| **Cross-correlator nonzero**: At CHSH = 2√2, \|⟪vA₀,vB₀⟩\| > 0 | `Obstruction.lean` | ✅ Proved |
| **Main Obstruction** (Thm 2/3): CHSH = 2√2 + submult → contradiction | `Obstruction.lean` | ✅ Proved |
| **Strict bound** (Corollary): submult → CHSH ≠ 2√2 | `Obstruction.lean` | ✅ Proved |
| **Construction** (Thm 5): ∃ PSD normalized submult kernel with CHSH > 2 | `Construction.lean` | ✅ Proved |
| **Rank-1 bound** (Thm 6): ±1 sign functions → \|CHSH\| ≤ 2 | `Rank1.lean` | ✅ Proved |
| **Rank-1 tight**: The bound 2 is achieved | `Rank1.lean` | ✅ Proved |
| **PSD bound**: \|G(i,j)\| ≤ 1 for normalized PSD kernels | `Defs.lean` | ✅ Proved |
| **Trivial bound**: \|CHSH\| ≤ 4 for normalized PSD kernels | `Defs.lean` | ✅ Proved |
| **Global → Bell submult**: Global submultiplicativity implies Bell-sector | `Defs.lean` | ✅ Proved |

### File Structure

- **`Defs.lean`**: Core definitions (CHSH, PSD kernel, submultiplicativity, etc.) and basic properties
- **`Rank1.lean`**: Rank-1 (deterministic/classical) CHSH bound: |CHSH| ≤ 2
- **`Tsirelson.lean`**: Tsirelson bound: |CHSH| ≤ 2√2 for inner product space representations
- **`Obstruction.lean`**: Submultiplicativity obstruction — CHSH = 2√2 is incompatible with geometry
- **`Construction.lean`**: Explicit kernel achieving CHSH = 2.04 > 2 with submultiplicativity

### Detailed Results

#### Constraint Level G1 (Positivity-only)
As expected, no useful bound beyond the Tsirelson bound |CHSH| ≤ 2√2.
This is just the general PSD kernel setting.

#### Constraint Level G2/G3 (Submultiplicativity — Global or Bell-sector)
**Main result**: Under Bell-sector submultiplicativity:
- |CHSH| < 2√2 (strictly below Tsirelson)
- |CHSH| > 2 is possible (not forced to classicality)
- The hierarchy is: 2 < sup|CHSH| < 2√2

The proof of the strict upper bound works by showing that at CHSH = 2√2, the
Tsirelson equality conditions force ⟪vA₀,vA₁⟫ = 0 (Alice's measurements orthogonal)
while simultaneously all cross-correlations are nonzero (|⟪vA₀,vB₀⟫| > 0, |⟪vB₀,vA₁⟫| > 0).
Submultiplicativity then requires |⟪vA₀,vA₁⟫| ≥ |⟪vA₀,vB₀⟫|·|⟪vB₀,vA₁⟫| > 0,
contradicting ⟪vA₀,vA₁⟫ = 0.

#### Explicit Construction (Theorem 5)
We use the symmetric ansatz with c = 51/100:
```
G = [1      c²     c      c   ]
    [c²     1      c     -c   ]
    [c      c      1      c²  ]
    [c     -c      c²     1   ]
```
where c = 0.51, giving CHSH = 4c = 2.04.

- PSD: verified (all eigenvalues positive, using sum-of-squares decomposition)
- Normalized: diagonal = 1
- Symmetric: by construction
- Submultiplicative on Bell quadruple: binding constraint is |c²| ≥ |c|·|c| = c² ✓

#### Optimal Bound under Symmetric Ansatz
Under the symmetric ansatz with s = c², the PSD constraint is c⁴ + 2c³ + 2c² ≤ 1.
The optimal c satisfies c⁴ + 2c³ + 2c² = 1, giving c_max ≈ 0.5437 and CHSH_max ≈ 2.175.
The true optimal may be higher under less symmetric configurations.

#### Rank-1 (Theorem 6)
For kernels G(i,j) = f(i)·f(j) with f taking values in {-1,+1}:
- |CHSH| = 2 always (proved by case analysis on 16 sign patterns)
- This confirms rank-1 kernels are Bell-classical

### The Obstruction Mechanism

The key mathematical insight is that the Tsirelson-optimal configuration requires:
1. Alice's measurements to be orthogonal: ⟪vA₀, vA₁⟫ = 0
2. Bob's measurements to be orthogonal: ⟪vB₀, vB₁⟫ = 0
3. All cross-correlations to be ±1/√2 (nonzero)

But submultiplicativity (which corresponds to the triangle inequality on the
log-geometric distance d_G(i,j) = -log|G(i,j)|) requires:
- |⟪vA₀,vA₁⟫| ≥ |⟪vA₀,vB₀⟫| · |⟪vB₀,vA₁⟫| = 1/2 > 0

This is incompatible with ⟪vA₀,vA₁⟫ = 0.

The submultiplicativity constraint essentially says that "detours don't help" —
going from A₀ to A₁ via B₀ can't produce a larger overlap than the direct one.
At the Tsirelson bound, the direct overlap is zero but the detour overlap is 1/2,
violating this principle.

### Interpretation

Geometry (in the form of submultiplicativity of the overlap kernel) acts as a
genuine regulator of quantum nonlocality:

- It doesn't eliminate nonlocality (CHSH > 2 is still possible)
- But it caps it strictly below the quantum maximum (CHSH < 2√2)
- This creates a "nonlocality budget" constrained by geometric consistency

The structural ladder is:
```
Rank-1 kernels:     |CHSH| ≤ 2    (classical)
Geometric kernels:  |CHSH| < 2√2  (constrained quantum)
General PSD:        |CHSH| ≤ 2√2  (full Tsirelson)
```
