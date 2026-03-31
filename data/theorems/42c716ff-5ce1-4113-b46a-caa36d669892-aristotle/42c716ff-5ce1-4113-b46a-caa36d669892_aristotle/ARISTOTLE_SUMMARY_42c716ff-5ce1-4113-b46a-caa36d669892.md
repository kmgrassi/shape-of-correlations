# Summary of changes
## CHSH vs Geometric Consistency — Formal Verification

Created `RequestProject/CHSH.lean` containing a complete Lean 4 formalization of the CHSH vs geometric consistency curve. All theorems are fully proved with no `sorry` and only standard axioms.

### Mathematical Content

The formalization studies the 4×4 symmetric Bell-CHSH Gram matrix:

```
G(a,b,x) = [[1, a, x, x],
             [a, 1, x, -x],
             [x, x, 1, b],
             [x, -x, b, 1]]
```

under positive semidefiniteness and μ-submultiplicativity constraints (`a ≥ μx²`, `b ≥ μx²`).

### Proved Theorems

1. **PSD necessary conditions** (`psd_implies_alice_bound`, `psd_implies_bob_bound`): If G is PSD, then `a + 2x² ≤ 1` and `b + 2x² ≤ 1`. Proved by evaluating the quadratic form at cleverly chosen test vectors `(-1, 1, 0, 2x)` and `(0, 2x, -1, 1)`.

2. **CHSH upper bound** (`chsh_upper_bound`): Under PSD and μ-submultiplicativity with μ ≥ 0: **CHSH = 4x ≤ 4/√(2+μ)**. The key chain: `μx² ≤ a` and `a + 2x² ≤ 1` imply `(2+μ)x² ≤ 1`.

3. **Tsirelson achievability** (`tsirelson_matrix_psd`, `tsirelson_value`): The matrix G(0, 0, 1/√2) is PSD (proved via sum-of-squares decomposition: `v^T G v = (v₀ + v₂/√2 + v₃/√2)² + (v₁ + v₂/√2 - v₃/√2)²`), and achieves CHSH = 4/√2 = 2√2.

4. **Strict bound for μ > 0** (`chsh_strict_bound`): For any μ > 0, **CHSH < 2√2**. Any positive geometric consistency strictly reduces the maximum Bell violation.

5. **Monotonicity** (`chsh_bound_tightens`, `feasible_mono`): The bound 4/√(2+μ) is monotone decreasing in μ, and the feasible set shrinks as μ increases.

6. **Summary theorem** (`chsh_geometric_consistency`): Combines all results into a single statement.

### Physical Interpretation

The curve C(μ) ≤ 4/√(2+μ) quantifies the trade-off between Bell nonlocality and geometric consistency:
- **μ = 0**: No geometric constraint → Tsirelson bound 2√2 is achievable
- **μ > 0**: Geometric consistency forces CHSH < 2√2
- Experimental CHSH ≈ 2√2 implies μ ≈ 0 for the Bell sector, meaning Bell sectors of reality are very weakly geometric even if macroscopic space is strongly geometric.

### Note on the Upper Bound

The bound 4/√(2+μ) is derived from a necessary condition for PSD (the 3×3 principal minor condition). For μ = 0 it is tight (achieved by the Tsirelson matrix). For μ > 0, the true supremum C(μ) may be strictly below 4/√(2+μ) due to the full 4×4 PSD condition being more restrictive. The formalization establishes 4/√(2+μ) as a rigorous upper bound, which suffices for the qualitative conclusions.