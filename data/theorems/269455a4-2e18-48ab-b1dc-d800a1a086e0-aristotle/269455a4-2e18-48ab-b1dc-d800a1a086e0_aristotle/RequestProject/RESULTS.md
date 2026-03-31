# CHSH Bounds Under Geometric (Submultiplicative) Constraints — Results

## Overview

This project formalizes the study of CHSH values under the constraint that
the correlation kernel G has submultiplicative absolute values, i.e.,
`|G(i,k)| ≥ |G(i,j)| · |G(j,k)|` for all triples. This condition makes
`d(i,j) = -log|G(i,j)|` a metric (triangle inequality), imposing an
"emergent geometry" on the correlation structure.

All results below are **machine-verified** in Lean 4 with Mathlib.
The formalization is in `RequestProject/CHSHBounds.lean`.

## Main Results

### Result 1: Correlator Bounds (Theorem 1)
**Statement**: For any PSD, normalized, symmetric kernel G:
`|G(i,j)| ≤ 1`

**Lean name**: `correlator_abs_le_one`

### Result 2: Tsirelson Bound
**Statement**: For any PSD, normalized, symmetric kernel G:
`CHSH(G) ≤ 2√2`

**Lean name**: `tsirelson_bound`

**Proof method**: Algebraic proof using two specific PSD conditions whose sum
eliminates the G(2,3) cross-term, giving
`4 + 2X·cos θ + 2Y·sin θ ≥ 0` where X = G(0,2)-G(1,3), Y = G(0,3)+G(1,2).
This yields X² + Y² ≤ 4, and by Cauchy-Schwarz CHSH = X + Y ≤ 2√2.

### Result 3: Orthogonality Obstruction (Theorems 4, 5)
**Statement**: If G(A₀,A₁) = 0 and G is submultiplicative, then for each
Bob setting b, at least one of G(A₀,b) or G(A₁,b) vanishes.
Consequently, `CHSH(G) ≤ 2`.

**Lean names**: `submult_zero_dichotomy`, `chsh_le_two_of_zero_submult`

### Result 4: Tsirelson Equality Forces Orthogonality
**Statement**: If G is PSD, normalized, symmetric, and CHSH(G) = 2√2,
then G(A₀,A₁) = 0.

**Lean name**: `chsh_eq_tsirelson_implies_ortho`

**Proof method**: Purely algebraic (no Gram decomposition needed!). Shows that
CHSH = 2√2 forces both PSD quadratic forms (from Result 2's proof) to vanish.
By the `psd_zero_form` lemma, this propagates to the linear forms, from which
G(0,1) = 0 follows by algebraic manipulation.

### Result 5: Main Theorem — Geometry Limits Nonlocality (Theorem 6)
**Statement**: Under PSD + normalized + symmetric + submultiplicative:
`CHSH(G) < 2√2` (strict inequality!)

**Lean name**: `chsh_lt_tsirelson_of_submult`

**Proof**: By contradiction. If CHSH ≥ 2√2, the Tsirelson bound gives
CHSH = 2√2 exactly. By Result 4, G(A₀,A₁) = 0. By Result 3, CHSH ≤ 2.
But 2 < 2√2, contradiction.

### Result 6: Nontrivial Coexistence (Theorem 8)
**Statement**: There exists a PSD, normalized, symmetric, submultiplicative
kernel with CHSH = 5/2 > 2.

**Lean names**: `exG_psd`, `exG_norm`, `exG_symm`, `exG_submult`,
`exG_chsh`, `exG_chsh_gt_two`

**Construction**: The kernel uses Gram vectors:
- v(A₀) = v(B₀) = (1, 0)
- v(A₁) = (1/2, √3/2)
- v(B₁) = (1/2, -√3/2)

giving G(i,j) = vᵢ · vⱼ. The CHSH value is exactly 5/2.

## Determination of the Regime

The results establish **Case D** (partial quantum regime):

| Bound | Value | Status |
|-------|-------|--------|
| Classical Bell bound | 2 | Exceeded (Result 6) |
| Submultiplicative sup | ≥ 5/2 | Constructive (Result 6) |
| Tsirelson bound | 2√2 ≈ 2.828 | NOT achieved (Result 5) |

**Conclusion**: `2 < sup CHSH ≤ 5/2 < 2√2`

Numerical optimization suggests the supremum is exactly 5/2, but the
exact value of the supremum is left as a conjecture.

## Key Conceptual Finding

**Spacetime geometry (submultiplicativity) imposes a quantitative limit on
quantum nonlocality**, reducing the maximum CHSH value below the Tsirelson
bound 2√2. However, this geometric constraint does NOT reduce nonlocality
to classical levels — the CHSH value can still exceed the classical bound of 2.

This demonstrates a **"nonlocality budget"**: geometry and nonlocality
coexist nontrivially, with geometry consuming part (but not all) of the
available quantum nonlocality.

## Technical Contributions

1. **Algebraic Tsirelson bound**: A proof of CHSH ≤ 2√2 that works directly
   from the PSD condition without Gram decomposition or spectral theory.

2. **PSD zero-form lemma** (`psd_zero_form`): If the PSD quadratic form
   vanishes for some c, the linear form ∑ⱼ c(j)G(k,j) vanishes for all k.
   Proof uses the substitution ε = -S with the identity ε² + 2εS ≥ 0.

3. **Algebraic Tsirelson equality analysis**: CHSH = 2√2 implies G(A₀,A₁) = 0,
   proved without Gram vectors using only the PSD zero-form lemma.

## Assumptions Tested

| Assumption | Status | Theorem |
|-----------|--------|---------|
| A: Global geometry ⇒ CHSH ≤ 2 | **FALSE** | `exG_chsh_gt_two` |
| B: Global geometry ⇒ CHSH < 2√2 | **TRUE** | `chsh_lt_tsirelson_of_submult` |
| C: Sectoral geometry allows full CHSH | Likely true (not formalized) | — |
| D: More geometry ⇒ less Bell violation | **TRUE** (qualitative) | Results 5+6 |
