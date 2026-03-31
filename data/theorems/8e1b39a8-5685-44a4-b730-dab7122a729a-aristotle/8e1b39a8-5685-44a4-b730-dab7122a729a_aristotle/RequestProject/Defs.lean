import Mathlib

/-!
# Physical Interpretations of μ — Core Definitions

This file contains the core definitions for interpreting μ as a physical quantity
in the context of approximate submultiplicativity of kernels.

Given a kernel G : α → α → ℝ, we define:
- `ApproxSubmult μ G`: the condition |G(i,k)| ≥ μ · |G(i,j)| · |G(j,k)|
- `ExactSubmult G`: the special case μ = 1
- `muParam G`: the maximal consistency parameter μ(G)
- `consistencyRatio G i j k`: the ratio |G(i,k)| / (|G(i,j)| · |G(j,k)|)
- `HasNondegTriple G`: existence of a triple with positive denominator
-/

noncomputable section

open Real

variable {α : Type*}

/-- Approximate submultiplicativity: |G(i,k)| ≥ μ · |G(i,j)| · |G(j,k)| for all triples. -/
def ApproxSubmult (μ : ℝ) (G : α → α → ℝ) : Prop :=
  ∀ i j k, |G i k| ≥ μ * |G i j| * |G j k|

/-- Exact submultiplicativity: |G(i,k)| ≥ |G(i,j)| · |G(j,k)| for all triples. -/
def ExactSubmult (G : α → α → ℝ) : Prop :=
  ∀ i j k, |G i k| ≥ |G i j| * |G j k|

/-- The consistency ratio |G(i,k)| / (|G(i,j)| · |G(j,k)|) for a given triple. -/
def consistencyRatio (G : α → α → ℝ) (i j k : α) : ℝ :=
  |G i k| / (|G i j| * |G j k|)

/-- Whether a kernel has at least one non-degenerate triple (positive denominator). -/
def HasNondegTriple (G : α → α → ℝ) : Prop :=
  ∃ i j k : α, |G i j| * |G j k| > 0

/-- The maximal consistency parameter μ(G), defined as the supremum of all
    nonneg μ for which ApproxSubmult μ G holds. -/
def muParam (G : α → α → ℝ) : ℝ :=
  sSup {μ : ℝ | 0 ≤ μ ∧ ApproxSubmult μ G}

/-- Additive triangle inequality with slack δ for an effective distance D. -/
def TriangleSlack (δ : ℝ) (D : α → α → ℝ) : Prop :=
  ∀ i j k, D i k ≤ D i j + D j k + δ

/-- The CHSH functional for a 2×2 kernel (specialized to 4 indices). -/
def CHSHValue (G : Fin 4 → Fin 4 → ℝ) : ℝ :=
  G 0 2 + G 0 3 + G 1 2 - G 1 3

end
