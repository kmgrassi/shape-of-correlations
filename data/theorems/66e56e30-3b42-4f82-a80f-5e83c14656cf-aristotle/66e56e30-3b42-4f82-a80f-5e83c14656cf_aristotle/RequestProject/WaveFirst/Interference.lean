/-
# Wave-First Quantum Theory: Interference Recovery Theorems

## Theorem 1: Two-slit interference cross term
## Theorem 2: Which-path decoherence removes cross term
## Theorem 3: Linear propagation preserves superposition
-/
import Mathlib

open Complex ComplexConjugate

/-! ## Section I: Core Definitions -/

/-- Intensity of a complex-valued wave at a point. -/
noncomputable def intensity (ψ : α → ℂ) (x : α) : ℝ := ‖ψ x‖ ^ 2

/-! ## Theorem 1: Two-slit interference cross term

If ψ = ψ₁ + ψ₂, then |ψ|² = |ψ₁|² + |ψ₂|² + 2 Re(ψ₁ * conj ψ₂). -/

theorem interference_cross_term (ψ₁ ψ₂ : α → ℂ) (x : α) :
    intensity (ψ₁ + ψ₂) x =
      intensity ψ₁ x + intensity ψ₂ x + 2 * (ψ₁ x * conj (ψ₂ x)).re := by
  unfold intensity; simp +decide [Complex.normSq, Complex.sq_norm]; ring

/-! ## Theorem 2: Which-path decoherence removes cross term

When the slit alternatives are tagged with orthogonal environment states,
the reduced screen intensity loses the interference (cross) term.

We model this in a tensor-product Hilbert space. The total state is
  Ψ = ψ₁ ⊗ e₁ + ψ₂ ⊗ e₂
with ⟨e₁, e₂⟩ = 0. The reduced intensity at screen point x is
  I(x) = |ψ₁(x)|² ‖e₁‖² + |ψ₂(x)|² ‖e₂‖² + 2 Re(ψ₁(x) * conj(ψ₂(x)) * ⟨e₁, e₂⟩)
When ⟨e₁, e₂⟩ = 0 and ‖e₁‖ = ‖e₂‖ = 1, this reduces to |ψ₁(x)|² + |ψ₂(x)|². -/

/-- Reduced intensity in a tensor-product state Ψ = ψ₁ ⊗ e₁ + ψ₂ ⊗ e₂.
    The inner product of the environment states appears as a parameter. -/
noncomputable def reducedIntensity (ψ₁ ψ₂ : α → ℂ) (ne₁ ne₂ : ℝ) (ip : ℂ) (x : α) : ℝ :=
  ‖ψ₁ x‖ ^ 2 * ne₁ ^ 2 + ‖ψ₂ x‖ ^ 2 * ne₂ ^ 2 +
    2 * (ψ₁ x * conj (ψ₂ x) * ip).re

theorem decoherence_removes_cross_term (ψ₁ ψ₂ : α → ℂ) (x : α) :
    reducedIntensity ψ₁ ψ₂ 1 1 0 x = ‖ψ₁ x‖ ^ 2 + ‖ψ₂ x‖ ^ 2 := by
  simp [reducedIntensity]

/-! ## Theorem 3: Linear propagation preserves superposition

If evolve is linear, then evolving a superposition equals the
superposition of evolved states. -/

theorem linear_propagation_preserves_superposition
    {S : Type*} [AddCommMonoid S] [Module ℂ S]
    (U : S →ₗ[ℂ] S) (a b : ℂ) (ψ φ : S) :
    U (a • ψ + b • φ) = a • U ψ + b • U φ := by
  rw [map_add, map_smul, map_smul]
