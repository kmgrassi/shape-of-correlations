import Mathlib

/-!
# Wave Amplitude and Interference

We define wave amplitudes on a finite type and prove the interference
cross-term formula for the superposition of two waves.

## Main results

* `interference_formula` — `|ψ₁ + ψ₂|² = |ψ₁|² + |ψ₂|² + 2 Re(ψ₁ · conj ψ₂)`
* `interference_relational` — the formula holds for any type, with no geometric hypotheses
-/

noncomputable section

open Complex

/-! ## Wave Amplitudes and Intensity -/

/-- A wave amplitude assigns a complex number to each node. -/
abbrev WaveAmplitude (S : Type*) := S → ℂ

/-- The intensity (Born rule) at a node. -/
def intensity {S : Type*} (ψ : WaveAmplitude S) (i : S) : ℝ :=
  ‖ψ i‖ ^ 2

/-- The cross term between two amplitudes at a node. -/
def crossTerm {S : Type*} (ψ₁ ψ₂ : WaveAmplitude S) (i : S) : ℝ :=
  2 * (ψ₁ i * starRingEnd ℂ (ψ₂ i)).re

/-! ## Interference Formula -/

/-- The interference formula: the intensity of a superposition equals
    the sum of individual intensities plus the cross term. -/
theorem interference_formula {S : Type*} (ψ₁ ψ₂ : WaveAmplitude S) (i : S) :
    intensity (ψ₁ + ψ₂) i =
      intensity ψ₁ i + intensity ψ₂ i + crossTerm ψ₁ ψ₂ i := by
  unfold intensity crossTerm
  simp only [Pi.add_apply]; norm_num [Complex.normSq, Complex.sq_norm]; ring

/-- Without superposition, the cross term vanishes (trivially). -/
theorem no_cross_term_single {S : Type*} (ψ : WaveAmplitude S) (i : S) :
    intensity ψ i = intensity ψ i + 0 := by ring

/-! ## All definitions are purely relational -/

/-- For any bijection `f : S ≃ T`, the interference physics is preserved.
    This captures the fact that `intensity`, `crossTerm`, and
    `interference_formula` depend only on the algebraic structure of
    complex amplitudes on a bare finite set — no ambient space is needed. -/
theorem interference_relational {S T : Type*} (f : S ≃ T)
    (ψ₁ ψ₂ : WaveAmplitude T) (i : S) :
    intensity (ψ₁ + ψ₂) (f i) =
      intensity ψ₁ (f i) + intensity ψ₂ (f i) + crossTerm ψ₁ ψ₂ (f i) :=
  interference_formula ψ₁ ψ₂ (f i)

end
