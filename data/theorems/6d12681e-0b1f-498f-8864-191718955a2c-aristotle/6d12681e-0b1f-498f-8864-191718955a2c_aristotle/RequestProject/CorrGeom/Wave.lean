/-
# Wave-on-Relations Theorems

Theorems F1-F3: Interference is purely relational and does not require space.
-/
import RequestProject.CorrGeom.Defs

noncomputable section

open Complex

variable {S : Type*}

/-! ## Theorem F1: Interference is relational

For any ψ₁, ψ₂ : S → ℂ and ψ = ψ₁ + ψ₂, we have
|ψ(i)|² = |ψ₁(i)|² + |ψ₂(i)|² + 2 Re(ψ₁(i) * conj(ψ₂(i)))
for every i, with NO geometric assumptions. -/

/-- The interference identity: |ψ₁(i) + ψ₂(i)|² = |ψ₁(i)|² + |ψ₂(i)|² + 2 Re(ψ₁(i) * conj(ψ₂(i))).
    This is a purely algebraic identity that holds on any type S, proving that
    interference does not require background space. -/
theorem interference_relational (ψ₁ ψ₂ : S → ℂ) (i : S) :
    Complex.normSq (ψ₁ i + ψ₂ i) =
      Complex.normSq (ψ₁ i) + Complex.normSq (ψ₂ i) +
        2 * (ψ₁ i * starRingEnd ℂ (ψ₂ i)).re := by
  norm_num [Complex.normSq, Complex.ext_iff]; ring

/-! ## Assumption 4 test: "Interference requires background space" is FALSE

The theorem above proves this false: the interference identity holds for
any function on any type S, with no geometric or spatial structure required. -/

/-! ## Theorem F3: Two-path relational toy model

We model: source → (path A or path B) → detector
using S = Fin 4: source = 0, pathA = 1, pathB = 2, detector = 3.

With both paths open, the amplitude at detector has a cross term.
With one path blocked, there is no cross term. -/

/-- Amplitude through path A only: ψ_A at detector. -/
def pathA_amplitude (a : ℂ) : Fin 4 → ℂ :=
  fun i => if i = (3 : Fin 4) then a else 0

/-- Amplitude through path B only: ψ_B at detector. -/
def pathB_amplitude (b : ℂ) : Fin 4 → ℂ :=
  fun i => if i = (3 : Fin 4) then b else 0

/-- With both paths open, intensity at detector has a cross term.
    This is the hallmark of interference. -/
theorem both_paths_cross_term (a b : ℂ) :
    Complex.normSq ((pathA_amplitude a + pathB_amplitude b) (3 : Fin 4)) =
      Complex.normSq a + Complex.normSq b +
        2 * (a * starRingEnd ℂ b).re := by
  unfold pathA_amplitude pathB_amplitude
  norm_num [Complex.normSq, Complex.ext_iff]; ring

/-- With only path A open, intensity at detector has no cross term. -/
theorem single_path_no_cross_term (a : ℂ) :
    Complex.normSq ((pathA_amplitude a) (3 : Fin 4)) = Complex.normSq a := rfl

end
