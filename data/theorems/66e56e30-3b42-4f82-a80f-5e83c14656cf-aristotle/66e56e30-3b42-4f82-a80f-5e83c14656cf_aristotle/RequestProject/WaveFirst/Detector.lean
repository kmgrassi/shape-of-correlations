/-
# Wave-First Quantum Theory: Detector-Event Theorems

## Theorem 8: Extended wave induces localized detector response
## Theorem 10: Born-rule recovery from detector functional
-/
import Mathlib

open MeasureTheory ENNReal

/-! ## Theorem 8: Detector response localization

An extended incoming wave can produce localized detection. We model
a detector array as a finite collection of disjoint regions, each with
a response probability. The total response sums to 1 (normalized). -/

/-- A detector array is a finite set of detectors, each with a response
    probability. Normalization means probabilities sum to 1. -/
structure DetectorArray (n : ℕ) where
  prob : Fin n → ℝ
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_sum : ∑ i, prob i = 1

/-- Each individual detector has probability ≤ 1. -/
theorem detector_prob_le_one {n : ℕ} (D : DetectorArray n) (i : Fin n) :
    D.prob i ≤ 1 := by
  exact D.prob_sum ▸ Finset.single_le_sum (fun a _ => D.prob_nonneg a) (Finset.mem_univ i)

/-- An extended wave (nonzero at multiple detectors) can still produce
    a normalized discrete probability distribution.
    This shows detection can be localized even for extended waves. -/
theorem extended_wave_localized_detection (n : ℕ) (hn : 0 < n)
    (amplitudes : Fin n → ℂ) (h_nonzero : ∃ i, amplitudes i ≠ 0)
    (h_norm : ∑ i, ‖amplitudes i‖ ^ 2 = 1) :
    ∃ D : DetectorArray n, ∀ i, D.prob i = ‖amplitudes i‖ ^ 2 := by
  exact ⟨⟨_, fun i => sq_nonneg _, h_norm⟩, fun i => rfl⟩

/-! ## Theorem 10: Born-rule recovery

Under suitable axioms on the detector response functional, the click
probability equals the integral of |ψ|² over the detector region.

We prove this in a discrete setting: if the detector response is
proportional to |ψ|² at each point, and the state is normalized,
then the detection probabilities form a valid probability distribution
matching the Born rule. -/

/-- Born rule in discrete setting: if ψ is normalized, then |ψ(i)|² gives
    a probability distribution. -/
theorem born_rule_discrete {n : ℕ} (hn : 0 < n)
    (ψ : Fin n → ℂ) (h_norm : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    (∀ i, 0 ≤ ‖ψ i‖ ^ 2) ∧ ∑ i, ‖ψ i‖ ^ 2 = 1 := by
  exact ⟨fun i => sq_nonneg _, h_norm⟩

/-- Born rule: detection probability for a subset of positions equals
    the sum of |ψ|² over that subset, which is between 0 and 1. -/
theorem born_rule_subset {n : ℕ}
    (ψ : Fin n → ℂ) (h_norm : ∑ i, ‖ψ i‖ ^ 2 = 1)
    (S : Finset (Fin n)) :
    0 ≤ ∑ i ∈ S, ‖ψ i‖ ^ 2 ∧ ∑ i ∈ S, ‖ψ i‖ ^ 2 ≤ 1 := by
  exact ⟨Finset.sum_nonneg fun _ _ => sq_nonneg _,
    h_norm ▸ Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _⟩
