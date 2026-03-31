/-
# Wave-First Quantum Theory: Holography Bridge Theorems

## Theorem 17: Finite entropy implies finite effective state count
## Theorem 18: Entropy-bounded sector + bounded observer content ⟹ finite observer measure
-/
import Mathlib

/-! ## Theorem 17: Finite entropy sector implies finite effective state count

If a physical sector satisfies an entropy bound S_max < ∞, then the number
of distinguishable states is bounded by N ≤ exp(S_max). -/

theorem finite_entropy_bounds_states (S_max : ℝ) (hS : 0 ≤ S_max)
    (N : ℕ) (hN : (N : ℝ) > Real.exp S_max) :
    ¬ (Real.log N ≤ S_max) := by
  exact not_le_of_gt ( Real.log_exp S_max ▸ Real.log_lt_log ( by positivity ) hN )

/-- Equivalent formulation: if log N ≤ S_max then N ≤ exp(S_max). -/
theorem state_count_bound (S_max : ℝ) (N : ℕ) (hN : 0 < N)
    (h : Real.log N ≤ S_max) :
    (N : ℝ) ≤ Real.exp S_max := by
  rwa [ Real.log_le_iff_le_exp ( by positivity ) ] at h

/-! ## Theorem 18: Entropy-bounded sector + bounded observer content ⟹ finite observer measure

If:
- the physical sector has at most N distinguishable states (N finite),
- each state has observer-content bounded by C,
- each state has measure μ(i),

then the total observer-measure is bounded by C · ∑ μ(i), which is finite
when the base measure is finite. -/

theorem entropy_bounded_finite_observer_measure
    (N : ℕ) (μ : Fin N → ℝ) (w : Fin N → ℝ) (C : ℝ)
    (hμ_nn : ∀ i, 0 ≤ μ i) (_hw_nn : ∀ i, 0 ≤ w i)
    (hw_bdd : ∀ i, w i ≤ C) (_hC : 0 ≤ C) :
    ∑ i, μ i * w i ≤ C * ∑ i, μ i := by
  simpa only [ mul_comm, Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ( hw_bdd i ) ( hμ_nn i )

/-- Combined holography + observer measure theorem:
    If S_max bounds entropy and C bounds observer content,
    then total observer measure ≤ C · ∑ μ(i). -/
theorem holography_observer_bridge
    (N : ℕ) (μ w : Fin N → ℝ)
    (hμ_nn : ∀ i, 0 ≤ μ i) (_hw_nn : ∀ i, 0 ≤ w i)
    (C : ℝ) (_hC : 0 ≤ C) (hw_bdd : ∀ i, w i ≤ C) :
    ∑ i, μ i * w i ≤ C * ∑ i, μ i := by
  simpa only [ mul_comm, Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ( hw_bdd i ) ( hμ_nn i )
