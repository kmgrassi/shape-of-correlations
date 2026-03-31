/-
# Entropy-Bound Compatibility and Observer-Measure Finiteness

## Main results:

1. **Basic bound**: If the number of distinguishable states N ≤ e^{S_max}
   and each state has observer-content ≤ c_max, then the total
   observer-measure M = Σ c(s) ≤ e^{S_max} · c_max.

2. **Area-law bound**: In a tensor network with bond dimension D,
   the number of distinguishable boundary configurations across a cut
   of size A is ≤ D^A. Combined with bounded observer content,
   this gives observer-measure ≤ D^A · c_max.

3. **Holographic regularization**: Entropy bounds of the form
   S ≤ Area / (4 G_N) in Planck units bound the state count and
   hence the observer-measure.

These results formalize:
"Holographic-style entropy bounds regularize observer counting."
-/
import Mathlib

open Finset BigOperators Real

noncomputable section

/-! ## 1. Basic entropy-bound → finite observer-measure -/

/-
PROBLEM
Given a finite set of states with bounded observer-content,
    the total observer-measure is bounded.

PROVIDED SOLUTION
∑ c(s) ≤ ∑ c_max = |S| · c_max. Use Finset.sum_le_sum to bound each term, then Finset.sum_const to simplify.
-/
theorem observer_measure_bounded
    {S : Type*} [Fintype S]
    (c : S → ℝ)                    -- observer content per state
    (c_nonneg : ∀ s, 0 ≤ c s)     -- content is nonneg
    (c_max : ℝ)                    -- uniform upper bound
    (hc : ∀ s, c s ≤ c_max)       -- each content ≤ c_max
    : ∑ s : S, c s ≤ Fintype.card S * c_max := by
      simpa using Finset.sum_le_sum fun s _ => hc s

/-
PROBLEM
If the state count is bounded by e^{S_max}, observer-measure
    is bounded by e^{S_max} · c_max.

PROVIDED SOLUTION
By observer_measure_bounded, ∑ c(s) ≤ |S| · c_max. Since |S| ≤ e^{S_max} and c_max ≥ 0, we get |S| · c_max ≤ e^{S_max} · c_max by mul_le_mul_of_nonneg_right.
-/
theorem observer_measure_entropy_bound
    {S : Type*} [Fintype S]
    (c : S → ℝ)
    (c_nonneg : ∀ s, 0 ≤ c s)
    (c_max S_max : ℝ)
    (hc : ∀ s, c s ≤ c_max)
(hcmax : 0 ≤ c_max)
    (hN : (Fintype.card S : ℝ) ≤ Real.exp S_max) :
    ∑ s : S, c s ≤ Real.exp S_max * c_max := by
      exact le_trans ( Finset.sum_le_sum fun _ _ => hc _ ) ( by simpa [ mul_comm ] using mul_le_mul_of_nonneg_right hN hcmax )

/-! ## 2. Area-law bound from tensor networks -/

/-
PROBLEM
In a tensor network, a cut of size A with bond dimension D
    allows at most D^A distinguishable boundary states.
    This is the fundamental area-law bound.

PROVIDED SOLUTION
∑ c(s) ≤ ∑ c_max = N · c_max ≤ D^A · c_max. Use Finset.sum_le_sum for the first step, Finset.sum_const and Finset.card_fin for simplification, then Nat.cast_le.mpr hN and mul_le_mul_of_nonneg_right.
-/
theorem area_law_state_count
    (D : ℕ) (A : ℕ) (hD : 0 < D)
    (N : ℕ)                        -- number of distinguishable states
    (hN : N ≤ D ^ A)              -- area-law bound
    (c_max : ℝ) (hcmax : 0 ≤ c_max)
    (c : Fin N → ℝ)
    (hc_nonneg : ∀ s, 0 ≤ c s)
    (hc_bound : ∀ s, c s ≤ c_max) :
    ∑ s : Fin N, c s ≤ ↑(D ^ A) * c_max := by
      exact le_trans ( Finset.sum_le_sum fun _ _ => hc_bound _ ) ( by simpa using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hN ) hcmax )

/-
PROBLEM
The area-law entropy is S_max = A · log D.

PROVIDED SOLUTION
exp(A · log D) = D^A. Use Real.exp_natMul or Real.rpow_natCast combined with Real.exp_log. Since D > 1, D > 0 as a real, so log D is well-defined. exp(A · log D) = exp(log D)^A = D^A. Use Real.exp_mul_log or rpow.
-/
theorem area_law_entropy (D : ℕ) (A : ℕ) (hD : 1 < D) :
    Real.exp (A * Real.log D) = (D : ℝ) ^ A := by
      rw [ mul_comm, Real.exp_mul, Real.exp_log ] <;> norm_cast ; linarith

/-! ## 3. Holographic regularization -/

/-
PROBLEM
Holographic principle: entropy is bounded by area in Planck units.
    S ≤ Area / (4 · G_N), so distinguishable states ≤ e^{Area/(4·G_N)}.
    With bounded observer content, the observer-measure is finite.

    This is a direct corollary of observer_measure_entropy_bound.

PROVIDED SOLUTION
This is a direct application of observer_measure_entropy_bound with S_max = Area/(4·G_N). Apply observer_measure_entropy_bound with the given hypotheses.
-/
theorem holographic_observer_bound
    (Area G_N c_max : ℝ)
    (hG : 0 < G_N)
    (hcmax : 0 ≤ c_max)
    {S : Type*} [Fintype S]
    (c : S → ℝ)
    (hc_nonneg : ∀ s, 0 ≤ c s)
    (hc : ∀ s, c s ≤ c_max)
    (hN : (Fintype.card S : ℝ) ≤ Real.exp (Area / (4 * G_N))) :
    ∑ s : S, c s ≤ Real.exp (Area / (4 * G_N)) * c_max := by
      exact le_trans ( Finset.sum_le_sum fun _ _ => hc _ ) ( by simpa [ mul_comm ] using mul_le_mul_of_nonneg_right hN hcmax )

/-! ## 4. Counterexample: without entropy bounds, observer-measure
       can be unbounded -/

/-
PROBLEM
Without an entropy bound (i.e., no bound on state count),
    the observer-measure can be arbitrarily large even with
    bounded per-state content.

PROVIDED SOLUTION
Given M, choose N = ⌈M⌉₊ + 1 (or just ⌈M⌉ + 1). Then for any c_max ≥ 1, N · c_max ≥ N · 1 ≥ M. Use Nat.ceil or just take N large enough.
-/
theorem unbounded_without_entropy_bound :
    ∀ M : ℝ, ∃ (N : ℕ), ∀ (c_max : ℝ), 1 ≤ c_max →
      M ≤ N * c_max := by
        intro M; use ⌈M⌉₊ + 1; intro c hc; push_cast; nlinarith [ Nat.le_ceil M ] ;

end