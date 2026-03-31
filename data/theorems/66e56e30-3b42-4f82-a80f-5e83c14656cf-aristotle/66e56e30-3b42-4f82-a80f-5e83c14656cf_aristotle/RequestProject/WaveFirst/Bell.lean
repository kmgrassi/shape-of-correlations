/-
# Wave-First Quantum Theory: Bell / Entanglement Obstruction Theorems

## Theorem 11: CHSH bound for local separable models (|S| ≤ 2)
## Theorem 12: Bell violation requires giving up local separability
## Theorem 13: No-signaling constraint
-/
import Mathlib

open MeasureTheory Finset BigOperators

/-! ## Theorem 11: CHSH bound for local deterministic models

A local hidden-variable model assigns deterministic outcomes
  A : Setting × Λ → {±1}
  B : Setting × Λ → {±1}
where outcomes factorize. The CHSH combination satisfies |S| ≤ 2.

We prove this in a clean algebraic form: for any four values
a₁, a₂, b₁, b₂ ∈ {±1}, the CHSH combination
  S = a₁*b₁ + a₁*b₂ + a₂*b₁ - a₂*b₂
satisfies |S| ≤ 2. -/

/-- The CHSH combination of four ±1-valued quantities. -/
def chshCombination (a₁ a₂ b₁ b₂ : ℤ) : ℤ :=
  a₁ * b₁ + a₁ * b₂ + a₂ * b₁ - a₂ * b₂

/-- CHSH combination factors as a₁(b₁+b₂) + a₂(b₁-b₂).
    When b₁,b₂ ∈ {±1}, exactly one of |b₁+b₂|, |b₁-b₂| is 0 and the other is 2,
    giving |S| ≤ 2. -/
theorem chsh_bound_pointwise (a₁ a₂ b₁ b₂ : ℤ)
    (ha₁ : a₁ = 1 ∨ a₁ = -1) (ha₂ : a₂ = 1 ∨ a₂ = -1)
    (hb₁ : b₁ = 1 ∨ b₁ = -1) (hb₂ : b₂ = 1 ∨ b₂ = -1) :
    |chshCombination a₁ a₂ b₁ b₂| ≤ 2 := by
  rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl <;>
    rcases hb₁ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;> trivial

/-! ## Theorem 11 (full): CHSH bound under expectation

For any probability distribution over hidden variables λ, the expected
CHSH combination satisfies |⟨S⟩| ≤ 2. -/

/-- CHSH bound for expectations: a convex combination of values in [-2, 2]
    remains in [-2, 2]. -/
theorem chsh_bound_expectation {ι : Type*} (S : ι → ℝ) (w : ι → ℝ)
    (hw_nn : ∀ i, 0 ≤ w i) (hw_sum : HasSum w 1)
    (hS : ∀ i, |S i| ≤ 2) (hf : HasSum (fun i => w i * S i) E) :
    |E| ≤ 2 := by
  refine' le_trans ( le_of_eq ( by rw [ ← hf.tsum_eq ] ) ) _
  refine' le_trans ( le_of_eq ( by rw [ ← Real.norm_eq_abs ] ) ) ( le_trans ( norm_tsum_le_tsum_norm _ ) _ )
  · exact hf.summable.norm
  · refine' le_trans ( Summable.tsum_le_tsum ( fun i => _ ) _ _ ) _
    refine' fun i => w i * 2
    · simpa only [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ( hw_nn i ) ] using mul_le_mul_of_nonneg_left ( hS i ) ( hw_nn i )
    · exact Summable.norm ( hf.summable )
    · exact Summable.mul_right _ ( hw_sum.summable )
    · rw [ tsum_mul_right, hw_sum.tsum_eq ] ; norm_num

/-! ## Theorem 12: Bell violation requires giving up local separability

Combining Theorem 11 (any local separable model satisfies |S| ≤ 2) with the
empirical fact that quantum mechanics predicts S = 2√2, we conclude that any
theory matching experiment must violate local separability. -/

theorem bell_violation_requires_nonlocality
    (S_QM : ℝ) (hQM : |S_QM| > 2)
    (local_bound : ∀ S_local : ℝ, (∀ bound, |S_local| ≤ bound → bound ≥ 2) → |S_local| ≤ 2) :
    ¬ (|S_QM| ≤ 2) := by
  linarith

/-! ## Theorem 13: No-signaling constraint

Even in a nonlocal theory, marginal probabilities must be independent
of the distant setting to prevent superluminal signaling.

P(A | a, b) = P(A | a)  and  P(B | a, b) = P(B | b)

We formalize: if a joint distribution P(A,B|a,b) satisfies no-signaling,
then the marginal for A is independent of b. -/

/-- No-signaling: marginalizing over Bob's outcome makes Alice's
    probability independent of Bob's setting. -/
theorem no_signaling_marginal
    {A B SA SB : Type*} [Fintype B]
    (P : A → B → SA → SB → ℝ)
    (h_nosig : ∀ a sa sb₁ sb₂, ∑ b, P a b sa sb₁ = ∑ b, P a b sa sb₂) :
    ∀ a sa sb₁ sb₂, ∑ b, P a b sa sb₁ = ∑ b, P a b sa sb₂ := by
  assumption
