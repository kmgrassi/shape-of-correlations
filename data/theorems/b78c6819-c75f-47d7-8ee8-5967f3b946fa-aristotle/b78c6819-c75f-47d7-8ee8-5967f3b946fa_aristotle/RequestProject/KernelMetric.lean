/-
# Correlation Kernel → Pseudometric / Metric

Given a "correlation kernel" I : V → V → ℝ satisfying:
  • 0 < I(i,j) ≤ 1
  • I(i,i) = 1
  • I(i,j) = I(j,i)               (symmetry)
  • I(i,j) ≥ I(i,k) · I(k,j)     (supermultiplicativity)

We prove that d(i,j) = −log I(i,j) is a pseudometric.
If additionally I(i,j) < 1 for i ≠ j, then d is a metric.

This is the core "metric emergence" result:
geometry arises from any supermultiplicative symmetric kernel.

Counterexample: an arbitrary symmetric positive kernel (without supermultiplicativity)
need NOT yield a pseudometric.
-/
import Mathlib

open Real

noncomputable section

/-! ## Correlation Kernel -/

/-- A correlation kernel on a type `V`: a symmetric, supermultiplicative function
    with values in (0,1] and I(i,i) = 1. -/
structure CorrKernel (V : Type*) where
  I : V → V → ℝ
  I_pos : ∀ i j, 0 < I i j
  I_le_one : ∀ i j, I i j ≤ 1
  I_self : ∀ i, I i i = 1
  I_symm : ∀ i j, I i j = I j i
  I_supermult : ∀ i j k, I i k * I k j ≤ I i j

namespace CorrKernel

variable {V : Type*} (K : CorrKernel V)

/-- The distance function derived from the kernel: d(i,j) = -log I(i,j). -/
def dist (i j : V) : ℝ := -Real.log (K.I i j)

/-! ### Pseudometric properties -/

/-
PROVIDED SOLUTION
d(i,i) = -log(I(i,i)) = -log(1) = 0. Unfold dist, rewrite K.I_self, use Real.log_one.
-/
theorem dist_self (i : V) : K.dist i i = 0 := by
  -- By definition of $K.dist$, we have $K.dist i i = -Real.log (K.I i i)$.
  simp [CorrKernel.dist, K.I_self]

/-
PROVIDED SOLUTION
Unfold dist, rewrite K.I_symm.
-/
theorem dist_symm (i j : V) : K.dist i j = K.dist j i := by
  exact congr_arg Neg.neg ( congr_arg Real.log ( K.I_symm i j ) )

/-
PROVIDED SOLUTION
Since 0 < I(i,j) ≤ 1, log I(i,j) ≤ 0, so -log I(i,j) ≥ 0. Use Real.log_nonpos (le_of_lt (K.I_pos i j)) (K.I_le_one i j) and negate.
-/
theorem dist_nonneg (i j : V) : 0 ≤ K.dist i j := by
  exact neg_nonneg_of_nonpos ( Real.log_nonpos ( le_of_lt ( K.I_pos i j ) ) ( K.I_le_one i j ) )

/-
PROVIDED SOLUTION
By K.I_supermult: I(i,k)·I(k,j) ≤ I(i,j). Since all values positive, take log (monotone): log(I(i,k)·I(k,j)) ≤ log(I(i,j)). Use Real.log_mul (ne_of_gt (K.I_pos i k)) (ne_of_gt (K.I_pos k j)) to split the LHS. Negate both sides to get the triangle inequality for dist = -log I.
-/
theorem dist_triangle (i j k : V) : K.dist i j ≤ K.dist i k + K.dist k j := by
  -- By the supermultiplicative property of $K$, we have $K.I i k * K.I k j \leq K.I i j$.
  have h_supermult : K.I i k * K.I k j ≤ K.I i j := by
    grind +suggestions
  -- Taking logarithms of both sides preserves the inequality because logarithm is a monotonically increasing function.
  have h_log_supermult : Real.log (K.I i k) + Real.log (K.I k j) ≤ Real.log (K.I i j) := by
    rw [ ← Real.log_mul ( ne_of_gt ( K.I_pos _ _ ) ) ( ne_of_gt ( K.I_pos _ _ ) ) ] ; exact Real.log_le_log ( mul_pos ( K.I_pos _ _ ) ( K.I_pos _ _ ) ) h_supermult;
  -- Since $K.I i k$ and $K.I k j$ are positive, their logarithms are real numbers.
  have h_log_real : Real.log (K.I i k) + Real.log (K.I k j) ≤ Real.log (K.I i j) := by
    exact h_log_supermult
  -- Using the definition of distance, we get the desired inequality.
  simp [dist, h_log_real] at *;
  exact (by
  rw [ ← Real.log_mul ( ne_of_gt ( K.I_pos _ _ ) ) ( ne_of_gt ( K.I_pos _ _ ) ) ] ; exact Real.log_le_log ( mul_pos ( K.I_pos _ _ ) ( K.I_pos _ _ ) ) ( by linarith ) ;); -- This contradicts our assumption that $K.I i k * K.I k j > K.I i j$.
  -- Therefore, the assumption must be false, and we have $K.I i k * K.I k j \leq K.I i j$.
  -- This completes the proof of the triangle inequality for the distance function.
  -- Therefore, the distance function is a pseudometric.
  -- This completes the proof. QED.

/-! ### Metric property (separation) -/

/-- A correlation kernel is *separating* if I(i,j) < 1 for distinct i, j. -/
def Separating : Prop := ∀ i j, i ≠ j → K.I i j < 1

/-
PROVIDED SOLUTION
Since K is Separating, I(i,j) < 1 for i ≠ j. Also I(i,j) > 0. So log I(i,j) < 0, hence -log I(i,j) > 0. Use Real.log_neg (K.I_pos i j) (hK hij).
-/
theorem dist_pos_of_ne (hK : K.Separating) {i j : V} (hij : i ≠ j) :
    0 < K.dist i j := by
      exact neg_pos_of_neg ( Real.log_neg ( K.I_pos i j ) ( hK i j hij ) )

/-! ### Bundle as Mathlib PseudoMetricSpace -/

/-
PROBLEM
The pseudometric space structure induced by a correlation kernel.

PROVIDED SOLUTION
The edist_dist field should follow from the default PseudoMetricSpace construction. The extended distance is defined as ENNReal.ofReal (dist x y). We need to show this equals the edist. Since we're constructing the PseudoMetricSpace, the edist is defined from dist, so this should be definitional or follow from rfl-like reasoning.
-/
def toPseudoMetricSpace : PseudoMetricSpace V where
  dist := K.dist
  dist_self := K.dist_self
  dist_comm := K.dist_symm
  dist_triangle := fun x y z => K.dist_triangle x z y
  edist_dist := fun x y => by
    exact ENNReal.coe_nnreal_eq _

/-! ## Counterexample: arbitrary symmetric kernel need not give a pseudometric -/

/-
PROBLEM
A non-supermultiplicative symmetric kernel whose -log does NOT satisfy
    the triangle inequality. This shows supermultiplicativity is essential.

PROVIDED SOLUTION
Use I(i,j) on Fin 3 defined as: I(i,i) = 1, I(0,1) = I(1,0) = 0.9, I(1,2) = I(2,1) = 0.9, I(0,2) = I(2,0) = 0.01. This satisfies positivity, ≤1, self=1, symmetry. For the triangle violation: take i=0, j=2, k=1. Then -log(0.9) + -log(0.9) = 2·(-log 0.9) ≈ 0.21 but -log(0.01) ≈ 4.6, so d(0,1)+d(1,2) < d(0,2). More precisely, -log(0.9) + -log(0.9) = -log(0.81) and -log(0.01) > -log(0.81) since 0.01 < 0.81. Use native_decide or norm_num for the numerical comparison after choosing concrete rational approximations like 9/10 and 1/100.
-/
theorem counterexample_no_triangle :
    ∃ (I : Fin 3 → Fin 3 → ℝ),
      (∀ i j, 0 < I i j) ∧
      (∀ i j, I i j ≤ 1) ∧
      (∀ i, I i i = 1) ∧
      (∀ i j, I i j = I j i) ∧
      ∃ i j k, -Real.log (I i k) + -Real.log (I k j) < -Real.log (I i j) := by
        -- Define the kernel $I$ as follows:
        refine' ⟨fun i j => if i = j then 1 else if i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 then 0.9 else if i = 1 ∧ j = 2 ∨ i = 2 ∧ j = 1 then 0.9 else if i = 0 ∧ j = 2 ∨ i = 2 ∧ j = 0 then 0.01 else 1, _, _, _, _, 0, 2, 1, _⟩ <;> norm_num [ Fin.forall_fin_succ, Fin.exists_fin_succ ] at *; (
        norm_num [ Fin.ext_iff ] at * <;> first | linarith | aesop | assumption;);
        · norm_num [ Fin.ext_iff ] at * <;> first | linarith | aesop | assumption;
        · lia;
        · norm_num [ Fin.ext_iff, ← Real.log_mul, Real.log_lt_log ] at * <;> first | linarith | aesop | assumption;

end CorrKernel

end