/-
  Causal Order as Extra Relational Data on Emergent Metric Geometry
  Part I (continued): Emergent Metric Properties

  Proves that `emergentDist` from a SymmetricKernel is a pseudometric.
-/
import Mathlib
import RequestProject.Defs

noncomputable section

open Real

variable {S : Type*} (K : SymmetricKernel S)

/-
PROBLEM
The emergent distance is nonneg since I(i,j) ≤ 1.

PROVIDED SOLUTION
emergentDist K i j = -log(I i j). Since I i j ≤ 1 and I i j > 0, log(I i j) ≤ 0, so -log(I i j) ≥ 0. Use Real.log_nonpos and K.le_one, K.pos.
-/
theorem emergentDist_nonneg (i j : S) : 0 ≤ emergentDist K i j := by
  exact neg_nonneg_of_nonpos ( Real.log_nonpos ( le_of_lt ( K.pos i j ) ) ( K.le_one i j ) )

/-
PROBLEM
d(i,i) = 0 since I(i,i) = 1.

PROVIDED SOLUTION
emergentDist K i i = -log(I i i) = -log 1 = 0. Use K.refl and Real.log_one.
-/
theorem emergentDist_self (i : S) : emergentDist K i i = 0 := by
  unfold emergentDist; norm_num [ Real.log_one, K.refl ] ;

/-
PROBLEM
d(i,j) = d(j,i) since I is symmetric.

PROVIDED SOLUTION
emergentDist K i j = -log(I i j) = -log(I j i) = emergentDist K j i. Use K.symm.
-/
theorem emergentDist_symm (i j : S) : emergentDist K i j = emergentDist K j i := by
  exact congr_arg Neg.neg ( congr_arg Real.log ( K.symm i j ) )

/-
PROBLEM
Triangle inequality from supermultiplicativity.

PROVIDED SOLUTION
We need -log I(i,k) ≤ -log I(i,j) + (-log I(j,k)) = -log(I(i,j) * I(j,k)). By supermultiplicativity I(i,k) ≥ I(i,j) * I(j,k). Since log is monotone and all values are positive, log I(i,k) ≥ log(I(i,j) * I(j,k)), so -log I(i,k) ≤ -log(I(i,j) * I(j,k)) = -log I(i,j) - log I(j,k). Use Real.log_mul_le (or Real.log_le_log) and the positivity of the kernel values. Key lemma: Real.log_mul, then neg_add, and Real.log_le_log_of_le with supermul.
-/
theorem emergentDist_triangle (i j k : S) :
    emergentDist K i k ≤ emergentDist K i j + emergentDist K j k := by
      -- By the properties of logarithms, we can simplify the inequality to log(I(i,k)) ≥ log(I(i,j) * I(j,k)).
      have h_log : Real.log (K.I i k) ≥ Real.log (K.I i j * K.I j k) := by
        exact Real.log_le_log ( mul_pos ( K.pos _ _ ) ( K.pos _ _ ) ) ( K.supermul _ _ _ );
      unfold emergentDist; rw [ Real.log_mul ( ne_of_gt ( K.pos i j ) ) ( ne_of_gt ( K.pos j k ) ) ] at h_log; linarith;

/-- The emergent distance forms a `CausalMetric` (with an empty causal relation). -/
def emergentCausalMetric (K : SymmetricKernel S) (C : CausalRelation S) :
    CausalMetric S where
  d := emergentDist K
  d_nonneg := emergentDist_nonneg K
  d_self := emergentDist_self K
  d_symm := emergentDist_symm K
  d_triangle := emergentDist_triangle K
  causal := C

end