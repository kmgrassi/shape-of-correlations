/-
# Metric Emergence Theorems

Theorems A1-A3: Proving that the emergent distance d(i,j) = -log(I(i,j))
satisfies pseudometric and metric axioms under appropriate assumptions.
-/
import RequestProject.CorrGeom.Defs

noncomputable section

open Real

variable {S : Type*}

/-! ## Theorem A1: Basic pseudometric axioms -/

/-- The emergent distance is nonneg: d(i,j) ≥ 0. -/
theorem emergentDist_nonneg (K : CorrKernel S) (i j : S) :
    0 ≤ emergentDist K i j :=
  neg_nonneg_of_nonpos (Real.log_nonpos (le_of_lt (K.pos i j)) (K.bound i j))

/-- The emergent distance is zero on diagonal: d(i,i) = 0. -/
theorem emergentDist_self (K : CorrKernel S) (i : S) :
    emergentDist K i i = 0 := by
  rw [emergentDist, K.norm]; norm_num

/-- The emergent distance is symmetric: d(i,j) = d(j,i). -/
theorem emergentDist_symm (K : CorrKernel S) (i j : S) :
    emergentDist K i j = emergentDist K j i := by
  simp [emergentDist, K.symm]

/-! ## Theorem A2: Triangle inequality from multiplicative correlation inequality -/

/-- If I(i,k) ≥ I(i,j) * I(j,k) for all i,j,k, then d satisfies the triangle inequality. -/
theorem emergentDist_triangle (K : CorrKernelTriangle S) (i j k : S) :
    emergentDist K.toCorrKernel i k ≤
      emergentDist K.toCorrKernel i j + emergentDist K.toCorrKernel j k := by
  unfold emergentDist
  rw [← neg_add, ← Real.log_mul (ne_of_gt (K.pos _ _)) (ne_of_gt (K.pos _ _))]
  exact neg_le_neg (Real.log_le_log (mul_pos (K.pos _ _) (K.pos _ _)) (K.mult_triangle _ _ _))

/-! ## Theorem A3: Metric criterion -/

/-- If I(i,j) = 1 ↔ i = j, then d(i,j) = 0 ↔ i = j. -/
theorem emergentDist_eq_zero_iff (K : CorrKernelSep S) (i j : S) :
    emergentDist K.toCorrKernel i j = 0 ↔ i = j := by
  rw [emergentDist]
  norm_num +zetaDelta at *
  have h_pos : 0 < K.I i j := K.pos i j
  have := K.sep i j
  grind +ring

/-! ## Theorem D1: Exponential coupling recovers original kernel -/

/-- H(i,j) = exp(-d(i,j)) = I(i,j). -/
theorem expCoupling_eq_kernel (K : CorrKernel S) (i j : S) :
    expCoupling K i j = K.I i j := by
  unfold expCoupling emergentDist
  rw [neg_neg, Real.exp_log (K.pos i j)]

/-- If d(i,j₁) < d(i,j₂), then H(i,j₁) > H(i,j₂) (monotone coupling). -/
theorem expCoupling_monotone (K : CorrKernel S) (i j₁ j₂ : S)
    (h : emergentDist K i j₁ < emergentDist K i j₂) :
    expCoupling K i j₂ < expCoupling K i j₁ :=
  Real.exp_lt_exp.2 (neg_lt_neg h)

end
