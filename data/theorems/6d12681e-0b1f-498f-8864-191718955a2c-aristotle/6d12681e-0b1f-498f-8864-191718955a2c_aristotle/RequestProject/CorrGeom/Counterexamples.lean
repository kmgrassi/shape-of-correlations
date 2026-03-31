/-
# Counterexample Theorems (B1-B3)

Stress-tests showing that various assumptions are genuinely needed.
-/
import RequestProject.CorrGeom.Defs

noncomputable section

open Real

/-! ## Theorem B1: Symmetry + positivity alone do not imply triangle inequality

We construct a kernel on Fin 3 satisfying all basic axioms but where
d fails the triangle inequality.

Take S = {0, 1, 2} with:
  I(0,1) = I(1,0) = exp(-1)
  I(1,2) = I(2,1) = exp(-1)
  I(0,2) = I(2,0) = exp(-3)
  I(i,i) = 1

Then d(0,1) = 1, d(1,2) = 1, d(0,2) = 3.
Triangle inequality requires d(0,2) ≤ d(0,1) + d(1,2) = 2, but d(0,2) = 3. ✗

Note: This kernel does NOT satisfy the multiplicative triangle inequality:
I(0,2) = exp(-3) but I(0,1)*I(1,2) = exp(-2) > exp(-3). -/

/-- A correlation kernel on Fin 3 that satisfies all basic axioms. -/
def counterexKernel_B1 : CorrKernel (Fin 3) where
  I := fun i j =>
    if i = j then 1
    else if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then Real.exp (-1)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then Real.exp (-1)
    else Real.exp (-3)  -- i=0,j=2 or i=2,j=0
  symm := by simp +decide [Fin.forall_fin_succ]
  pos := fun i j => by split_ifs <;> positivity
  norm := by intro i; fin_cases i <;> simp
  bound := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp

/-- The triangle inequality fails for this kernel: d(0,2) > d(0,1) + d(1,2). -/
theorem triangle_not_automatic :
    emergentDist counterexKernel_B1 0 2 >
      emergentDist counterexKernel_B1 0 1 + emergentDist counterexKernel_B1 1 2 := by
  unfold emergentDist counterexKernel_B1; norm_num
  simp +decide [Real.log_exp]
  norm_num +zetaDelta at *

/-! ## Theorem B2: Multiplicative triangle is equivalent to metric triangle

One might expect the multiplicative triangle inequality to be merely sufficient
for the metric triangle inequality. In fact, they are equivalent!

If d(i,k) ≤ d(i,j) + d(j,k) for all i,j,k, then:
  -log(I(i,k)) ≤ -log(I(i,j)) + (-log(I(j,k))) = -log(I(i,j) * I(j,k))
  ⟹ log(I(i,k)) ≥ log(I(i,j) * I(j,k))
  ⟹ I(i,k) ≥ I(i,j) * I(j,k)

So the multiplicative triangle inequality is not just sufficient but *necessary*
for the triangle inequality of d. -/

/-- The multiplicative triangle inequality is actually equivalent to the triangle
    inequality for the emergent distance (not just sufficient). -/
theorem mult_triangle_iff_triangle (K : CorrKernel S) :
    (∀ i j k, K.I i k ≥ K.I i j * K.I j k) ↔
    (∀ i j k, emergentDist K i k ≤ emergentDist K i j + emergentDist K j k) := by
  constructor <;> intro h <;> intro i j k <;> have := h i j k <;>
    simp_all +decide [emergentDist]
  · rw [← Real.log_mul (ne_of_gt (K.pos _ _)) (ne_of_gt (K.pos _ _))]
    exact Real.log_le_log (mul_pos (K.pos _ _) (K.pos _ _)) (by linarith [h i j k])
  · rw [← Real.log_le_log_iff (mul_pos (K.pos i j) (K.pos j k)) (K.pos i k),
      Real.log_mul (ne_of_gt (K.pos i j)) (ne_of_gt (K.pos j k))]
    linarith [h i j k]

/-! ## Theorem B3: Degeneracy from non-separating kernels

Take the constant kernel I(i,j) = 1 for all i,j on Fin 2.
Then d(i,j) = 0 for all i,j, so d is a pseudometric but not a metric. -/

/-- The constant-1 kernel on Fin 2: all correlations are 1. -/
def constOneKernel : CorrKernel (Fin 2) where
  I := fun _ _ => 1
  symm := by intro i j; rfl
  pos := by intro i j; exact one_pos
  norm := by intro i; rfl
  bound := by intro i j; exact le_refl 1

/-- The emergent distance of the constant-1 kernel is identically zero. -/
theorem constOneKernel_dist_zero (i j : Fin 2) :
    emergentDist constOneKernel i j = 0 :=
  neg_eq_zero.mpr (by exact Real.log_one ▸ by fin_cases i <;> fin_cases j <;> rfl)

/-- The constant-1 kernel gives a pseudometric that is not a metric:
    there exist distinct points with distance zero. -/
theorem non_separating_not_metric :
    ∃ (i j : Fin 2), i ≠ j ∧ emergentDist constOneKernel i j = 0 :=
  ⟨0, 1, by decide, constOneKernel_dist_zero 0 1⟩

end
