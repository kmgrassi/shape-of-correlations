import RequestProject.Defs

/-!
# Part II: Geometry from Common Origin

We prove that the symmetric kernel I_R induces an emergent metric d_R = D,
that d_R is a pseudometric, and that coupling strength decreases with emergent distance.
-/

open Real

noncomputable section

variable {S : Type*} (R : RelationalOrigin S)

/-! ## Theorem 1: Common-origin metric emergence -/

/-
PROBLEM
The emergent distance recovers the original cost function: d_R(i,j) = D(i,j)

PROVIDED SOLUTION
Unfold d_R and I_R. d_R(i,j) = -log(exp(-D(i,j))) = -(-D(i,j)) = D(i,j). Use Real.log_exp.
-/
theorem metric_emergence (i j : S) : R.d_R i j = R.D i j := by
  -- By definition of `d_R`, we have `d_R i j = -log (R.I_R i j)`.
  simp [RelationalOrigin.d_R, RelationalOrigin.I_R]

/-
PROBLEM
d_R is nonneg

PROVIDED SOLUTION
By metric_emergence, d_R(i,j) = D(i,j) ≥ 0.
-/
theorem d_R_nonneg (i j : S) : 0 ≤ R.d_R i j := by
  -- Since $D$ is nonnegative, log(exp(-$D$)) is also nonnegative.
  simp [RelationalOrigin.d_R, RelationalOrigin.I_R, R.D_nonneg]

/-
PROBLEM
d_R(i,i) = 0

PROVIDED SOLUTION
By metric_emergence, d_R(i,i) = D(i,i) = 0.
-/
theorem d_R_self (i : S) : R.d_R i i = 0 := by
  -- By definition of $d_R$, we have $d_R(i,i) = -\log(I_R(i,i))$.
  simp [RelationalOrigin.d_R, RelationalOrigin.I_R];
  exact R.D_self i

/-
PROBLEM
d_R is symmetric

PROVIDED SOLUTION
By metric_emergence, d_R(i,j) = D(i,j) = D(j,i) = d_R(j,i).
-/
theorem d_R_symm (i j : S) : R.d_R i j = R.d_R j i := by
  -- By definition of $d_R$, we have $d_R(i, j) = - \log(\exp(-D(i, j)))$.
  simp [RelationalOrigin.d_R];
  rw [ RelationalOrigin.I_R, RelationalOrigin.I_R, R.D_symm ]

/-
PROBLEM
d_R satisfies the triangle inequality

PROVIDED SOLUTION
By metric_emergence, reduce to D's triangle inequality.
-/
theorem d_R_triangle (i j k : S) : R.d_R i k ≤ R.d_R i j + R.d_R j k := by
  rw [ metric_emergence, metric_emergence, metric_emergence ];
  exact R.D_triangle i j k

/-
PROBLEM
d_R is a pseudometric (summary: nonneg, self-zero, symmetric, triangle)

PROVIDED SOLUTION
Combine d_R_nonneg, d_R_self, d_R_symm, d_R_triangle.
-/
theorem d_R_pseudometric :
    (∀ i j, 0 ≤ R.d_R i j) ∧
    (∀ i, R.d_R i i = 0) ∧
    (∀ i j, R.d_R i j = R.d_R j i) ∧
    (∀ i j k, R.d_R i k ≤ R.d_R i j + R.d_R j k) := by
      exact ⟨ d_R_nonneg R, d_R_self R, d_R_symm R, d_R_triangle R ⟩

/-
PROBLEM
If D has the separation property, d_R is a metric

PROVIDED SOLUTION
By metric_emergence, d_R(i,j) = 0 implies D(i,j) = 0 implies i = j by hsep.
-/
theorem d_R_metric (hsep : ∀ i j, R.D i j = 0 → i = j) :
    (∀ i j, R.d_R i j = 0 → i = j) := by
      -- Apply the metric_emergence theorem to both sides of the equation d_R(i, j) = 0.
      intros i j h_eq
      have h_D_eq : R.D i j = 0 := by
        unfold RelationalOrigin.d_R at h_eq;
        unfold RelationalOrigin.I_R at h_eq; aesop;
      apply hsep i j h_D_eq

/-! ## Theorem 2: Coupling locality from same origin -/

/-
PROBLEM
The coupling kernel equals the correlation kernel: H_R = I_R

PROVIDED SOLUTION
H_R(i,j) = exp(-d_R(i,j)) = exp(-D(i,j)) = I_R(i,j). Use metric_emergence to rewrite d_R as D.
-/
theorem coupling_eq_correlation (i j : S) : R.H_R i j = R.I_R i j := by
  unfold RelationalOrigin.H_R RelationalOrigin.I_R;
  unfold RelationalOrigin.d_R RelationalOrigin.I_R; simp +decide [ Real.exp_neg ] ;

/-
PROBLEM
I_R values are in (0, 1]

PROVIDED SOLUTION
I_R(i,j) = exp(-D(i,j)) > 0 since exp is always positive. Use Real.exp_pos.
-/
theorem I_R_pos (i j : S) : 0 < R.I_R i j := by
  exact Real.exp_pos _

/-
PROVIDED SOLUTION
I_R(i,j) = exp(-D(i,j)) ≤ exp(0) = 1 since -D(i,j) ≤ 0 (D nonneg) and exp is monotone. Use exp_le_exp or exp_le_one_of_nonpos.
-/
theorem I_R_le_one (i j : S) : R.I_R i j ≤ 1 := by
  exact Real.exp_le_one_iff.mpr ( neg_nonpos.mpr ( R.D_nonneg i j ) )

/-
PROBLEM
Coupling strength decreases with emergent distance:
    if d_R(i,j) ≤ d_R(i,k) then H_R(i,j) ≥ H_R(i,k)

PROVIDED SOLUTION
H_R = exp(-d_R). Since d_R(i,j) ≤ d_R(i,k), we have -d_R(i,k) ≤ -d_R(i,j), so exp(-d_R(i,k)) ≤ exp(-d_R(i,j)) by monotonicity of exp.
-/
theorem coupling_decreases_with_distance (i j k : S)
    (h : R.d_R i j ≤ R.d_R i k) : R.H_R i k ≤ R.H_R i j := by
      exact Real.exp_le_exp.2 ( neg_le_neg h )

/-
PROBLEM
Coupling strength is maximal for zero distance

PROVIDED SOLUTION
H_R(i,i) = exp(-d_R(i,i)) = exp(-0) = exp(0) = 1. Use d_R_self and exp_zero.
-/
theorem coupling_maximal_at_zero (i : S) : R.H_R i i = 1 := by
  unfold RelationalOrigin.H_R; norm_num [ d_R_self ] ;

end