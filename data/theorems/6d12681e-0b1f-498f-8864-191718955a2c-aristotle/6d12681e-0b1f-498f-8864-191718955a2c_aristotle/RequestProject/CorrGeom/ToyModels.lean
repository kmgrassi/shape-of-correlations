/-
# Toy Models: 1D Chain and 2D Grid

Theorems E2-E3: Explicit correlation kernels that recover line and grid geometry.
Also contains embedding theorems C1-C2 and the non-geometric kernel E4.
-/
import RequestProject.CorrGeom.Defs

noncomputable section

open Real

/-! ## Theorem C1 / E2: 1D Chain Model

I(i,j) = exp(-α|i-j|) on a finite type, proving d(i,j) = α|i-j|.
This recovers exact 1D line geometry. -/

/-- The 1D chain correlation kernel: I(i,j) = exp(-α * |i - j|)
    for α > 0 on a finite chain. -/
def chainKernel (N : ℕ) (α : ℝ) (hα : 0 < α) : CorrKernel (Fin N) where
  I := fun i j => Real.exp (-α * |(i : ℤ) - (j : ℤ)|)
  symm := fun i j => by rw [abs_sub_comm]
  pos := fun i j => Real.exp_pos _
  norm := by intro i; simp
  bound := by
    intro i j
    apply Real.exp_le_one_iff.mpr
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity

/-- The emergent distance of the chain kernel is α|i-j|. -/
theorem chainKernel_dist (N : ℕ) (α : ℝ) (hα : 0 < α) (i j : Fin N) :
    emergentDist (chainKernel N α hα) i j = α * |(i : ℤ) - (j : ℤ)| := by
  unfold emergentDist chainKernel; aesop

/-- The chain kernel satisfies the multiplicative triangle inequality. -/
theorem chainKernel_mult_triangle (N : ℕ) (α : ℝ) (hα : 0 < α) (i j k : Fin N) :
    (chainKernel N α hα).I i k ≥ (chainKernel N α hα).I i j * (chainKernel N α hα).I j k := by
  unfold chainKernel
  simp +zetaDelta at *
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by
    cases abs_cases ((i : ℝ) - j) <;> cases abs_cases ((j : ℝ) - k) <;>
      cases abs_cases ((i : ℝ) - k) <;> nlinarith)

/-! ## Theorem D1 applied to chain: Nearest-neighbor dominance -/

/-- In the chain model, the exponential coupling H(i,j) = exp(-d(i,j)) = I(i,j),
    so interaction strength strictly decreases with distance |i-j|.
    That is, if |i-j₁| < |i-j₂|, then H(i,j₁) > H(i,j₂). -/
theorem chain_coupling_decreases_with_dist (N : ℕ) (α : ℝ) (hα : 0 < α)
    (i j₁ j₂ : Fin N) (h : |(i : ℤ) - j₁| < |(i : ℤ) - j₂|) :
    expCoupling (chainKernel N α hα) i j₂ < expCoupling (chainKernel N α hα) i j₁ := by
  unfold expCoupling; rw [chainKernel_dist N α hα, chainKernel_dist N α hα]; gcongr

/-! ## Theorem C2 / E3: 2D Grid Model

I((a,b),(c,d)) = exp(-α(|a-c| + |b-d|)) on Fin N × Fin M,
proving d = α * Manhattan distance. -/

/-- The 2D grid correlation kernel: I((a,b),(c,d)) = exp(-α(|a-c| + |b-d|)). -/
def gridKernel (N M : ℕ) (α : ℝ) (hα : 0 < α) : CorrKernel (Fin N × Fin M) where
  I := fun p q => Real.exp (-α * (|(p.1 : ℤ) - (q.1 : ℤ)| + |(p.2 : ℤ) - (q.2 : ℤ)|))
  symm := fun i j => by rw [abs_sub_comm, abs_sub_comm (j.2 : ℤ)]
  pos := fun p q => Real.exp_pos _
  norm := by intro p; simp
  bound := by
    intro p q
    apply Real.exp_le_one_iff.mpr
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity

/-- Manhattan distance on a grid. -/
def manhattanDist (p q : Fin N × Fin M) : ℝ :=
  |(p.1 : ℤ) - (q.1 : ℤ)| + |(p.2 : ℤ) - (q.2 : ℤ)|

/-- The emergent distance of the grid kernel is α * Manhattan distance. -/
theorem gridKernel_dist (N M : ℕ) (α : ℝ) (hα : 0 < α) (p q : Fin N × Fin M) :
    emergentDist (gridKernel N M α hα) p q = α * manhattanDist p q := by
  unfold emergentDist gridKernel manhattanDist; aesop

/-- The grid kernel satisfies the multiplicative triangle inequality. -/
theorem gridKernel_mult_triangle (N M : ℕ) (α : ℝ) (hα : 0 < α)
    (p q r : Fin N × Fin M) :
    (gridKernel N M α hα).I p r ≥
      (gridKernel N M α hα).I p q * (gridKernel N M α hα).I q r := by
  norm_num [gridKernel]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by
    nlinarith [abs_sub_le (p.1 : ℝ) (q.1 : ℝ) (r.1 : ℝ),
               abs_sub_le (p.2 : ℝ) (q.2 : ℝ) (r.2 : ℝ)])

/-! ## Theorem C1: Exact line embedding -/

/-- If I(i,j) = exp(-|x_i - x_j|) for some coordinates x : S → ℝ,
    then d(i,j) = |x_i - x_j|. -/
theorem line_embedding_recovers_dist {S : Type*} (x : S → ℝ)
    (K : CorrKernel S) (hK : ∀ i j, K.I i j = Real.exp (-|x i - x j|)) (i j : S) :
    emergentDist K i j = |x i - x j| := by
  unfold emergentDist; rw [hK]; simp +decide [Real.log_exp]

/-! ## Theorem C2: Exact Euclidean embedding -/

/-- If I(i,j) = exp(-‖x_i - x_j‖) for coordinates x : S → EuclideanSpace ℝ (Fin n),
    then d(i,j) = ‖x_i - x_j‖. -/
theorem euclidean_embedding_recovers_dist {S : Type*} {n : ℕ}
    (x : S → EuclideanSpace ℝ (Fin n))
    (K : CorrKernel S) (hK : ∀ i j, K.I i j = Real.exp (-‖x i - x j‖)) (i j : S) :
    emergentDist K i j = ‖x i - x j‖ := by
  unfold emergentDist; aesop

end
