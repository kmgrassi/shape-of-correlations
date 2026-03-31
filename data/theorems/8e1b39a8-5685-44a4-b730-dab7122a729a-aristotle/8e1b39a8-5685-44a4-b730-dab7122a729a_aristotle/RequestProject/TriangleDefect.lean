import RequestProject.Defs

/-!
# Triangle Defect Interpretation of μ (Priority 2)

The single most important conceptual theorem: μ is really a triangle-defect parameter.

## Main results:
- **Theorem B** (`approxSubmult_iff_triangleSlack`):
  For G with all positive absolute values and μ > 0, setting D(i,j) = -log|G(i,j)|:
  ApproxSubmult μ G ⟺ TriangleSlack (-log μ) D.
  Thus δ = -log μ is an additive geometric defect / triangle slack.

- **Theorem 5** (`delta_antitone_mu`): μ ↑ ⟺ δ ↓
- `delta_zero_iff_mu_one`: exact geometry (μ = 1) corresponds to δ = 0
- `exact_triangle_of_mu_one`: μ = 1 gives the exact triangle inequality for D
-/

noncomputable section

open Real

variable {α : Type*}

/-! ## The exponential-decay setting -/

/-- A kernel has all-positive absolute values. -/
def AllPositive (G : α → α → ℝ) : Prop :=
  ∀ i j, |G i j| > 0

/-- The effective distance D(i,j) = -log|G(i,j)| for a positive kernel. -/
def effectiveDist (G : α → α → ℝ) (i j : α) : ℝ :=
  -Real.log (|G i j|)

/-! ## Theorem B: ApproxSubmult ↔ Triangle Slack -/

/-- **Theorem B (key conceptual theorem)**: For a kernel with all-positive absolute
    values and μ > 0, ApproxSubmult μ G is equivalent to the triangle inequality
    with additive slack δ = -log μ for the effective distance D = -log|G|.

    This identifies μ as a triangle-defect parameter: δ = -log μ measures how far
    the effective geometry deviates from satisfying the triangle inequality. -/
theorem approxSubmult_iff_triangleSlack {G : α → α → ℝ} {μ : ℝ}
    (hG : AllPositive G) (hμ : μ > 0) :
    ApproxSubmult μ G ↔ TriangleSlack (-Real.log μ) (effectiveDist G) := by
  unfold ApproxSubmult TriangleSlack effectiveDist
  constructor <;> intro h i j k <;> contrapose! h
  · use i, j, k
    rw [← Real.log_lt_log_iff (hG _ _) (mul_pos (mul_pos hμ (hG _ _)) (hG _ _))]
    rw [Real.log_mul (mul_ne_zero hμ.ne' (ne_of_gt (hG i j))) (ne_of_gt (hG j k)),
        Real.log_mul hμ.ne' (ne_of_gt (hG i j))]
    linarith
  · have h_log : Real.log (|G i k|) < Real.log μ + Real.log (|G i j|) + Real.log (|G j k|) := by
      rw [← Real.log_mul, ← Real.log_mul] <;> try nlinarith [hG i j, hG j k]
      exact Real.log_lt_log (hG i k) h
    exact ⟨i, j, k, by linarith⟩

/-! ## Theorem 5: Monotonicity of δ = -log μ -/

/-- δ = -log μ is antitone in μ: larger μ means smaller δ (better geometry). -/
theorem delta_antitone_mu {μ₁ μ₂ : ℝ} (h1 : 0 < μ₁) (_h2 : 0 < μ₂)
    (hle : μ₁ ≤ μ₂) : -Real.log μ₂ ≤ -Real.log μ₁ :=
  neg_le_neg (Real.log_le_log h1 hle)

/-- Exact geometry (μ = 1) corresponds to δ = 0 (exact triangle inequality). -/
theorem delta_zero_iff_mu_one {μ : ℝ} (hμ : 0 < μ) (_hμ1 : μ ≤ 1) :
    -Real.log μ = 0 ↔ μ = 1 := by
  rw [neg_eq_zero, Real.log_eq_zero]
  grind

/-- When μ = 1, ApproxSubmult gives the exact triangle inequality for D
    (i.e., TriangleSlack 0). -/
theorem exact_triangle_of_mu_one {G : α → α → ℝ} (hG : AllPositive G) :
    ApproxSubmult 1 G ↔ TriangleSlack 0 (effectiveDist G) := by
  convert approxSubmult_iff_triangleSlack hG (show 0 < (1 : ℝ) by norm_num) using 1
  norm_num

end
