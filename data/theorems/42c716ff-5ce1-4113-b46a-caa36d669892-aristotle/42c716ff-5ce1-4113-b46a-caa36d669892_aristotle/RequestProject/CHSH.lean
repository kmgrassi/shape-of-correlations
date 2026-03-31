import Mathlib

noncomputable section

open Real

/-!
# CHSH vs Geometric Consistency Curve

We study the trade-off between Bell-CHSH nonlocality and geometric consistency
(μ-submultiplicativity) for PSD normalized Gram matrices on the Bell sector.

## Setup

Given parameters `a b x : ℝ` with `a, b, x ∈ [0,1]`, define the 4×4 symmetric
Bell-CHSH Gram matrix:

    G(a,b,x) = [[1, a, x, x],
                 [a, 1, x, -x],
                 [x, x, 1, b],
                 [x, -x, b, 1]]

where:
- Diagonal entries are 1 (normalized)
- `a = |G(A₀, A₁)|` is Alice's internal overlap
- `b = |G(B₀, B₁)|` is Bob's internal overlap
- The CHSH value equals `4x` under the symmetric ansatz

The constraint `a ≥ μ·x²` and `b ≥ μ·x²` represents μ-submultiplicativity
(geometric consistency at strength μ).

## Main Results

- `chsh_upper_bound`: Under PSD and μ-submultiplicativity, CHSH ≤ 4/√(2+μ)
- `tsirelson_matrix_psd`: The Tsirelson matrix G(0,0,1/√2) is PSD
- `tsirelson_value`: The Tsirelson bound 2√2 is achieved at μ = 0
- `chsh_strict_bound`: CHSH < 2√2 for all μ > 0
- `chsh_bound_tightens`: The bound 4/√(2+μ) is monotone decreasing in μ
-/

-- ============================================================
-- Section 1: Definitions
-- ============================================================

/-- The quadratic form v^T G(a,b,x) v of the Bell-CHSH Gram matrix. -/
def bellQuadForm (a b x : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2
  + 2 * a * (v 0 * v 1)
  + 2 * x * (v 0 * v 2)
  + 2 * x * (v 0 * v 3)
  + 2 * x * (v 1 * v 2)
  - 2 * x * (v 1 * v 3)
  + 2 * b * (v 2 * v 3)

/-- The Bell-CHSH Gram matrix G(a,b,x) is positive semidefinite:
    for all vectors v, the quadratic form v^T G v is non-negative. -/
def BellPSD (a b x : ℝ) : Prop :=
  ∀ v : Fin 4 → ℝ, 0 ≤ bellQuadForm a b x v

-- ============================================================
-- Section 2: PSD implies necessary algebraic conditions
-- ============================================================

/-- Evaluating the Bell quadratic form at the test vector (-1, 1, 0, 2x)
    yields 2(1 - a - 2x²). This is the key vector for deriving Alice's bound. -/
lemma bellQuadForm_alice_test (a b x : ℝ) :
    bellQuadForm a b x ![(-1), 1, 0, 2 * x] = 2 * (1 - a - 2 * x ^ 2) := by
  unfold bellQuadForm; norm_num; ring;
  erw [Matrix.cons_val_succ']; norm_num; ring;
  erw [Matrix.cons_val_succ']; norm_num; ring

/-- **PSD necessary condition (Alice)**: If G(a,b,x) is PSD, then a + 2x² ≤ 1.
    Proof: evaluate the PSD condition at v = (-1, 1, 0, 2x). -/
theorem psd_implies_alice_bound {a b x : ℝ} (h : BellPSD a b x) :
    a + 2 * x ^ 2 ≤ 1 := by
  have := h ![(-1), 1, 0, 2 * x]
  rw [bellQuadForm_alice_test] at this
  linarith

/-- Evaluating the Bell quadratic form at the test vector (0, 2x, -1, 1)
    yields 2(1 - b - 2x²). This is the key vector for deriving Bob's bound. -/
lemma bellQuadForm_bob_test (a b x : ℝ) :
    bellQuadForm a b x ![0, 2 * x, (-1), 1] = 2 * (1 - b - 2 * x ^ 2) := by
  unfold bellQuadForm; norm_num; ring;
  repeat erw [Matrix.cons_val_succ']; norm_num; ring;

/-- **PSD necessary condition (Bob)**: If G(a,b,x) is PSD, then b + 2x² ≤ 1.
    Proof: evaluate the PSD condition at v = (0, 2x, -1, 1). -/
theorem psd_implies_bob_bound {a b x : ℝ} (h : BellPSD a b x) :
    b + 2 * x ^ 2 ≤ 1 := by
  linarith [h ![0, 2 * x, -1, 1], bellQuadForm_bob_test a b x]

-- ============================================================
-- Section 3: The CHSH upper bound
-- ============================================================

/-- **Key algebraic bound**: if μx² ≤ a and a + 2x² ≤ 1, then (2+μ)x² ≤ 1. -/
theorem submult_psd_implies_x_sq_bound {a x μ : ℝ}
    (h_sub : μ * x ^ 2 ≤ a) (h_psd : a + 2 * x ^ 2 ≤ 1) :
    (2 + μ) * x ^ 2 ≤ 1 := by
  linarith

/-- **CHSH upper bound**: Under PSD and μ-submultiplicativity with μ ≥ 0,
    we have x ≤ 1/√(2+μ), equivalently CHSH = 4x ≤ 4/√(2+μ). -/
theorem chsh_upper_bound {a b x μ : ℝ} (hμ : 0 ≤ μ) (hx : 0 ≤ x)
    (h_psd : BellPSD a b x) (h_sub_a : μ * x ^ 2 ≤ a) :
    4 * x ≤ 4 / sqrt (2 + μ) := by
  have h_sqrt : x ≤ 1 / Real.sqrt (2 + μ) := by
    apply le_trans (Real.le_sqrt_of_sq_le
      (show x ^ 2 ≤ (1 : ℝ) / (2 + μ) from by
        rw [le_div_iff₀ <| by positivity]
        nlinarith [psd_implies_alice_bound h_psd]))
      (by norm_num)
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h_sqrt zero_le_four

/-- **Strict CHSH bound**: For μ > 0, the CHSH value is strictly below Tsirelson's
    bound 2√2. Interpretation: any positive geometric consistency reduces the
    maximum possible Bell violation. -/
theorem chsh_strict_bound {a b x μ : ℝ} (hμ : 0 < μ) (hx : 0 ≤ x)
    (h_psd : BellPSD a b x) (h_sub_a : μ * x ^ 2 ≤ a) :
    4 * x < 2 * sqrt 2 := by
  have h_bound : 4 * x ≤ 4 / Real.sqrt (2 + μ) :=
    chsh_upper_bound hμ.le hx h_psd h_sub_a
  exact lt_of_le_of_lt h_bound (by
    rw [div_lt_iff₀] <;>
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (2 + μ),
      Real.sq_sqrt zero_le_two, Real.sq_sqrt (show 0 ≤ 2 + μ by positivity),
      mul_pos (Real.sqrt_pos.2 zero_lt_two)
        (Real.sqrt_pos.2 (show 0 < 2 + μ by positivity))])

-- ============================================================
-- Section 4: Tsirelson's bound is achievable (μ = 0)
-- ============================================================

/-- The Bell quadratic form at the Tsirelson point G(0, 0, 1/√2) decomposes as
    a sum of two squares:
      v^T G v = (v₀ + v₂/√2 + v₃/√2)² + (v₁ + v₂/√2 - v₃/√2)²
    This immediately implies positive semidefiniteness.

    The factorization corresponds to writing G = V^T V where
      V = [[1, 0, 1/√2, 1/√2],
           [0, 1, 1/√2, -1/√2]]
    is the 2×4 matrix whose columns are unit vectors in ℝ² at angles
    0°, 90°, 45°, -45° (Alice's and Bob's measurement directions). -/
theorem tsirelson_quad_form_eq (v : Fin 4 → ℝ) :
    bellQuadForm 0 0 (1 / sqrt 2) v =
    (v 0 + v 2 / sqrt 2 + v 3 / sqrt 2) ^ 2 +
    (v 1 + v 2 / sqrt 2 - v 3 / sqrt 2) ^ 2 := by
  unfold bellQuadForm; ring; norm_num; ring;

/-- **Tsirelson matrix is PSD**: The Bell-CHSH Gram matrix G(0, 0, 1/√2) is
    positive semidefinite. This is the matrix achieving the Tsirelson bound. -/
theorem tsirelson_matrix_psd : BellPSD 0 0 (1 / sqrt 2) := fun v => by
  have := tsirelson_quad_form_eq v
  nlinarith [sq_nonneg (v 0 + v 2 / Real.sqrt 2 + v 3 / Real.sqrt 2),
             sq_nonneg (v 1 + v 2 / Real.sqrt 2 - v 3 / Real.sqrt 2)]

/-- The CHSH value at the Tsirelson point equals 2√2. -/
theorem tsirelson_value : 4 * (1 / sqrt 2) = 2 * sqrt 2 := by
  rw [mul_one_div, div_eq_iff] <;> ring_nf <;> norm_num

-- ============================================================
-- Section 5: Monotonicity of the bound
-- ============================================================

/-- **Monotonicity**: The CHSH upper bound 4/√(2+μ) is decreasing in μ.
    Stronger geometric consistency (larger μ) implies a tighter bound
    on Bell nonlocality. -/
theorem chsh_bound_tightens {μ₁ μ₂ : ℝ} (h₁ : 0 ≤ μ₁) (h₂ : μ₁ ≤ μ₂) :
    (4 : ℝ) / sqrt (2 + μ₂) ≤ 4 / sqrt (2 + μ₁) := by
  gcongr

/-- **Feasibility monotonicity**: A feasible point for stronger geometric
    consistency μ₂ is also feasible for weaker consistency μ₁ ≤ μ₂. -/
theorem feasible_mono {a b x μ₁ μ₂ : ℝ} (hle : μ₁ ≤ μ₂) (hx : 0 ≤ x)
    (h_sub_a : μ₂ * x ^ 2 ≤ a) (h_sub_b : μ₂ * x ^ 2 ≤ b) :
    μ₁ * x ^ 2 ≤ a ∧ μ₁ * x ^ 2 ≤ b := by
  constructor <;> nlinarith [sq_nonneg x]

-- ============================================================
-- Section 6: Summary theorem
-- ============================================================

/-- **Main theorem (CHSH vs Geometric Consistency)**:

    (1) At μ = 0 (no geometric constraint), the Tsirelson bound 2√2 is achieved.
    (2) For any μ > 0, the maximum CHSH value is strictly less than 2√2.
    (3) An explicit upper bound: CHSH ≤ 4/√(2+μ) for all μ ≥ 0.
    (4) The bound tightens monotonically with μ.

    **Physical interpretation**: If experiments observe CHSH ≈ 2√2 (near Tsirelson),
    then the geometric consistency parameter μ must be near 0 for the Bell sector.
    This means Bell sectors of reality are very weakly geometric, even if
    macroscopic space exhibits strong geometric consistency. -/
theorem chsh_geometric_consistency :
    -- (1) Tsirelson's bound is achieved at μ = 0
    (BellPSD 0 0 (1 / sqrt 2) ∧ 4 * (1 / sqrt 2) = 2 * sqrt 2) ∧
    -- (2) For all μ > 0, CHSH < 2√2
    (∀ μ : ℝ, 0 < μ → ∀ a b x : ℝ, 0 ≤ x → BellPSD a b x →
      μ * x ^ 2 ≤ a → 4 * x < 2 * sqrt 2) ∧
    -- (3) Explicit upper bound CHSH ≤ 4/√(2+μ)
    (∀ μ : ℝ, 0 ≤ μ → ∀ a b x : ℝ, 0 ≤ x → BellPSD a b x →
      μ * x ^ 2 ≤ a → 4 * x ≤ 4 / sqrt (2 + μ)) ∧
    -- (4) Monotonicity
    (∀ μ₁ μ₂ : ℝ, 0 ≤ μ₁ → μ₁ ≤ μ₂ →
      (4 : ℝ) / sqrt (2 + μ₂) ≤ 4 / sqrt (2 + μ₁)) := by
  exact ⟨⟨tsirelson_matrix_psd, tsirelson_value⟩,
         fun μ hμ a b x hx hpsd hsub => chsh_strict_bound hμ hx hpsd hsub,
         fun μ hμ a b x hx hpsd hsub => chsh_upper_bound hμ hx hpsd hsub,
         fun μ₁ μ₂ h₁ h₂ => chsh_bound_tightens h₁ h₂⟩

end
