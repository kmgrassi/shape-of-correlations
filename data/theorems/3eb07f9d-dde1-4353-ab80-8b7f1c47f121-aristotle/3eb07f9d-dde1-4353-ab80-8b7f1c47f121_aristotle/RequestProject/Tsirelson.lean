/-
# Tsirelson Bound (Theorem 1)

For any unit vectors v_{A₀}, v_{A₁}, v_{B₀}, v_{B₁} in a real inner product space,
the CHSH functional satisfies:
  |⟨v_{A₀}, v_{B₀}⟩ + ⟨v_{A₀}, v_{B₁}⟩ + ⟨v_{A₁}, v_{B₀}⟩ - ⟨v_{A₁}, v_{B₁}⟩| ≤ 2√2

This is the quantum Tsirelson bound. Combined with the rank-1 bound of 2,
this establishes the hierarchy: classical ≤ 2 < quantum ≤ 2√2.

Proof sketch:
1. CHSH = ⟨v_{A₀}, v_{B₀}+v_{B₁}⟩ + ⟨v_{A₁}, v_{B₀}-v_{B₁}⟩
2. By Cauchy-Schwarz: |CHSH| ≤ ‖v_{B₀}+v_{B₁}‖ + ‖v_{B₀}-v_{B₁}‖
3. By Cauchy-Schwarz on ℝ²: (a+b)² ≤ 2(a²+b²)
4. ‖v_{B₀}+v_{B₁}‖² + ‖v_{B₀}-v_{B₁}‖² = 2‖v_{B₀}‖² + 2‖v_{B₁}‖² = 4
5. Therefore |CHSH| ≤ √(2·4) = 2√2
-/
import Mathlib
import RequestProject.Defs

open InnerProductSpace Real

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-
PROBLEM
Key helper: the sum of norms bound using the parallelogram identity.
    For any vectors u, w: (‖u + w‖ + ‖u - w‖)² ≤ 2(‖u + w‖² + ‖u - w‖²) = 4(‖u‖² + ‖w‖²)

PROVIDED SOLUTION
By the Cauchy-Schwarz inequality on ℝ² with the vector (1,1) and (‖u+w‖, ‖u-w‖): (a+b)² ≤ 2(a²+b²). So (‖u+w‖+‖u-w‖)² ≤ 2(‖u+w‖²+‖u-w‖²). By the parallelogram law, ‖u+w‖²+‖u-w‖² = 2‖u‖²+2‖w‖². Use norm_add_sq_real and norm_sub_sq_real, and the fact that (a+b)² ≤ 2(a²+b²) follows from 0 ≤ (a-b)².
-/
theorem sum_norms_sq_le (u w : V) :
    (‖u + w‖ + ‖u - w‖) ^ 2 ≤ 2 * (2 * ‖u‖ ^ 2 + 2 * ‖w‖ ^ 2) := by
  linarith [ sq_nonneg ( ‖u + w‖ - ‖u - w‖ ), norm_add_sq_real u w, norm_sub_sq_real u w ]

/-
PROBLEM
Tsirelson bound: for unit vectors in a real inner product space,
    CHSH ≤ 2√2.

PROVIDED SOLUTION
1. Use chsh_decomposition to write CHSH = ⟪vA₀, vB₀+vB₁⟫ + ⟪vA₁, vB₀-vB₁⟫.
2. By triangle inequality and real_inner_le_norm (or Cauchy-Schwarz): each term ≤ ‖vAᵢ‖ · ‖...‖.
3. Since ‖vA₀‖ = ‖vA₁‖ = 1: CHSH ≤ ‖vB₀+vB₁‖ + ‖vB₀-vB₁‖.
4. By sum_norms_sq_le: (‖vB₀+vB₁‖ + ‖vB₀-vB₁‖)² ≤ 2·(2‖vB₀‖²+2‖vB₁‖²) = 2·4 = 8.
5. Therefore CHSH ≤ √8 = 2√2.
-/
theorem tsirelson_bound_le (vA₀ vA₁ vB₀ vB₁ : V)
    (hA₀ : ‖vA₀‖ = 1) (hA₁ : ‖vA₁‖ = 1)
    (hB₀ : ‖vB₀‖ = 1) (hB₁ : ‖vB₁‖ = 1) :
    ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ + ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ ≤ 2 * sqrt 2 := by
  -- By the properties of the inner product and the Cauchy-Schwarz inequality, we have:
  have h_inner : ⟪vA₀, vB₀ + vB₁⟫_ℝ + ⟪vA₁, vB₀ - vB₁⟫_ℝ ≤ ‖vB₀ + vB₁‖ + ‖vB₀ - vB₁‖ := by
    exact add_le_add ( by simpa [ hA₀ ] using abs_le.mp ( abs_real_inner_le_norm vA₀ ( vB₀ + vB₁ ) ) |>.2 ) ( by simpa [ hA₁ ] using abs_le.mp ( abs_real_inner_le_norm vA₁ ( vB₀ - vB₁ ) ) |>.2 );
  have h_norm : ‖vB₀ + vB₁‖^2 + ‖vB₀ - vB₁‖^2 = 4 := by
    rw [ @norm_add_sq ℝ, @norm_sub_sq ℝ ] ; norm_num [ hB₀, hB₁ ] ; ring;
  have h_norm_le : ‖vB₀ + vB₁‖ + ‖vB₀ - vB₁‖ ≤ 2 * Real.sqrt 2 := by
    nlinarith only [ sq_nonneg ( ‖vB₀ + vB₁‖ - ‖vB₀ - vB₁‖ ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, h_norm ];
  convert h_inner.trans h_norm_le using 1 ; simp +decide [ inner_add_right, inner_sub_right ] ; ring

/-
PROBLEM
Tsirelson bound: for unit vectors in a real inner product space,
    -2√2 ≤ CHSH.

PROVIDED SOLUTION
Apply tsirelson_bound_le to (-vA₀) (-vA₁) vB₀ vB₁. This changes the signs of all inner products involving Alice's vectors. We have ‖-vA₀‖ = ‖vA₀‖ = 1, ‖-vA₁‖ = ‖vA₁‖ = 1. The bound gives ⟪-vA₀, vB₀⟫ + ⟪-vA₀, vB₁⟫ + ⟪-vA₁, vB₀⟫ - ⟪-vA₁, vB₁⟫ ≤ 2√2. Since ⟪-v, w⟫ = -⟪v, w⟫, this becomes -(⟪vA₀, vB₀⟫ + ⟪vA₀, vB₁⟫ + ⟪vA₁, vB₀⟫ - ⟪vA₁, vB₁⟫) ≤ 2√2, which gives ⟪vA₀, vB₀⟫ + ⟪vA₀, vB₁⟫ + ⟪vA₁, vB₀⟫ - ⟪vA₁, vB₁⟫ ≥ -2√2.
-/
theorem tsirelson_bound_ge (vA₀ vA₁ vB₀ vB₁ : V)
    (hA₀ : ‖vA₀‖ = 1) (hA₁ : ‖vA₁‖ = 1)
    (hB₀ : ‖vB₀‖ = 1) (hB₁ : ‖vB₁‖ = 1) :
    -(2 * sqrt 2) ≤ ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ + ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ := by
  by_contra h_contra;
  convert tsirelson_bound_le ( -vA₀ ) ( -vA₁ ) vB₀ vB₁ _ _ _ _ using 1 <;> simp +decide [ * ];
  linarith

/-- Tsirelson bound (absolute value form): |CHSH| ≤ 2√2 -/
theorem tsirelson_bound (vA₀ vA₁ vB₀ vB₁ : V)
    (hA₀ : ‖vA₀‖ = 1) (hA₁ : ‖vA₁‖ = 1)
    (hB₀ : ‖vB₀‖ = 1) (hB₁ : ‖vB₁‖ = 1) :
    |⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ + ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ| ≤ 2 * sqrt 2 := by
  rw [abs_le]
  exact ⟨tsirelson_bound_ge vA₀ vA₁ vB₀ vB₁ hA₀ hA₁ hB₀ hB₁,
         tsirelson_bound_le vA₀ vA₁ vB₀ vB₁ hA₀ hA₁ hB₀ hB₁⟩

/-
PROBLEM
CHSH expressed as sum of two inner products (key decomposition)

PROVIDED SOLUTION
Expand inner_add_right and inner_sub_right to decompose the inner products with sums. ⟪vA₀, vB₀ + vB₁⟫ = ⟪vA₀, vB₀⟫ + ⟪vA₀, vB₁⟫ and ⟪vA₁, vB₀ - vB₁⟫ = ⟪vA₁, vB₀⟫ - ⟪vA₁, vB₁⟫.
-/
theorem chsh_decomposition (vA₀ vA₁ vB₀ vB₁ : V) :
    ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ + ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ =
    ⟪vA₀, vB₀ + vB₁⟫_ℝ + ⟪vA₁, vB₀ - vB₁⟫_ℝ := by
  simp +decide [ inner_add_right, inner_sub_right ] ; ring

end