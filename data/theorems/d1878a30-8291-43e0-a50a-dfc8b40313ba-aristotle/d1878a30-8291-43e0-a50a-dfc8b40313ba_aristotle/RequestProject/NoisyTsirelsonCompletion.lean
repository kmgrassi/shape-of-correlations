import Mathlib

open Matrix Real BigOperators

set_option maxHeartbeats 800000

/-! # Noisy Tsirelson Bell-sector Gram completion

We work over ℝ with the index convention:
  0 = A₀, 1 = A₁, 2 = B₀, 3 = B₁.

We define the noisy-Tsirelson Gram matrix and prove several lemmas
about its determinant, positive semidefiniteness, and μ-submultiplicativity.
-/

noncomputable section

/-- The noisy-Tsirelson Bell-sector Gram matrix. -/
def noisyTsirelsonGram (x y z : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, z, x, x;
     z, 1, x, -x;
     x, x, 1, y;
     x, -x, y, 1]

/-
Helper: determinant of a 4×4 matrix expanded in terms of entries.
-/
lemma det_fin_four (A : Matrix (Fin 4) (Fin 4) ℝ) :
    A.det =
      A 0 0 * A 1 1 * A 2 2 * A 3 3 - A 0 0 * A 1 1 * A 2 3 * A 3 2
    - A 0 0 * A 1 2 * A 2 1 * A 3 3 + A 0 0 * A 1 2 * A 2 3 * A 3 1
    + A 0 0 * A 1 3 * A 2 1 * A 3 2 - A 0 0 * A 1 3 * A 2 2 * A 3 1
    - A 0 1 * A 1 0 * A 2 2 * A 3 3 + A 0 1 * A 1 0 * A 2 3 * A 3 2
    + A 0 1 * A 1 2 * A 2 0 * A 3 3 - A 0 1 * A 1 2 * A 2 3 * A 3 0
    - A 0 1 * A 1 3 * A 2 0 * A 3 2 + A 0 1 * A 1 3 * A 2 2 * A 3 0
    + A 0 2 * A 1 0 * A 2 1 * A 3 3 - A 0 2 * A 1 0 * A 2 3 * A 3 1
    - A 0 2 * A 1 1 * A 2 0 * A 3 3 + A 0 2 * A 1 1 * A 2 3 * A 3 0
    + A 0 2 * A 1 3 * A 2 0 * A 3 1 - A 0 2 * A 1 3 * A 2 1 * A 3 0
    - A 0 3 * A 1 0 * A 2 1 * A 3 2 + A 0 3 * A 1 0 * A 2 2 * A 3 1
    + A 0 3 * A 1 1 * A 2 0 * A 3 2 - A 0 3 * A 1 1 * A 2 2 * A 3 0
    - A 0 3 * A 1 2 * A 2 0 * A 3 1 + A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  simp +decide [ Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.succAbove ] ; ring!;

/-
Lemma 1: determinant identity for the noisy-Tsirelson Gram matrix.
-/
theorem noisyTsirelsonGram_det (x y z : ℝ) :
    (noisyTsirelsonGram x y z).det =
      (1 - y ^ 2) * (1 - z ^ 2) - 4 * x ^ 2 * (1 - x ^ 2) := by
  unfold noisyTsirelsonGram; norm_num [ Matrix.det_succ_row_zero ] ; ring;
  simp +decide [ Fin.sum_univ_succ, Fin.succAbove ] ; ring

/-
Lemma 2: PSD determinant upper bound.
-/
theorem psd_det_upper_bound (x y z : ℝ)
    (hG : (noisyTsirelsonGram x y z).PosSemidef) :
    (1 - y ^ 2) * (1 - z ^ 2) ≥ 4 * x ^ 2 * (1 - x ^ 2) := by
  exact le_of_sub_nonneg ( by have := hG.det_nonneg; rw [ noisyTsirelsonGram_det ] at this; linarith )

/-
Lemma 3: min-overlap upper bound.
-/
theorem min_overlap_upper_bound (x y z : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / √2)
    (hG : (noisyTsirelsonGram x y z).PosSemidef) :
    min (|y|) (|z|) ≤ √(1 - x ^ 2) - x := by
  -- Applying the result from `psd_det_upper_bound`, we get $(1 - y^2)(1 - z^2) \geq 4x^2(1 - x^2)$.
  have h_det_bound : (1 - y^2) * (1 - z^2) ≥ 4 * x^2 * (1 - x^2) := by
    convert psd_det_upper_bound x y z hG using 1;
  -- Since $|y| \leq 1$ and $|z| \leq 1$, we have $1 - y^2 \geq 0$ and $1 - z^2 \geq 0$.
  have h_nonneg : 1 - y^2 ≥ 0 ∧ 1 - z^2 ≥ 0 := by
    constructor <;> have := hG.2 <;> norm_num [ noisyTsirelsonGram ] at this;
    · specialize this ( Finsupp.single 2 1 - Finsupp.single 3 y ) ; norm_num [ Finsupp.sum_fintype ] at this;
      simp +decide [ Fin.sum_univ_succ, Finsupp.single_apply ] at this ; nlinarith;
    · specialize this ( Finsupp.single 0 1 - Finsupp.single 1 z ) ; norm_num [ Finsupp.sum_fintype ] at this;
      simp +decide [ Fin.sum_univ_succ, Finsupp.single_apply ] at this ; nlinarith;
  -- Let $m = \min(|y|, |z|)$. We need to show that $m \leq \sqrt{1 - x^2} - x$.
  set m := min |y| |z| with hm_def
  have hm_le : m^2 ≤ 1 - 2 * x * Real.sqrt (1 - x^2) := by
    have hm_le : (1 - m^2)^2 ≥ 4 * x^2 * (1 - x^2) := by
      have hm_le : (1 - m^2) ≥ (1 - y^2) ∧ (1 - m^2) ≥ (1 - z^2) := by
        simp +zetaDelta at *;
        constructor <;> cases min_cases |y| |z| <;> cases abs_cases y <;> cases abs_cases z <;> push_cast [ * ] at * <;> nlinarith;
      nlinarith;
    contrapose! hm_le;
    convert pow_lt_pow_left₀ ( sub_lt_sub_left hm_le 1 ) _ two_ne_zero using 1 <;> ring;
    · rw [ Real.sq_sqrt ] <;> nlinarith [ show x ^ 2 ≤ 1 / 2 by exact le_trans ( pow_le_pow_left₀ hx0 hx1 2 ) ( by norm_num ) ];
    · exact sub_nonneg_of_le ( pow_le_one₀ ( by positivity ) ( min_le_of_left_le ( show |y| ≤ 1 by exact abs_le.mpr ⟨ by nlinarith, by nlinarith ⟩ ) ) );
  nlinarith only [ show 0 ≤ Real.sqrt ( 1 - x ^ 2 ) - x by exact sub_nonneg_of_le <| Real.le_sqrt_of_sq_le <| by nlinarith [ show x ^ 2 ≤ 1 / 2 by exact le_trans ( pow_le_pow_left₀ hx0 hx1 2 ) <| by norm_num ], hm_le, Real.mul_self_sqrt ( show 0 ≤ 1 - x ^ 2 by exact sub_nonneg.mpr <| by exact le_trans ( pow_le_pow_left₀ hx0 hx1 2 ) <| by norm_num ) ]

/-
Lemma 4: achievability — the Gram matrix with y = z = t is PSD.
-/
theorem noisyTsirelsonGram_achievable_psd (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / √2) :
    (noisyTsirelsonGram x (√(1 - x ^ 2) - x) (√(1 - x ^ 2) - x)).PosSemidef := by
  constructor <;> norm_num [ noisyTsirelsonGram ];
  · ext i j; fin_cases i <;> fin_cases j <;> rfl;
  · intro v;
    norm_num [ Finsupp.sum_fintype, Fin.sum_univ_succ ];
    -- Let's simplify the expression by grouping like terms.
    suffices h_simp : ∀ (a b c d : ℝ), 0 ≤ a^2 + b^2 + c^2 + d^2 + 2 * (Real.sqrt (1 - x^2) - x) * (a * b + c * d) + 2 * x * (a * c + a * d + b * c - b * d) by
      linarith! [ h_simp ( v 0 ) ( v 1 ) ( v 2 ) ( v ( Fin.succ 2 ) ) ];
    intro a b c d
    set s := Real.sqrt (1 - x^2)
    set t := s - x
    have hs : s^2 = 1 - x^2 := by
      exact Real.sq_sqrt <| sub_nonneg.2 <| pow_le_one₀ hx0 <| hx1.trans <| by rw [ div_le_iff₀ ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;
    have ht : t = s - x := by
      rfl
    have ht_nonneg : 0 ≤ t := by
      exact sub_nonneg_of_le <| Real.le_sqrt_of_sq_le <| by nlinarith [ show x ^ 2 ≤ 1 / 2 by exact le_trans ( pow_le_pow_left₀ hx0 hx1 2 ) <| by norm_num ] ;
    have ht_le_one : t ≤ 1 := by
      nlinarith [ Real.sqrt_nonneg ( 1 - x ^ 2 ) ];
    -- We'll use the fact that $t = s - x$ and $s^2 = 1 - x^2$ to simplify the expression.
    have h_simp : 0 ≤ (a + t * b + x * c + x * d)^2 + (b + t * a + x * c - x * d)^2 + (c + t * d + x * a + x * b)^2 + (d + t * c + x * a - x * b)^2 := by
      positivity;
    nlinarith [ mul_nonneg hx0 ht_nonneg, mul_nonneg hx0 ( sq_nonneg ( a + b + c + d ) ), mul_nonneg hx0 ( sq_nonneg ( a + b - c - d ) ), mul_nonneg hx0 ( sq_nonneg ( a - b + c - d ) ), mul_nonneg hx0 ( sq_nonneg ( a - b - c + d ) ) ]

/-- μ-submultiplicativity for a matrix: for all triples (i, j, k),
    |M i j| ≥ μ * |M i k| * |M k j|. -/
def muSubmult (M : Matrix (Fin 4) (Fin 4) ℝ) (mu : ℝ) : Prop :=
  ∀ i j k : Fin 4, |M i j| ≥ mu * |M i k| * |M k j|

/-
Lemma 5: relevant μ-constraints.
    If G is μ-submultiplicative with x ≥ 0, then μ*x² ≤ |y| and μ*x² ≤ |z|.
-/
theorem mu_constraints (x y z mu : ℝ) (hx : 0 ≤ x)
    (hmu : muSubmult (noisyTsirelsonGram x y z) mu) :
    mu * x ^ 2 ≤ |y| ∧ mu * x ^ 2 ≤ |z| := by
  unfold noisyTsirelsonGram at hmu; ( unfold muSubmult at hmu; );
  simp_all +decide [ Fin.forall_fin_succ, abs_of_nonneg ];
  constructor <;> nlinarith

/-
Lemma 6: upper bound on μ.
-/
theorem mu_upper_bound (x y z mu : ℝ)
    (hx0 : 0 < x) (hx1 : x ≤ 1 / √2)
    (hG : (noisyTsirelsonGram x y z).PosSemidef)
    (hmu : muSubmult (noisyTsirelsonGram x y z) mu)
    (_hmu0 : 0 ≤ mu) :
    mu ≤ (√(1 - x ^ 2) - x) / x ^ 2 := by
  have h1 : mu * x ^ 2 ≤ Real.sqrt (1 - x ^ 2) - x := by
    have := min_overlap_upper_bound x y z hx0.le hx1 hG;
    exact le_trans ( by have := mu_constraints x y z mu hx0.le hmu; aesop ) this;
  rwa [ le_div_iff₀ ( sq_pos_of_pos hx0 ) ]

/-
Lemma 7: achievability of μ.
-/
theorem mu_achievable (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1 / √2) :
    let t := √(1 - x ^ 2) - x
    let mu := min 1 (t / x ^ 2)
    (noisyTsirelsonGram x t t).PosSemidef ∧
    muSubmult (noisyTsirelsonGram x t t) mu := by
  refine' ⟨ noisyTsirelsonGram_achievable_psd x hx0.le hx1, _ ⟩;
  intro i j k;
  -- By definition of $t$, we know that $t = \sqrt{1 - x^2} - x$.
  set t := Real.sqrt (1 - x ^ 2) - x;
  -- We'll use that $t = \sqrt{1 - x^2} - x$ and $mu = \min(1, t / x^2)$ to simplify the goal.
  have ht : 0 ≤ t ∧ t ≤ 1 := by
    simp +zetaDelta at *;
    exact ⟨ Real.le_sqrt_of_sq_le ( by nlinarith [ inv_mul_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, inv_pow ( Real.sqrt 2 ) 2 ] ), Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ inv_mul_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, inv_pow ( Real.sqrt 2 ) 2 ] ⟩ ⟩
  have hmu : 0 ≤ min 1 (t / x ^ 2) ∧ min 1 (t / x ^ 2) ≤ 1 := by
    exact ⟨ le_min zero_le_one ( div_nonneg ht.1 ( sq_nonneg x ) ), min_le_left _ _ ⟩
  have hmu_le : min 1 (t / x ^ 2) * x ^ 2 ≤ t := by
    cases min_cases ( 1 : ℝ ) ( t / x ^ 2 ) <;> nlinarith [ mul_div_cancel₀ t ( ne_of_gt ( sq_pos_of_pos hx0 ) ) ]
  have hmu_le_x : min 1 (t / x ^ 2) * x ≤ 1 := by
    nlinarith
  have hmu_le_t : min 1 (t / x ^ 2) * t ≤ 1 := by
    nlinarith;
  -- By definition of $noisyTsirelsonGram$, we know that its entries are either $1$, $t$, or $x$.
  have h_entries : ∀ i j, abs (noisyTsirelsonGram x t t i j) = if i = j then 1 else if i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 ∨ i = 2 ∧ j = 3 ∨ i = 3 ∧ j = 2 then t else x := by
    simp +decide [ Fin.forall_fin_succ, noisyTsirelsonGram ];
    lia;
  simp +decide only [h_entries];
  split_ifs <;> try linarith;
  any_goals nlinarith [ mul_nonneg hmu.1 hx0.le ];
  grind; all_goals grind

end