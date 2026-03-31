/-
# Submultiplicativity Obstruction (Theorems 2-3, Lemmas A-C)

Main result: Bell-sector submultiplicativity is incompatible with
maximal CHSH violation (|CHSH| = 2√2).

Key insight: at CHSH = 2√2, equality conditions force
⟪vA₀,vA₁⟫ = 0 and |⟪vA₀,vB₀⟫| = 1/√2 > 0.
Submultiplicativity would require 0 = |⟪vA₀,vA₁⟩| ≥ |⟪vA₀,vB₀⟩|·|⟪vB₀,vA₁⟩| = 1/2 > 0.
Contradiction.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.Tsirelson

open Real InnerProductSpace

noncomputable section

/-! ## Lemma B: Zero overlap obstructs submultiplicativity -/

/-
PROBLEM
If a value is zero but the product of two absolute values is positive,
    the submultiplicativity constraint |a₀a₁| ≥ |a₀b| · |ba₁| is violated.

PROVIDED SOLUTION
h_zero gives |a₀a₁| = 0. The product |a₀b| * |ba₁| > 0 since both factors are positive. So 0 ≥ positive is false.
-/
theorem zero_overlap_obstructs_submult
    (a₀a₁ a₀b ba₁ : ℝ)
    (h_zero : a₀a₁ = 0)
    (h_pos1 : 0 < |a₀b|)
    (h_pos2 : 0 < |ba₁|) :
    ¬(|a₀a₁| ≥ |a₀b| * |ba₁|) := by
  aesop

/-! ## Tsirelson equality characterization -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-
PROBLEM
At CHSH = 2√2, Bob's measurements must be orthogonal: ⟪vB₀, vB₁⟫ = 0.

    Proof: From the Cauchy-Schwarz chain, CHSH ≤ ‖vB₀+vB₁‖ + ‖vB₀-vB₁‖.
    Then (a+b)² ≤ 2(a²+b²), with equality iff a=b.
    a² + b² = ‖vB₀+vB₁‖² + ‖vB₀-vB₁‖² = 2‖vB₀‖² + 2‖vB₁‖² = 4.
    Equality in the AM-QM step requires ‖vB₀+vB₁‖ = ‖vB₀-vB₁‖,
    which means ⟪vB₀,vB₁⟫ = 0.

PROVIDED SOLUTION
From the Tsirelson bound proof chain:
1. CHSH = ⟪vA₀, vB₀+vB₁⟫ + ⟪vA₁, vB₀-vB₁⟫ (by chsh_decomposition)
2. Each term ≤ ‖vAᵢ‖·‖...‖ = ‖...‖ by Cauchy-Schwarz (real_inner_le_norm) and unit vector norm
3. So CHSH ≤ ‖vB₀+vB₁‖ + ‖vB₀-vB₁‖
4. By (a+b)² ≤ 2(a²+b²), ‖vB₀+vB₁‖ + ‖vB₀-vB₁‖ ≤ √(2(‖vB₀+vB₁‖²+‖vB₀-vB₁‖²))
5. ‖vB₀+vB₁‖² + ‖vB₀-vB₁‖² = 2‖vB₀‖²+2‖vB₁‖² = 4 (parallelogram law)
6. So CHSH ≤ √8 = 2√2

At equality CHSH = 2√2:
- Equality in step 4: ‖vB₀+vB₁‖ = ‖vB₀-vB₁‖
- ‖vB₀+vB₁‖² = 2+2⟪vB₀,vB₁⟫ and ‖vB₀-vB₁‖² = 2-2⟪vB₀,vB₁⟫
- Equal iff ⟪vB₀,vB₁⟫ = 0

So trace back from 2√2 = ‖vB₀+vB₁‖+‖vB₀-vB₁‖ with (a+b)²≤2(a²+b²) equality condition (a=b), combined with a²+b² = 4.

Concretely: 8 = (2√2)² ≤ (‖vB₀+vB₁‖+‖vB₀-vB₁‖)² ≤ 2(‖vB₀+vB₁‖²+‖vB₀-vB₁‖²) = 8.
So all inequalities are equalities. The second inequality is equality iff ‖vB₀+vB₁‖=‖vB₀-vB₁‖ (from (a-b)²=0). Since ‖vB₀+vB₁‖²-‖vB₀-vB₁‖² = 4⟪vB₀,vB₁⟫, this forces ⟪vB₀,vB₁⟫ = 0.

But we also need: 2√2 ≤ ‖vB₀+vB₁‖+‖vB₀-vB₁‖ from the Cauchy-Schwarz steps.
From step 2: CHSH ≤ ⟪vA₀, vB₀+vB₁⟫ + ⟪vA₁, vB₀-vB₁⟫ ≤ ‖vB₀+vB₁‖+‖vB₀-vB₁‖ ≤ 2√2 = CHSH.
So all are equalities, in particular ‖vB₀+vB₁‖+‖vB₀-vB₁‖ = 2√2.
Then (‖vB₀+vB₁‖+‖vB₀-vB₁‖)² = 8 and ‖vB₀+vB₁‖²+‖vB₀-vB₁‖² = 4.
(a+b)² = a²+2ab+b² = 4+2ab = 8, so ab=2, where a=‖vB₀+vB₁‖, b=‖vB₀-vB₁‖.
Also a²+b² = 4 and 2ab=4, so (a-b)² = a²-2ab+b² = 4-4 = 0, so a=b.
a²=2, so ‖vB₀+vB₁‖²=2, but ‖vB₀+vB₁‖² = 2+2⟪vB₀,vB₁⟫, so ⟪vB₀,vB₁⟫=0.
-/
theorem tsirelson_equality_bob_orthogonal (vA₀ vA₁ vB₀ vB₁ : V)
    (hA₀ : ‖vA₀‖ = 1) (hA₁ : ‖vA₁‖ = 1)
    (hB₀ : ‖vB₀‖ = 1) (hB₁ : ‖vB₁‖ = 1)
    (h_max : ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ + ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ = 2 * sqrt 2) :
    ⟪vB₀, vB₁⟫_ℝ = 0 := by
  -- From the equality part of the proof, we know that ‖vB₀ + vB₁‖ = ‖vB₀ - vB₁‖.
  have h_eq_norms : ‖vB₀ + vB₁‖ = ‖vB₀ - vB₁‖ := by
    have h_eq_norms : ‖vB₀ + vB₁‖ + ‖vB₀ - vB₁‖ = 2 * Real.sqrt 2 := by
      refine' le_antisymm _ _;
      · have h_cauchy_schwarz : ∀ (u v : V), ‖u + v‖^2 + ‖u - v‖^2 = 2 * (‖u‖^2 + ‖v‖^2) := by
          intro u v; rw [ @norm_add_sq ℝ, @norm_sub_sq ℝ ] ; ring;
        generalize_proofs at *; simp_all +decide [ ← sq ] ;
        nlinarith [ sq_nonneg ( ‖vB₀ + vB₁‖ - ‖vB₀ - vB₁‖ ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, h_cauchy_schwarz vB₀ vB₁, hB₀ ▸ hB₁ ▸ h_cauchy_schwarz vB₀ vB₁ ] ;
      · have h_cauchy_schwarz : ⟪vA₀, vB₀ + vB₁⟫_ℝ + ⟪vA₁, vB₀ - vB₁⟫_ℝ ≤ ‖vB₀ + vB₁‖ + ‖vB₀ - vB₁‖ := by
          exact add_le_add ( by simpa [ hA₀ ] using abs_le.mp ( abs_real_inner_le_norm vA₀ ( vB₀ + vB₁ ) ) |>.2 ) ( by simpa [ hA₁ ] using abs_le.mp ( abs_real_inner_le_norm vA₁ ( vB₀ - vB₁ ) ) |>.2 );
        simp_all +decide [ inner_add_right, inner_sub_right ];
        linarith;
    have h_eq_norms_sq : ‖vB₀ + vB₁‖^2 + ‖vB₀ - vB₁‖^2 = 4 := by
      rw [ @norm_add_sq ℝ, @norm_sub_sq ℝ ] ; ring ; norm_num [ hB₀, hB₁ ];
    nlinarith only [ h_eq_norms, h_eq_norms_sq, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
  have := norm_add_sq_real vB₀ vB₁; have := norm_sub_sq_real vB₀ vB₁; simp_all +decide ; linarith;

/-
PROBLEM
At CHSH = 2√2, Alice's measurements must be orthogonal: ⟪vA₀, vA₁⟫ = 0.

PROVIDED SOLUTION
From the equality conditions of the Tsirelson bound proof:
At CHSH = 2√2, equality in Cauchy-Schwarz requires ⟪vA₀, vB₀+vB₁⟫ = ‖vB₀+vB₁‖ (i.e., vA₀ is parallel to vB₀+vB₁ with positive coefficient) and ⟪vA₁, vB₀-vB₁⟫ = ‖vB₀-vB₁‖ (vA₁ parallel to vB₀-vB₁).

Since ⟪vB₀,vB₁⟫=0 (from tsirelson_equality_bob_orthogonal), vB₀+vB₁ and vB₀-vB₁ are orthogonal:
⟪vB₀+vB₁, vB₀-vB₁⟫ = ‖vB₀‖²-‖vB₁‖² = 1-1 = 0.

Since vA₀ ∝ vB₀+vB₁ and vA₁ ∝ vB₀-vB₁, and these two directions are orthogonal, we get ⟪vA₀,vA₁⟫ = 0.

More concretely: from the Cauchy-Schwarz equality conditions and h_max:
- ⟪vA₀, vB₀+vB₁⟫ = ‖vB₀+vB₁‖ (since ‖vA₀‖=1)
- ⟪vA₁, vB₀-vB₁⟫ = ‖vB₀-vB₁‖ (since ‖vA₁‖=1)

Then ⟪vA₀,vA₁⟫ can be decomposed using vB₀,vB₁ as a basis (in the relevant subspace). Since vA₀ = (vB₀+vB₁)/√2 and vA₁ = (vB₀-vB₁)/√2 (up to components orthogonal to both), and ⟪vA₀,vA₁⟫ = (1/2)(‖vB₀‖²-‖vB₁‖²) = 0.

Alternative cleaner route:
2√2 = ⟪vA₀, vB₀+vB₁⟫ + ⟪vA₁, vB₀-vB₁⟫ ≤ ‖vB₀+vB₁‖ + ‖vB₀-vB₁‖ ≤ 2√2.
So ⟪vA₀, vB₀+vB₁⟫ = ‖vB₀+vB₁‖ = √2 and ⟪vA₁, vB₀-vB₁⟫ = ‖vB₀-vB₁‖ = √2.

From ⟪vA₀, vB₀+vB₁⟫ = ‖vB₀+vB₁‖ and ‖vA₀‖=1: vA₀ = (vB₀+vB₁)/‖vB₀+vB₁‖ + w where ⟪w, vB₀+vB₁⟫ = 0.
Similarly vA₁ = (vB₀-vB₁)/‖vB₀-vB₁‖ + w' where ⟪w', vB₀-vB₁⟫ = 0.

⟪vA₀,vA₁⟫ = ⟪(vB₀+vB₁)/√2 + w, (vB₀-vB₁)/√2 + w'⟫
= (1/2)⟪vB₀+vB₁, vB₀-vB₁⟫ + ...
= 0 + cross terms.

This is getting complicated. Let me just use nlinarith with the right auxiliary expressions.

Key facts to use:
- bob_orth: ⟪vB₀,vB₁⟫ = 0
- h_max: the sum = 2√2
- real_inner_le_norm applied to each term
- ‖vB₀+vB₁‖² = 2 (from bob_orth and unit norms)
- ‖vB₀-vB₁‖² = 2

Use inner_mul_le_norm_mul_iff to get the exact equality conditions: ⟪x,y⟫ = ‖x‖*‖y‖ iff x = (‖x‖/‖y‖)*y (when y≠0).

Then ⟪vA₀,vA₁⟫ = (1/2)⟪vB₀+vB₁, vB₀-vB₁⟫/‖vB₀+vB₁‖·‖vB₀-vB₁‖ · ‖vA₀‖·‖vA₁‖ ... this isn't quite right.

Actually: The cleanest approach is to use abs_inner_le_norm for ⟪vA₀,vA₁⟫, and bound it using the Cauchy-Schwarz equality conditions.

From h_max = 2√2 and the chain:
⟪vA₀, vB₀+vB₁⟫ + ⟪vA₁, vB₀-vB₁⟫ = 2√2
Both ⟪vA₀, vB₀+vB₁⟫ ≤ √2 and ⟪vA₁, vB₀-vB₁⟫ ≤ √2
So both must equal √2.

Now use inner_eq_norm_mul_iff_of_ne_zero (or similar) to get that vA₀ is a positive scalar multiple of vB₀+vB₁. Since ‖vA₀‖=1 and ‖vB₀+vB₁‖=√2, we get vA₀ = (vB₀+vB₁)/√2.
Similarly vA₁ = (vB₀-vB₁)/√2.

Then ⟪vA₀,vA₁⟫ = ⟪(vB₀+vB₁)/√2, (vB₀-vB₁)/√2⟫ = (1/2)(‖vB₀‖²-‖vB₁‖²) = (1/2)(1-1) = 0.
-/
theorem tsirelson_equality_alice_orthogonal (vA₀ vA₁ vB₀ vB₁ : V)
    (hA₀ : ‖vA₀‖ = 1) (hA₁ : ‖vA₁‖ = 1)
    (hB₀ : ‖vB₀‖ = 1) (hB₁ : ‖vB₁‖ = 1)
    (h_max : ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ + ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ = 2 * sqrt 2) :
    ⟪vA₀, vA₁⟫_ℝ = 0 := by
  -- From the equality conditions of the Cauchy-Schwarz inequality, we know that ⟪vA₀, vB₀ + vB₁⟫ = √2 and ⟪vA₁, vB₀ - vB₁⟫ = √2.
  have h_cauchy_schwarz : ⟪vA₀, vB₀ + vB₁⟫_ℝ = Real.sqrt 2 ∧ ⟪vA₁, vB₀ - vB₁⟫_ℝ = Real.sqrt 2 := by
    have h_equality_conditions : ‖vA₀‖ = 1 ∧ ‖vA₁‖ = 1 ∧ ‖vB₀ + vB₁‖ = Real.sqrt 2 ∧ ‖vB₀ - vB₁‖ = Real.sqrt 2 := by
      have h_cauchy_schwarz : ⟪vB₀, vB₁⟫_ℝ = 0 := by
        exact?;
      simp_all +decide [ norm_add_sq_real, norm_sub_sq_real ];
      constructor <;> rw [ ← sq_eq_sq₀ ] <;> norm_num [ *, norm_add_sq_real, norm_sub_sq_real ];
    have h_cauchy_schwarz : ⟪vA₀, vB₀ + vB₁⟫_ℝ ≤ Real.sqrt 2 ∧ ⟪vA₁, vB₀ - vB₁⟫_ℝ ≤ Real.sqrt 2 := by
      exact ⟨ by simpa [ h_equality_conditions ] using real_inner_le_norm vA₀ ( vB₀ + vB₁ ), by simpa [ h_equality_conditions ] using real_inner_le_norm vA₁ ( vB₀ - vB₁ ) ⟩;
    exact ⟨ by linarith [ show ⟪vA₀, vB₀ + vB₁⟫_ℝ = ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ by rw [ inner_add_right ], show ⟪vA₁, vB₀ - vB₁⟫_ℝ = ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ by rw [ inner_sub_right ] ], by linarith [ show ⟪vA₀, vB₀ + vB₁⟫_ℝ = ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ by rw [ inner_add_right ], show ⟪vA₁, vB₀ - vB₁⟫_ℝ = ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ by rw [ inner_sub_right ] ] ⟩;
  -- Using the Cauchy-Schwarz equality conditions, we get that $vA₀ = \frac{vB₀ + vB₁}{\sqrt{2}}$ and $vA₁ = \frac{vB₀ - vB₁}{\sqrt{2}}$.
  have hvA₀ : vA₀ = (1 / Real.sqrt 2) • (vB₀ + vB₁) := by
    have hvA₀ : ‖vA₀ - (1 / Real.sqrt 2) • (vB₀ + vB₁)‖^2 = 0 := by
      rw [ @norm_sub_sq ℝ ];
      simp_all +decide [ norm_smul, inner_smul_right ];
      simp_all +decide [ ← smul_add, inner_add_right, inner_smul_right ];
      rw [ norm_smul, Real.norm_of_nonneg ( by positivity ), norm_eq_sqrt_real_inner ] ; norm_num [ hB₀, hB₁ ];
      rw [ inv_mul_eq_div, div_pow, Real.sq_sqrt ] <;> norm_num [ norm_add_sq_real, hB₀, hB₁ ];
      have := tsirelson_equality_bob_orthogonal vA₀ vA₁ vB₀ vB₁ hA₀ hA₁ hB₀ hB₁ ( by linarith ) ; linarith;
    exact sub_eq_zero.mp ( norm_eq_zero.mp ( sq_eq_zero_iff.mp hvA₀ ) )
  have hvA₁ : vA₁ = (1 / Real.sqrt 2) • (vB₀ - vB₁) := by
    have hvA₁ : ‖vA₁ - (1 / Real.sqrt 2) • (vB₀ - vB₁)‖^2 = 0 := by
      rw [ @norm_sub_sq ℝ ] ; norm_num [ hA₁, hB₀, hB₁, h_cauchy_schwarz.2, inner_smul_right, inner_sub_right ] ; ring ;
      norm_num [ norm_smul, hB₀, hB₁ ];
      rw [ mul_pow, inv_pow, abs_of_nonneg ( Real.sqrt_nonneg _ ), Real.sq_sqrt ] <;> norm_num [ hB₀, hB₁, norm_sub_sq_real ];
      have := tsirelson_equality_bob_orthogonal vA₀ vA₁ vB₀ vB₁ hA₀ hA₁ hB₀ hB₁ h_max; norm_num at this; linarith;
    exact sub_eq_zero.mp ( norm_eq_zero.mp ( sq_eq_zero_iff.mp hvA₁ ) );
  simp_all +decide [ inner_add_left, inner_add_right, inner_smul_left, inner_smul_right ];
  simp_all +decide [ inner_sub_right, inner_sub_left ];
  rw [ real_inner_comm ] ; ring

/-
PROBLEM
At CHSH = 2√2, all cross-correlators are nonzero (each has |·| = 1/√2).
    In particular |⟪vA₀, vB₀⟫| > 0 and |⟪vB₀, vA₁⟫| > 0.

PROVIDED SOLUTION
From the proof of tsirelson_equality_alice_orthogonal, at CHSH = 2√2 we established:
  vA₀ = (vB₀ + vB₁)/√2  and  vA₁ = (vB₀ - vB₁)/√2.

So:
  ⟪vA₀, vB₀⟫ = ⟪(vB₀+vB₁)/√2, vB₀⟫ = (1/√2)(‖vB₀‖² + ⟪vB₁,vB₀⟫) = (1/√2)(1+0) = 1/√2.
  ⟪vB₀, vA₁⟫ = ⟪vB₀, (vB₀-vB₁)/√2⟫ = (1/√2)(‖vB₀‖² - ⟪vB₀,vB₁⟫) = (1/√2)(1-0) = 1/√2.

Both are positive (1/√2 > 0), so |⟪vA₀,vB₀⟫| = 1/√2 > 0 and |⟪vB₀,vA₁⟫| = 1/√2 > 0.

Alternatively, more directly: from h_max = 2√2 > 0, the four correlators can't all be zero. And by the Cauchy-Schwarz equality conditions, ⟪vA₀,vB₀+vB₁⟫ = √2 > 0, which means ⟪vA₀,vB₀⟫ + ⟪vA₀,vB₁⟫ = √2 ≠ 0. Since both are equal (by symmetry of the construction), each is 1/√2.

Actually simplest: just compute. We know ⟪vB₀,vB₁⟫ = 0 and the chain of equalities from the Tsirelson bound proof gives ⟪vA₀, vB₀+vB₁⟫ = √2. So ⟪vA₀,vB₀⟫ + ⟪vA₀,vB₁⟫ = √2.

Similarly ⟪vA₁, vB₀-vB₁⟫ = √2, so ⟪vA₁,vB₀⟫ - ⟪vA₁,vB₁⟫ = √2.

And ⟪vA₀,vB₀⟫ + ⟪vA₀,vB₁⟫ + ⟪vA₁,vB₀⟫ - ⟪vA₁,vB₁⟫ = 2√2 (given).

Since each of the first part equals √2 and the second equals √2, and each individual correlator is bounded by 1 in absolute value, we can deduce that ⟪vA₀,vB₀⟫ and ⟪vA₁,vB₀⟫ are both nonzero.

Actually, the simplest approach: from h_max and using the fact that each |inner product| ≤ 1 (by unit vectors):
|⟪vA₀,vB₀⟫| + |⟪vA₀,vB₁⟫| + |⟪vA₁,vB₀⟫| + |⟪vA₁,vB₁⟫| ≥ |⟪vA₀,vB₀⟫ + ⟪vA₀,vB₁⟫ + ⟪vA₁,vB₀⟫ - ⟪vA₁,vB₁⟫| = 2√2 > 2.

If |⟪vA₀,vB₀⟫| = 0, then the sum ≤ 0 + 1 + 1 + 1 = 3. But we also know (from tighter bounds) that ⟪vA₀,vB₀+vB₁⟫ = √2, which since ⟪vA₀,vB₁⟫ ≤ 1, gives ⟪vA₀,vB₀⟫ ≥ √2-1 > 0.

So |⟪vA₀,vB₀⟫| ≥ √2-1 > 0. Similarly for |⟪vB₀,vA₁⟫|.

Use nlinarith with real_inner_le_norm, the equality conditions, and √2 > 1.
-/
theorem tsirelson_equality_cross_nonzero (vA₀ vA₁ vB₀ vB₁ : V)
    (hA₀ : ‖vA₀‖ = 1) (hA₁ : ‖vA₁‖ = 1)
    (hB₀ : ‖vB₀‖ = 1) (hB₁ : ‖vB₁‖ = 1)
    (h_max : ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ + ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ = 2 * sqrt 2) :
    0 < |⟪vA₀, vB₀⟫_ℝ| ∧ 0 < |⟪vB₀, vA₁⟫_ℝ| := by
  -- By the equality conditions of the Tsirelson bound, we have ⟪vA₀, vB₀ + vB₁⟫ = √2 and ⟪vA₁, vB₀ - vB₁⟫ = √2.
  have h_eq : ⟪vA₀, vB₀ + vB₁⟫_ℝ = Real.sqrt 2 ∧ ⟪vA₁, vB₀ - vB₁⟫_ℝ = Real.sqrt 2 := by
    have h_eq : ‖vB₀ + vB₁‖ = Real.sqrt 2 ∧ ‖vB₀ - vB₁‖ = Real.sqrt 2 := by
      have h_bob_orthogonal : ⟪vB₀, vB₁⟫_ℝ = 0 := by
        exact?;
      constructor <;> rw [ ← sq_eq_sq₀ ] <;> norm_num [ *, norm_add_sq_real, norm_sub_sq_real ];
    have h_cauchy_schwarz : ∀ (u v : V), ‖u‖ = 1 → ‖v‖ = Real.sqrt 2 → ⟪u, v⟫_ℝ ≤ Real.sqrt 2 := by
      exact fun u v hu hv => le_trans ( abs_le.mp ( abs_real_inner_le_norm u v ) |>.2 ) ( by norm_num [ hu, hv ] );
    constructor <;> linarith [ h_cauchy_schwarz vA₀ ( vB₀ + vB₁ ) hA₀ h_eq.1, h_cauchy_schwarz vA₁ ( vB₀ - vB₁ ) hA₁ h_eq.2, show ⟪vA₀, vB₀ + vB₁⟫_ℝ = ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ by rw [ inner_add_right ], show ⟪vA₁, vB₀ - vB₁⟫_ℝ = ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ by rw [ inner_sub_right ] ];
  simp_all +decide [ inner_add_right, inner_sub_right ];
  -- By the properties of the inner product, we know that ⟪vA₀, vB₀⟫_ℝ ≤ ‖vA₀‖ * ‖vB₀‖ = 1 and ⟪vA₀, vB₁⟫_ℝ ≤ ‖vA₀‖ * ‖vB₁‖ = 1.
  have h_inner_bounds : |⟪vA₀, vB₀⟫_ℝ| ≤ 1 ∧ |⟪vA₀, vB₁⟫_ℝ| ≤ 1 ∧ |⟪vA₁, vB₀⟫_ℝ| ≤ 1 ∧ |⟪vA₁, vB₁⟫_ℝ| ≤ 1 := by
    exact ⟨ by simpa [ hA₀, hB₀ ] using abs_real_inner_le_norm vA₀ vB₀, by simpa [ hA₀, hB₁ ] using abs_real_inner_le_norm vA₀ vB₁, by simpa [ hA₁, hB₀ ] using abs_real_inner_le_norm vA₁ vB₀, by simpa [ hA₁, hB₁ ] using abs_real_inner_le_norm vA₁ vB₁ ⟩;
  constructor <;> intro h <;> simp_all +decide [ abs_le ];
  rw [ real_inner_comm ] at h ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

/-! ## Main Obstruction Theorems -/

/-- **Theorem 2/3 (Main Obstruction):**
    Maximal CHSH violation (CHSH = 2√2) is incompatible with submultiplicativity
    of the Gram matrix on the Bell quadruple.

    Specifically: if CHSH = 2√2 and the single submultiplicativity constraint
    |⟪vA₀,vA₁⟫| ≥ |⟪vA₀,vB₀⟫|·|⟪vB₀,vA₁⟫| holds, we get a contradiction. -/
theorem maximal_chsh_violates_submult (vA₀ vA₁ vB₀ vB₁ : V)
    (hA₀ : ‖vA₀‖ = 1) (hA₁ : ‖vA₁‖ = 1)
    (hB₀ : ‖vB₀‖ = 1) (hB₁ : ‖vB₁‖ = 1)
    (h_max : ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ + ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ = 2 * sqrt 2)
    (h_submult : |⟪vA₀, vA₁⟫_ℝ| ≥ |⟪vA₀, vB₀⟫_ℝ| * |⟪vB₀, vA₁⟫_ℝ|) :
    False := by
  have h_orth := tsirelson_equality_alice_orthogonal vA₀ vA₁ vB₀ vB₁ hA₀ hA₁ hB₀ hB₁ h_max
  have h_cross := tsirelson_equality_cross_nonzero vA₀ vA₁ vB₀ vB₁ hA₀ hA₁ hB₀ hB₁ h_max
  have h_obstruct := zero_overlap_obstructs_submult ⟪vA₀, vA₁⟫_ℝ ⟪vA₀, vB₀⟫_ℝ ⟪vB₀, vA₁⟫_ℝ
    h_orth h_cross.1 h_cross.2
  exact h_obstruct h_submult

/-- **Corollary:** Under Bell-sector submultiplicativity and PSD+normalized,
    |CHSH| ≠ 2√2. Combined with the Tsirelson bound, this gives |CHSH| < 2√2. -/
theorem chsh_lt_tsirelson_under_submult (vA₀ vA₁ vB₀ vB₁ : V)
    (hA₀ : ‖vA₀‖ = 1) (hA₁ : ‖vA₁‖ = 1)
    (hB₀ : ‖vB₀‖ = 1) (hB₁ : ‖vB₁‖ = 1)
    (h_submult : |⟪vA₀, vA₁⟫_ℝ| ≥ |⟪vA₀, vB₀⟫_ℝ| * |⟪vB₀, vA₁⟫_ℝ|) :
    ⟪vA₀, vB₀⟫_ℝ + ⟪vA₀, vB₁⟫_ℝ + ⟪vA₁, vB₀⟫_ℝ - ⟪vA₁, vB₁⟫_ℝ ≠ 2 * sqrt 2 := by
  intro h_max
  exact maximal_chsh_violates_submult vA₀ vA₁ vB₀ vB₁ hA₀ hA₁ hB₀ hB₁ h_max h_submult

/-! ## Lemma C: Bell-sector submultiplicativity forces positive internal overlaps -/

/-
PROBLEM
Under submultiplicativity, if cross-correlations are nonzero,
    then internal overlaps must be positive.

PROVIDED SOLUTION
From h_submult: |G_A₀A₁| ≥ |G_A₀B| * |G_BA₁|. Since G_A₀B ≠ 0 and G_BA₁ ≠ 0, both |G_A₀B| > 0 and |G_BA₁| > 0, so the product is positive. Hence |G_A₀A₁| > 0.
-/
theorem submult_forces_positive_overlap
    (G_A₀A₁ G_A₀B G_BA₁ : ℝ)
    (h_submult : |G_A₀A₁| ≥ |G_A₀B| * |G_BA₁|)
    (h1 : G_A₀B ≠ 0) (h2 : G_BA₁ ≠ 0) :
    |G_A₀A₁| > 0 := by
  exact lt_of_lt_of_le ( mul_pos ( abs_pos.mpr h1 ) ( abs_pos.mpr h2 ) ) h_submult

end